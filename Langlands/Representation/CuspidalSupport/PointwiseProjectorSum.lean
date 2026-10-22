import Langlands.Representation.CuspidalSupport.NaturalProjectorDecomposition
import Mathlib.Algebra.BigOperators.Finprod

/-! Internal finite-support algebra for the eventual quasicuspidal projector. -/

noncomputable section

namespace Langlands

universe uR uG uV uW uI uJ

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module R V]
  {W : Type uW} [AddCommGroup W] [Module R W]
  {ι : Type uI} {κ : Type uJ}
  {ρ : Representation R G V} {σ : Representation R G W}

/-- Sum a family of actual equivariant endomorphisms that is finite on each vector. -/
def pointwiseFiniteSum
    (e : ι → ρ.IntertwiningMap ρ)
    (hfinite : ∀ v : V, Function.HasFiniteSupport (fun i => e i v)) :
    ρ.IntertwiningMap ρ where
  toLinearMap :=
    { toFun := fun v => ∑ᶠ i, e i v
      map_add' := by
        intro v w
        simp only [map_add]
        exact finsum_add_distrib (hfinite v) (hfinite w)
      map_smul' := by
        intro r v
        simp only [map_smul, RingHom.id_apply]
        exact (smul_finsum' r (hfinite v)).symm }
  isIntertwining' g := by
    ext v
    change (∑ᶠ i, e i (ρ g v)) = ρ g (∑ᶠ i, e i v)
    rw [map_finsum _ (hfinite v)]
    exact finsum_congr fun i => Representation.IntertwiningMap.isIntertwining ρ ρ (e i) g v

@[simp] theorem pointwiseFiniteSum_apply
    (e : ι → ρ.IntertwiningMap ρ)
    (hfinite : ∀ v : V, Function.HasFiniteSupport (fun i => e i v)) (v : V) :
    pointwiseFiniteSum e hfinite v = ∑ᶠ i, e i v := rfl

/-- A finite stratum containing every nonzero summand supplies pointwise finiteness. -/
theorem finiteSupport_of_finite_stratum
    (e : ι → ρ.IntertwiningMap ρ) (v : V) (s : Set ι) (hs : s.Finite)
    (hzero : ∀ i, i ∉ s → e i v = 0) :
    Function.HasFiniteSupport (fun i => e i v) := by
  apply hs.subset
  intro i hi
  by_contra h
  exact hi (hzero i h)

section Projectors

variable (e : ι → ρ.IntertwiningMap ρ)
  (hfinite : ∀ v : V, Function.HasFiniteSupport (fun i => e i v))
  (hid : ∀ i v, e i (e i v) = e i v)
  (horth : ∀ i j, i ≠ j → ∀ v, e i (e j v) = 0)

include hid horth

/-- Each component absorbs the total projector on the left. -/
theorem component_pointwiseFiniteSum (i : ι) (v : V) :
    e i (pointwiseFiniteSum e hfinite v) = e i v := by
  rw [pointwiseFiniteSum_apply, map_finsum _ (hfinite v)]
  calc
    (∑ᶠ j, e i (e j v)) = e i (e i v) :=
      finsum_eq_single _ i (fun j hji => horth i j hji.symm v)
    _ = e i v := hid i v

/-- The total projector fixes every component image. -/
theorem pointwiseFiniteSum_component (i : ι) (v : V) :
    pointwiseFiniteSum e hfinite (e i v) = e i v := by
  rw [pointwiseFiniteSum_apply]
  calc
    (∑ᶠ j, e j (e i v)) = e i (e i v) :=
      finsum_eq_single _ i (fun j hji => horth j i hji v)
    _ = e i v := hid i v

/-- A pointwise-finite sum of pairwise orthogonal idempotents is idempotent. -/
theorem pointwiseFiniteSum_idempotent (v : V) :
    pointwiseFiniteSum e hfinite (pointwiseFiniteSum e hfinite v) =
      pointwiseFiniteSum e hfinite v := by
  change (∑ᶠ i, e i (pointwiseFiniteSum e hfinite v)) = ∑ᶠ i, e i v
  exact finsum_congr fun i => component_pointwiseFiniteSum e hfinite hid horth i v

end Projectors

/-- A linear map intertwining the components also intertwines their pointwise sums.
The index equivalence allows the components to be permuted, as in outer conjugation. -/
theorem pointwiseFiniteSum_covariant
    (e : ι → ρ.IntertwiningMap ρ)
    (hfinite : ∀ v : V, Function.HasFiniteSupport (fun i => e i v))
    (q : κ → σ.IntertwiningMap σ)
    (hqfinite : ∀ w : W, Function.HasFiniteSupport (fun j => q j w))
    (f : V →ₗ[R] W) (t : ι ≃ κ)
    (h : ∀ i v, q (t i) (f v) = f (e i v)) (v : V) :
    pointwiseFiniteSum q hqfinite (f v) = f (pointwiseFiniteSum e hfinite v) := by
  simp only [pointwiseFiniteSum_apply]
  rw [map_finsum _ (hfinite v)]
  exact (finsum_eq_of_bijective t t.bijective (fun i => (h i v).symm)).symm

namespace SmoothRep

open CategoryTheory

variable [TopologicalSpace G]

/-- The pointwise sum of natural orthogonal projectors supplies the algebraic
split once its range has property P and it fixes every P-object. -/
theorem decomposition_of_pointwiseFiniteSum
    (P : SmoothRep.{uR, uG, uV} R G → Prop)
    (e : ι → ∀ A : SmoothRep.{uR, uG, uV} R G,
      A.representation.IntertwiningMap A.representation)
    (hfinite : ∀ (A : SmoothRep.{uR, uG, uV} R G) (v : A),
      Function.HasFiniteSupport (fun i => e i A v))
    (hnat : ∀ i (A B : SmoothRep.{uR, uG, uV} R G) (f : A ⟶ B) (v : A),
      e i B (hom f v) = hom f (e i A v))
    (hid : ∀ i (A : SmoothRep.{uR, uG, uV} R G) (v : A), e i A (e i A v) = e i A v)
    (horth : ∀ i j, i ≠ j → ∀ (A : SmoothRep.{uR, uG, uV} R G) (v : A),
      e i A (e j A v) = 0)
    (himage : ∀ A : SmoothRep.{uR, uG, uV} R G,
      P (subrepresentation A (pointwiseFiniteSum (fun i => e i A) (hfinite A)).range))
    (hfix : ∀ D : SmoothRep.{uR, uG, uV} R G, P D → ∀ v : D,
      pointwiseFiniteSum (fun i => e i D) (hfinite D) v = v)
    (A : SmoothRep.{uR, uG, uV} R G) :
    ∃ S Q : Subrepresentation A.representation,
      IsCompl S.toSubmodule Q.toSubmodule ∧ P (subrepresentation A S) ∧
      ∀ D : SmoothRep.{uR, uG, uV} R G,
        IsSubquotient D (subrepresentation A Q) → P D → Subsingleton D := by
  apply decomposition_of_natural_idempotent P
    (fun B => pointwiseFiniteSum (fun i => e i B) (hfinite B)) ?_ ?_ himage hfix A
  · intro B C f v
    exact pointwiseFiniteSum_covariant (fun i => e i B) (hfinite B)
      (fun i => e i C) (hfinite C) (hom f).toLinearMap (Equiv.refl ι)
      (fun i w => hnat i B C f w) v
  · intro B v
    exact pointwiseFiniteSum_idempotent (fun i => e i B) (hfinite B)
      (fun i w => hid i B w) (fun i j hij w => horth i j hij B w) v

end SmoothRep
end Langlands
