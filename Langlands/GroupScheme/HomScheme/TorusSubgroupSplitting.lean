import Langlands.GroupScheme.HomScheme.SplitTorusHopfPoint
import Langlands.GroupScheme.Rational.SplitTorus

/-! # Étale-local splitting of closed torus subgroups

Over an affine test scheme `T`, a closed subgroup `L ⊆ G_T` which is a relative torus is split
on finitely many affine étale charts `Spec C_k → T` that jointly cover `T`. On each chart the
subgroup is the range of a split-torus homomorphism, encoded by a Hopf point
`O(G) → C_k ⊗[R] R[ℤ^{I_k}]` whose `C_k`-linear extension is surjective. -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.HomScheme.TorusSplitting

open Langlands.FiniteBialgebraHom FiniteSource SplitTorusPoint

variable {R : Type u} [CommRing R] {T : Over (Spec (CommRingCat.of R))}

/-- The ring `A` of an affine scheme `g : Spec A ⟶ T`, as an `R`-algebra through
`Spec A ⟶ T ⟶ Spec R`. -/
@[nolint unusedArguments]
def ChartRing (A : CommRingCat.{u}) (_g : Spec A ⟶ T.left) : Type u := A

instance (A : CommRingCat.{u}) (g : Spec A ⟶ T.left) : CommRing (ChartRing A g) :=
  inferInstanceAs (CommRing A)

instance (A : CommRingCat.{u}) (g : Spec A ⟶ T.left) : Algebra R (ChartRing A g) :=
  (Spec.preimage (g ≫ T.hom)).hom.toAlgebra

/-- The morphism `g : Spec A ⟶ T` as a morphism of schemes over `Spec R`. -/
def chartHom (A : CommRingCat.{u}) (g : Spec A ⟶ T.left) : specOver R (ChartRing A g) ⟶ T :=
  Over.homMk g (Spec.map_preimage (g ≫ T.hom)).symm

@[simp]
theorem chartHom_left (A : CommRingCat.{u}) (g : Spec A ⟶ T.left) :
    (chartHom A g).left = g :=
  rfl

variable (G : GroupScheme (Spec (CommRingCat.of R))) {L : GroupScheme T.left}
  (i : L ⟶ (GroupScheme.baseChange T.hom).obj G)

/-- On a chart `g : Spec A ⟶ T` splitting `L` by `e`, the inclusion of `L` as a homomorphism
from the split torus. -/
def chartRelHom (A : CommRingCat.{u}) (g : Spec A ⟶ T.left) (I : Type u) [Finite I]
    (e : (GroupScheme.baseChange g).obj L ≅ splitTorus (Spec A) I) :
    RelativeHom (splitTorus (Spec (CommRingCat.of R)) I) G (specOver R (ChartRing A g)) :=
  (splitTorus.baseChangeIso (specOver R (ChartRing A g)).hom I ≪≫ e.symm).hom ≫
    TorusSubgroupModuli.familyHom i (chartHom A g)

theorem isClosedSubgroup_chartRelHom (hi : IsClosedSubgroup i) (A : CommRingCat.{u})
    (g : Spec A ⟶ T.left) (I : Type u) [Finite I]
    (e : (GroupScheme.baseChange g).obj L ≅ splitTorus (Spec A) I) :
    IsClosedSubgroup (chartRelHom G i A g I e) :=
  IsClosedSubgroup.iso_comp _ (TorusSubgroupModuli.isClosedSubgroup_familyHom i hi _)

theorem evaluate_chartHom (A : CommRingCat.{u}) (g : Spec A ⟶ T.left) (I : Type u) [Finite I]
    (e : (GroupScheme.baseChange g).obj L ≅ splitTorus (Spec A) I) :
    TorusSubgroupModuli.evaluate i (chartHom A g) =
      SubgroupFunctor.range (chartRelHom G i A g I e) :=
  (SubgroupFunctor.range_iso_comp _ _).symm

end TorusSplitting

open Langlands.FiniteBialgebraHom FiniteSource SplitTorusPoint TorusSplitting

/-- **Étale-local splitting.** Let `T` be an affine scheme over `Spec R` and `i : L ⟶ G_T` a
closed subgroup which is a relative torus. Then there are finitely many affine étale charts
`b k : Spec C_k ⟶ T`, jointly surjective, and Hopf points `f k : O(G) → C_k ⊗[R] R[ℤ^{I_k}]`
with surjective `C_k`-linear extensions, such that the evaluation of `i` on each chart is the
range of the split-torus homomorphism of `f k`. -/
theorem exists_etale_splitPoints {R : Type u} [CommRing R]
    (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffine G.X.left]
    {T : Over (Spec (CommRingCat.of R))} [IsAffine T.left] {L : GroupScheme T.left}
    (i : L ⟶ (GroupScheme.baseChange T.hom).obj G) (hi : IsClosedSubgroup i)
    (hL : RelativeTorus.IsTorus L) :
    ∃ (n : ℕ) (C : Fin n → Type u) (_ : ∀ k, CommRing (C k)) (_ : ∀ k, Algebra R (C k))
      (b : ∀ k, specOver R (C k) ⟶ T) (I : Fin n → Type u) (_ : ∀ k, Fintype (I k))
      (_ : ∀ k, DecidableEq (I k))
      (f : ∀ k, {f : AffineCoordinates.hopfAlgebra G →ₐ[R] C k ⊗[R] AddMonoidAlgebra R (I k → ℤ) //
        IsHopfPoint R f}),
      (∀ k, Etale (b k).left) ∧ (∀ t : T.left, ∃ k, t ∈ Set.range (b k).left.base) ∧
      (∀ k, Function.Surjective (AlgHom.liftEquiv R (C k) _ _ (f k).1)) ∧
      ∀ k, TorusSubgroupModuli.evaluate i (b k) =
        SubgroupFunctor.range ((splitPointEquiv G (C k)).symm (f k)) := by
  classical
  obtain ⟨𝒰, h𝒰⟩ := hL
  -- an affine étale chart through every point
  let j : T.left → 𝒰.I₀ := fun t => 𝒰.idx t
  let y : ∀ t, 𝒰.X (j t) := fun t => (𝒰.covers t).choose
  let a : ∀ t, (𝒰.X (j t)).affineOpenCover.I₀ := fun t => (𝒰.X (j t)).affineOpenCover.idx (y t)
  let A : T.left → CommRingCat.{u} := fun t => (𝒰.X (j t)).affineOpenCover.X (a t)
  let g : ∀ t, Spec (A t) ⟶ T.left := fun t => (𝒰.X (j t)).affineOpenCover.f (a t) ≫ 𝒰.f (j t)
  have hg : ∀ t, Etale (g t) := fun t => by
    have := 𝒰.map_prop (j t)
    infer_instance
  have hgt : ∀ t, t ∈ Set.range (g t) := fun t => by
    obtain ⟨z, hz⟩ := (𝒰.X (j t)).affineOpenCover.covers (y t)
    refine ⟨z, ?_⟩
    change 𝒰.f (j t) ((𝒰.X (j t)).affineOpenCover.f (a t) z) = t
    rw [hz]
    exact (𝒰.covers t).choose_spec
  have hsplit : ∀ t, IsSplitTorus ((GroupScheme.baseChange (g t)).obj L) := fun t =>
    IsSplitTorus.of_iso (baseChangeCompIso (𝒰.f (j t)) _ L) ((h𝒰 (j t)).baseChange _)
  choose I hI e using hsplit
  let : ∀ t, Fintype (I t) := fun t => Fintype.ofFinite _
  -- finitely many charts cover `T`
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun t => Set.range (g t))
    (fun t => (g t).isOpenMap.isOpen_range) (fun t _ => Set.mem_iUnion.mpr ⟨t, hgt t⟩)
  let ε := s.equivFin
  let t₀ : Fin s.card → T.left := fun k => (ε.symm k).1
  refine ⟨s.card, fun k => ChartRing (A (t₀ k)) (g (t₀ k)), fun k => inferInstance,
    fun k => inferInstance, fun k => chartHom (A (t₀ k)) (g (t₀ k)), fun k => I (t₀ k),
    fun k => inferInstance, fun k => inferInstance,
    fun k => splitPointEquiv G _ (chartRelHom G i (A (t₀ k)) (g (t₀ k)) (I (t₀ k))
      (e (t₀ k)).some), fun k => ?_, fun t => ?_, fun k => ?_, fun k => ?_⟩
  · exact hg (t₀ k)
  · obtain ⟨x, hx, htx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ t))
    refine ⟨ε ⟨x, hx⟩, ?_⟩
    change t ∈ Set.range (g (t₀ (ε ⟨x, hx⟩)))
    rw [show t₀ (ε ⟨x, hx⟩) = x by simp [t₀]]
    exact htx
  · rw [← isClosedSubgroup_splitPointEquiv_symm_iff, Equiv.symm_apply_apply]
    exact isClosedSubgroup_chartRelHom G i hi _ _ _ _
  · rw [Equiv.symm_apply_apply]
    exact evaluate_chartHom G i _ _ _ _

end Langlands.GroupScheme.HomScheme
