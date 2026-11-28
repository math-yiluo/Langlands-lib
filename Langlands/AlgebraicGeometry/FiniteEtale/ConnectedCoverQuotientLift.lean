import Langlands.AlgebraicGeometry.FiniteEtale.CoverStabilizerLift
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricFiberFiniteProof
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricGaloisFiberFunctorProof
import Mathlib.CategoryTheory.Galois.Prorepresentability

/-! # Lifting quotient values through a connected pullback cover -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry PreGaloisCategory

universe u v

namespace Langlands.AlgebraicGeometry.FiniteEtale

/-- At a point with nonempty fibre, a cover with connected source is a connected object
of the Galois category. -/
theorem cover_isConnected_of_connectedSpace {S : Scheme.{u}} [ConnectedSpace S]
    [IsLocallyNoetherian S] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (Y : Cover S) [ConnectedSpace Y.obj.left] (x : Fiber s Y) :
    IsConnected Y := by
  let hs := geometricFiberFinite s
  obtain ⟨hC, hF⟩ := geometricGaloisFiberFunctor s hs
  let F := fiberFunctor s hs
  refine ⟨not_initial_of_inhabited F (X := Y) x, ?_⟩
  intro Z i hmono hZi
  obtain ⟨z⟩ := (not_initial_iff_fiber_nonempty F Z).mp hZi
  obtain ⟨a⟩ : Nonempty (Spec (.of Ω)) := inferInstance
  have hz : (Set.range i.hom.left).Nonempty := ⟨_, z.left a, rfl⟩
  have hs : Function.Surjective i.hom.left :=
    Set.range_eq_univ.mp ((EpiPreservation.isClopen_range_hom_left i).eq_univ hz)
  have : Mono i.hom := preserves_mono_of_preservesLimit (inclusion S) i
  have : Etale i.hom.left := (EpiPreservation.finiteEtale_hom_left i).2
  have : IsFinite i.hom.left := (EpiPreservation.finiteEtale_hom_left i).1
  have : Surjective i.hom.left := ⟨hs⟩
  have : IsIso ((Over.forget S).map i.hom) :=
    show IsIso i.hom.left from Flat.isIso_of_surjective_of_mono _
  have : IsIso ((inclusion S).map i) :=
    show IsIso i.hom from isIso_of_reflects_iso i.hom (Over.forget S)
  exact isIso_of_reflects_iso i (inclusion S)

/-- If a pointed representation kills the fundamental group of one cover and the cover
remains connected after pullback, the pointed map from the new base reaches the full image
of the representation. -/
def ConnectedCoverQuotientLiftStatement : Prop :=
  ∀ {S S' : Scheme.{u}} [ConnectedSpace S'] [IsLocallyNoetherian S']
    (f : S' ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ S') (Y : Cover S) (x : Fiber (t ≫ f) Y),
    ConnectedSpace ((pullbackFunctor f).obj Y).obj.left →
    ∀ {H : Type v} [Group H]
      (ρ : FundamentalGroup (t ≫ f) (geometricFiberFinite (t ≫ f)) →* H),
      ρ.comp (fundamentalGroupMap Y.obj.hom x.left (t ≫ f) (Over.w x)
        (geometricFiberFinite x.left) (geometricFiberFinite (t ≫ f))) = 1 →
      ∀ g : FundamentalGroup (t ≫ f) (geometricFiberFinite (t ≫ f)),
        ∃ h : FundamentalGroup t (geometricFiberFinite t),
          ρ (fundamentalGroupMap f t (t ≫ f) rfl (geometricFiberFinite t)
            (geometricFiberFinite (t ≫ f)) h) = ρ g

/-- Match the action on the selected lift by transitivity in the connected pulled-back cover.
The difference lies in the stabilizer, which is killed by the representation. -/
theorem connectedCoverQuotientLift : ConnectedCoverQuotientLiftStatement.{u, v} := by
  intro S S' _ _ f Ω _ _ t Y x hconn H _ ρ hρ g
  let s := t ≫ f
  let ht := geometricFiberFinite t
  let hs := geometricFiberFinite s
  let G := fundamentalGroupMap f t s rfl ht hs
  let Z := (pullbackFunctor f).obj Y
  let e := pullbackFiberEquiv f t s rfl Y
  obtain ⟨hC, hF⟩ := geometricGaloisFiberFunctor t ht
  have hZ : IsConnected Z := cover_isConnected_of_connectedSpace t Z (e x)
  have : MulAction.IsPretransitive (FundamentalGroup t ht) (Fiber t Z) :=
    FiberFunctor.isPretransitive_of_isConnected (fiberFunctor t ht) Z
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (FundamentalGroup t ht) (e x) (e (g • x))
  have hx : G h • x = g • x := e.injective ((pullbackFiberEquiv_smul f t s rfl ht hs h Y x).trans hh)
  have hstab : ((G h)⁻¹ * g) • x = x := by rw [mul_smul, ← hx, inv_smul_smul]
  obtain ⟨k, hk⟩ := (exists_fundamentalGroupMap_eq_iff s hs Y x (geometricFiberFinite x.left) _).mpr hstab
  have heq : ρ ((G h)⁻¹ * g) = 1 := by
    rw [← hk]
    exact DFunLike.congr_fun hρ k
  rw [map_mul, map_inv, inv_mul_eq_one] at heq
  exact ⟨h, heq⟩

end Langlands.AlgebraicGeometry.FiniteEtale
