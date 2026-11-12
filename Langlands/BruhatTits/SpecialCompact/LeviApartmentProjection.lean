import Langlands.BruhatTits.SpecialCompact.LeviApartmentRestriction

/-! # The affine projection to the prescribed Levi apartment -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.GroupScheme.RealTorusSpace

namespace Langlands.BruhatTits.SpecialCompact

variable {F : Type u} [Field F]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G M : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffineHom M.X.hom]
    [Smooth G.X.hom] [ConnectedSpace G.X.left] [LocallyOfFiniteType M.X.hom]
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G) (iM : S.toGrp ⟶ M)
    [Mono i.hom.hom.left] [Mono iM.hom.hom.left]
    (j : M ⟶ G) (hcomp : iM ≫ j = i) (ζ : cocharacterLattice S)
    (hj : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy j)
    (hjc : IsClosedSubgroup j) (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    {ω : Fˣ → ℝ} (D : KPApartmentData i ω)


include hcomp hj in
/-- The ambient root annihilator lies in the Levi root annihilator because
the actual Levi roots are a subset at the same torus. -/
theorem rootAnnihilator_le_levi : rootAnnihilator i ≤ rootAnnihilator iM := by
  intro v hv
  apply mem_rootAnnihilator.mpr
  intro a ha
  exact mem_rootAnnihilator.mp hv a (relativeRoots_subset_of_factor hj iM hcomp ha)

/-- The quotient linear map induced by identity on the full cocharacter space. -/
def leviTranslationProjection : TranslationSpace i →ₗ[ℝ] TranslationSpace iM :=
  (rootAnnihilator i).mapQ (rootAnnihilator iM) LinearMap.id
    (by simpa only [Submodule.comap_id] using rootAnnihilator_le_levi i iM j hcomp ζ hj)

@[simp] theorem leviTranslationProjection_mk (v : V S) :
    leviTranslationProjection i iM j hcomp ζ hj (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk v := rfl

/-- The actual linear apartment projection is surjective. -/
theorem leviTranslationProjection_surjective :
    Function.Surjective (leviTranslationProjection i iM j hcomp ζ hj) := by
  intro v
  induction v using Submodule.Quotient.induction_on with
  | _ v => exact ⟨Submodule.Quotient.mk v, rfl⟩

/-- The linear kernel is exactly the additional annihilator directions,
viewed inside the original ambient translation quotient. -/
theorem ker_leviTranslationProjection :
    LinearMap.ker (leviTranslationProjection i iM j hcomp ζ hj) =
      (rootAnnihilator iM).map (rootAnnihilator i).mkQ := by
  rw [leviTranslationProjection, Submodule.ker_mapQ, Submodule.comap_id]

/-- The actual Levi root form pulls back to the same ambient root form. -/
theorem rootForm_comp_leviTranslationProjection (a : relativeRoots iM) :
    (rootForm iM a).comp (leviTranslationProjection i iM j hcomp ζ hj) =
      rootForm i ⟨a, relativeRoots_subset_of_factor hj iM hcomp a.property⟩ := by
  apply LinearMap.ext
  intro v
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    simp only [LinearMap.comp_apply, leviTranslationProjection_mk, rootForm_mk]

/-- Projection respects the translations induced by the same full real
cocharacter vector. -/
theorem leviApartmentProjection_mk_vadd (v : V S) (x : D.Apartment) :
    leviApartmentProjection hS i iM j hcomp ζ hj hjc hG hi D
        ((Submodule.Quotient.mk v : TranslationSpace i) +ᵥ x) =
      (Submodule.Quotient.mk v : TranslationSpace iM) +ᵥ
        leviApartmentProjection hS i iM j hcomp ζ hj hjc hG hi D x := by
  apply KPApartmentData.Apartment.ext
  exact leviRestrictedRootFunctionFamily_vadd iM j hS i hcomp ζ hj hjc x.val v

/-- The actual restriction of apartment points as an affine map between the
existing quotient translation spaces. -/
def leviApartmentAffineProjection :
    D.Apartment →ᵃ[ℝ] (leviRestrictedApartmentData hS i iM j hcomp ζ hj hjc hG hi D).Apartment where
  toFun := leviApartmentProjection hS i iM j hcomp ζ hj hjc hG hi D
  linear := leviTranslationProjection i iM j hcomp ζ hj
  map_vadd' := by
    intro x v
    induction v using Submodule.Quotient.induction_on with
    | _ v => exact leviApartmentProjection_mk_vadd hS i iM j hcomp ζ hj hjc hG hi D v x

/-- This affine projection is surjective on the actual apartment carriers. -/
theorem leviApartmentAffineProjection_surjective :
    Function.Surjective (leviApartmentAffineProjection hS i iM j hcomp ζ hj hjc hG hi D) :=
  leviApartmentProjection_surjective hS i iM j hcomp ζ hj hjc hG hi D

/-- Two ambient points have the same projected point precisely when their
translation difference belongs to the explicit quotient kernel. -/
theorem leviApartmentProjection_eq_iff (x y : D.Apartment) :
    leviApartmentProjection hS i iM j hcomp ζ hj hjc hG hi D x =
        leviApartmentProjection hS i iM j hcomp ζ hj hjc hG hi D y ↔
      x -ᵥ y ∈ (rootAnnihilator iM).map (rootAnnihilator i).mkQ := by
  rw [← ker_leviTranslationProjection i iM j hcomp ζ hj]
  let f := leviApartmentAffineProjection hS i iM j hcomp ζ hj hjc hG hi D
  change f x = f y ↔ f.linear (x -ᵥ y) = 0
  rw [f.linearMap_vsub]
  exact vsub_eq_zero_iff_eq.symm

end Langlands.BruhatTits.SpecialCompact
