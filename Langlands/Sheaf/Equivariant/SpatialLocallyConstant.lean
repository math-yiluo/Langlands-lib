import Langlands.Sheaf.Equivariant.SpatialInduction
import Langlands.Sheaf.Equivariant.LocallyConstant
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.CategoryTheory.Whiskering

/-! # Full locally constant sheaves under spatial induction -/

noncomputable section

universe u v r w

namespace Langlands.Sheaf.Equivariant.SpatialInduction

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Topology
open Langlands.TopologicalInduction

section Chart

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (H : Subgroup G) (hH : IsOpen (H : Set G))
  (X : Type u) [TopologicalSpace X] [MulAction H X] [ContinuousSMul H X]

/-- Every open of the local space is homeomorphic to its actual unit-chart image. -/
def unitOpenHomeomorph (U : ActionOpens H X) :
    U.openSet ≃ₜ (unitOpen H hH X U).openSet :=
  (isOpenEmbedding_unit (X := X) hH).isEmbedding.homeomorphImage
    (f := unit H (X := X)) (U.openSet : Set X)

@[simp]
theorem unitOpenHomeomorph_apply_coe (U : ActionOpens H X) (x : U.openSet) :
    (unitOpenHomeomorph H hH X U x : Space H X) = unit H x.val := rfl

/-- The open homeomorphisms commute with every actual subgroup-labelled point map. -/
theorem unitOpenHomeomorph_pointMap {U V : ActionOpens H X} (f : U ⟶ V)
    (x : U.openSet) :
    unitOpenHomeomorph H hH X V (LocallyConstantSheaf.pointMap f x) =
      LocallyConstantSheaf.pointMap ((unitFunctor H hH X).map f)
        (unitOpenHomeomorph H hH X U x) := by
  apply Subtype.ext
  exact unit_subgroup_smul f.label x.val

variable {R : Type r} [CommRing R] {M : Type w} [AddCommGroup M] [Module R M]

/-- Pullback by the actual unit-chart homeomorphism on every full section module. -/
def unitSectionsLinearEquiv (U : ActionOpens H X) :
    LocallyConstant (unitOpen H hH X U).openSet M ≃ₗ[R]
      LocallyConstant U.openSet M where
  toFun := LocallyConstant.comapₗ R
    ⟨unitOpenHomeomorph H hH X U, (unitOpenHomeomorph H hH X U).continuous⟩
  invFun := LocallyConstant.comapₗ R
    ⟨(unitOpenHomeomorph H hH X U).symm, (unitOpenHomeomorph H hH X U).symm.continuous⟩
  left_inv s := by
    apply LocallyConstant.ext
    intro x
    exact congrArg s ((unitOpenHomeomorph H hH X U).apply_symm_apply x)
  right_inv s := by
    apply LocallyConstant.ext
    intro x
    exact congrArg s ((unitOpenHomeomorph H hH X U).symm_apply_apply x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem unitSectionsLinearEquiv_apply (U : ActionOpens H X)
    (s : LocallyConstant (unitOpen H hH X U).openSet M) (x : U.openSet) :
    unitSectionsLinearEquiv (R := R) H hH X U s x =
      s (unitOpenHomeomorph H hH X U x) := rfl

@[simp]
theorem unitSectionsLinearEquiv_symm_apply (U : ActionOpens H X)
    (s : LocallyConstant U.openSet M) (x : (unitOpen H hH X U).openSet) :
    (unitSectionsLinearEquiv (R := R) H hH X U).symm s x =
      s ((unitOpenHomeomorph H hH X U).symm x) := rfl

/-- The complete labelled pullbacks agree, including the inverse coefficient operator. -/
theorem unitSectionsLinearEquiv_pullback (τ : Representation R G M)
    {U V : ActionOpens H X} (f : U ⟶ V)
    (s : LocallyConstant (unitOpen H hH X V).openSet M) :
    unitSectionsLinearEquiv (R := R) H hH X U
        (LocallyConstantSheaf.pullback τ ((unitFunctor H hH X).map f) s) =
      LocallyConstantSheaf.pullback (τ.comp H.subtype) f
        (unitSectionsLinearEquiv (R := R) H hH X V s) := by
  apply LocallyConstant.ext
  intro x
  change τ (f.label : G)⁻¹
      (s (LocallyConstantSheaf.pointMap ((unitFunctor H hH X).map f)
        (unitOpenHomeomorph H hH X U x))) =
    τ (f.label : G)⁻¹
      (s (unitOpenHomeomorph H hH X V (LocallyConstantSheaf.pointMap f x)))
  rw [unitOpenHomeomorph_pointMap]

/-- Every original coefficient linear map commutes with the openwise comparison. -/
theorem unitSectionsLinearEquiv_map {N : Type w} [AddCommGroup N] [Module R N]
    (a : M →ₗ[R] N) (U : ActionOpens H X)
    (s : LocallyConstant (unitOpen H hH X U).openSet M) :
    unitSectionsLinearEquiv (R := R) H hH X U (LocallyConstant.mapₗ R a s) =
      LocallyConstant.mapₗ R a (unitSectionsLinearEquiv (R := R) H hH X U s) := rfl

end Chart

section Sheaf

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (H : Subgroup G) (hH : IsOpen (H : Set G))
  (X : Type u) [TopologicalSpace X] [MulAction H X] [ContinuousSMul H X]
  {R : Type r} [CommRing R] {M : Type w} [AddCommGroup M] [Module R M]

/-- The openwise comparisons form an isomorphism of full transport presheaves. -/
def restrictLocallyConstantPresheafIso (τ : Representation R G M) :
    (unitFunctor H hH X).op ⋙ LocallyConstantSheaf.presheaf (X := Space H X) τ ≅
      LocallyConstantSheaf.presheaf (X := X) (τ.comp H.subtype) :=
  NatIso.ofComponents (fun U =>
    (unitSectionsLinearEquiv (R := R) H hH X U.unop).toModuleIso) (by
    intro U V f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    exact unitSectionsLinearEquiv_pullback H hH X τ f.unop s)

/-- Restriction of the full ambient locally constant sheaf is the full local sheaf. -/
def restrictLocallyConstantIso (τ : Representation R G M) :
    (restrict H hH X (ModuleCat.{max u w} R)).obj
        (LocallyConstantSheaf.sheaf (X := Space H X) τ) ≅
      LocallyConstantSheaf.sheaf (X := X) (τ.comp H.subtype) :=
  (sheafProperty H X (ModuleCat.{max u w} R)).isoMk
    (restrictLocallyConstantPresheafIso H hH X τ)

@[simp]
theorem restrictLocallyConstantIso_hom_app (τ : Representation R G M)
    (U : ActionOpens H X) (s : LocallyConstant (unitOpen H hH X U).openSet M)
    (x : U.openSet) :
    LocallyConstant.toFun
        (((restrictLocallyConstantIso H hH X τ).hom.hom.app (op U)) s) x =
      s (unitOpenHomeomorph H hH X U x) := rfl

@[simp]
theorem restrictLocallyConstantIso_inv_app (τ : Representation R G M)
    (U : ActionOpens H X) (s : LocallyConstant U.openSet M)
    (x : (unitOpen H hH X U).openSet) :
    LocallyConstant.toFun
        (((restrictLocallyConstantIso H hH X τ).inv.hom.app (op U)) s) x =
      s ((unitOpenHomeomorph H hH X U).symm x) := rfl

/-- The entire comparison is natural in every original coefficient intertwiner. -/
def restrictLocallyConstantNatIso :
    LocallyConstantSheaf.functor R G (Space H X) ⋙
        restrict H hH X (ModuleCat.{max u w} R) ≅
      Rep.resFunctor H.subtype ⋙ LocallyConstantSheaf.functor R H X :=
  NatIso.ofComponents (fun P => restrictLocallyConstantIso H hH X P.ρ) (by
    intro P Q a
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    exact unitSectionsLinearEquiv_map H hH X a.hom.toLinearMap U.unop s)

/-- These actual right-Kan indexing categories fit in the section-module universe. -/
instance unitChartModuleLimits (U : (ActionOpens G (Space H X))ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow U (unitFunctor H hH X).op)
      (ModuleCat.{max u w} R) :=
  ModuleCat.hasLimitsOfShape

/-- Genuine spatial induction of the full local coefficient sheaf recovers the
full ambient coefficient sheaf, naturally in every coefficient intertwiner. -/
def induceLocallyConstantNatIso :
    (Rep.resFunctor H.subtype ⋙ LocallyConstantSheaf.functor R H X) ⋙
        induce H hH X (ModuleCat.{max u w} R) ≅
      LocallyConstantSheaf.functor R G (Space H X) :=
  Functor.isoWhiskerRight (restrictLocallyConstantNatIso (R := R) H hH X).symm
      (induce H hH X (ModuleCat.{max u w} R)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (LocallyConstantSheaf.functor R G (Space H X))
      (induceRestrictIso H hH X (ModuleCat.{max u w} R)) ≪≫
    Functor.rightUnitor _

/-- The converse comparison is an isomorphism of full sheaves, obtained from
the actual right-Kan inverse and the explicit unit-chart comparison. -/
def induceLocallyConstantIso (τ : Representation R G M) :
    (induce H hH X (ModuleCat.{max u w} R)).obj
        (LocallyConstantSheaf.sheaf (X := X) (τ.comp H.subtype)) ≅
      LocallyConstantSheaf.sheaf (X := Space H X) τ :=
  (induceLocallyConstantNatIso H hH X).app (Rep.of τ)

end Sheaf

end Langlands.Sheaf.Equivariant.SpatialInduction
