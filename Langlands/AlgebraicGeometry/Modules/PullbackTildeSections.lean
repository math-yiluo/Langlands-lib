import Langlands.AlgebraicGeometry.Modules.PullbackAffineSections
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Langlands.AlgebraicGeometry.Modules.DerivedSections

/-! # Canonical sections of an actual associated-sheaf pullback -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct ChangeOfRings

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.Scheme.Modules

open Langlands.AlgebraicGeometry.Modules.DerivedSections

variable {R : CommRingCat.{u}} {X : Scheme.{u}}
    (p : X ⟶ Spec R) (C : ModuleCat.{u} R)

/-- The actual global pullback of every associated-sheaf generator, linear over R. -/
def pullbackTildeGlobalSections : C ⟶
    (relativeGlobalSections p).obj ((Scheme.Modules.pullback p).obj (tilde C)) :=
  (tilde.isoTop C).hom ≫ (moduleSpecΓFunctor (R := CommRingCat.of R)).map
    ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app (tilde C))

/-- Restricting the actual global generator is restricted actual section pullback. -/
theorem pullbackTildeGlobalSections_restrict (U : X.Opens) (c : C) :
    ((Scheme.Modules.pullback p).obj (tilde C)).presheaf.map
      (homOfLE (show U ≤ ⊤ from le_top)).op (pullbackTildeGlobalSections p C c) =
      sectionPullbackLE p (tilde C) (show U ≤ p ⁻¹ᵁ ⊤ from le_top) (tilde.toOpen C ⊤ c) := rfl

/-- Change the scalar-extension base from R to the actual global section ring
of Spec R, retaining the prescribed section pullback map. -/
def pullbackTildeScalarIso (U : X.Opens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom p U
    (ModuleCat.extendScalars (algebraMap R Γ(X, U))).obj C ≅
      (ModuleCat.extendScalars (p.appLE ⊤ U le_top).hom).obj
        (ModuleCat.of Γ(Spec R, ⊤) Γ(tilde C, ⊤)) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom p U
  let φ := (Scheme.ΓSpecIso R).inv.hom
  let ψ := (p.appLE ⊤ U le_top).hom
  let F : ModuleCat.{u} Γ(Spec R, ⊤) :=
    ModuleCat.of _ Γ(tilde C, ⊤)
  let : (ModuleCat.restrictScalars φ).IsEquivalence :=
    inferInstanceAs (ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv.toRingHom)).IsEquivalence
  let E : (ModuleCat.extendScalars φ).obj ((moduleSpecΓFunctor
      (R := CommRingCat.of R)).obj (tilde C)) ≅ F :=
    asIso ((ModuleCat.extendRestrictScalarsAdj φ).counit.app F)
  exact (ModuleCat.extendScalars (algebraMap R Γ(X, U))).mapIso (tilde.isoTop C) ≪≫
    (ModuleCat.extendScalarsComp φ ψ).app _ ≪≫
      (ModuleCat.extendScalars ψ).mapIso E

/-- The scalar-base comparison preserves the distinguished tensor generators. -/
theorem pullbackTildeScalarIso_one_tmul (U : X.Opens) (c : C) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom p U
    (pullbackTildeScalarIso p C U).hom ((1 : Γ(X, U)) ⊗ₜ[R,algebraMap R Γ(X, U)] c) =
      (1 : Γ(X, U)) ⊗ₜ[Γ(Spec R, ⊤),(p.appLE ⊤ U le_top).hom]
        (show Γ(tilde C, ⊤) from tilde.toOpen C ⊤ c) := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom p U
  simp only [pullbackTildeScalarIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, ConcreteCategory.comp_apply, asIso_hom,
    ModuleCat.ExtendScalars.map_tmul]
  have hcomp := ModuleCat.extendScalarsComp_hom_app_one_tmul
    (Scheme.ΓSpecIso R).inv.hom (p.appLE ⊤ U le_top).hom
    ((moduleSpecΓFunctor (R := R)).obj (tilde C)) ((tilde.isoTop C).hom c)
  erw [hcomp, ModuleCat.ExtendScalars.map_tmul]
  congr 1
  exact ModuleCat.extendRestrictScalarsAdj_counit_app_apply_one_tmul
    (f := (Scheme.ΓSpecIso R).inv.hom)
    (ModuleCat.of Γ(Spec R, ⊤) Γ(tilde C, ⊤))
    (show Γ(tilde C, ⊤) from tilde.toOpen C ⊤ c)

/-- The actual affine tensor sections comparison for the pullback of an
associated sheaf, with no finite-projective or flatness assumption. -/
def pullbackTildeSectionsEquiv (U : X.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom p U
    Γ(X, U) ⊗[R] C ≃ₗ[Γ(X, U)]
      Γ((Scheme.Modules.pullback p).obj (tilde C), U) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom p U
  let h : (U : X.Opens) ≤ p ⁻¹ᵁ ⊤ := le_top
  let : IsIso (pullbackTensorMap p (tilde C) h) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (pullbackTensorMap_bijective p (tilde C) h U.2 (isAffineOpen_top _))
  exact (extendScalarsAlgebraEquiv R Γ(X, U) C).symm ≪≫ₗ
    (pullbackTildeScalarIso p C U).toLinearEquiv ≪≫ₗ
      (asIso (pullbackTensorMap p (tilde C) h)).toLinearEquiv

/-- The actual affine tensor equivalence sends 1⊗c to the restriction of
the canonical actual global pulled-back generator. -/
theorem pullbackTildeSectionsEquiv_one_tmul (U : X.affineOpens) (c : C) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom p U
    pullbackTildeSectionsEquiv p C U ((1 : Γ(X, U)) ⊗ₜ[R] c) =
      ((Scheme.Modules.pullback p).obj (tilde C)).presheaf.map
        (homOfLE (show (U : X.Opens) ≤ ⊤ from le_top)).op
          (pullbackTildeGlobalSections p C c) := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom p U
  change pullbackTensorMap p (tilde C) (show (U : X.Opens) ≤ p ⁻¹ᵁ ⊤ from le_top)
    ((pullbackTildeScalarIso p C U).hom
      ((1 : Γ(X, U)) ⊗ₜ[R,algebraMap R Γ(X, U)] c)) = _
  rw [pullbackTildeScalarIso_one_tmul, pullbackTensorMap_one_tmul]
  rfl

/-- The actual affine tensor comparison is exactly the scalar-linear map
induced by the canonical restricted global generators. -/
theorem pullbackTildeSectionsEquiv_tmul (U : X.affineOpens) (a : Γ(X, U)) (c : C) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom p U
    pullbackTildeSectionsEquiv p C U (a ⊗ₜ[R] c) =
      a • ((Scheme.Modules.pullback p).obj (tilde C)).presheaf.map
        (homOfLE (show (U : X.Opens) ≤ ⊤ from le_top)).op
          (pullbackTildeGlobalSections p C c) := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom p U
  have h : (a ⊗ₜ[R] c : Γ(X, U) ⊗[R] C) =
      a • ((1 : Γ(X, U)) ⊗ₜ[R] c) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h, map_smul, pullbackTildeSectionsEquiv_one_tmul]

/-- The actual affine tensor comparison commutes with restriction of the
base open and the coefficient tensor factor. -/
theorem pullbackTildeSectionsEquiv_restrict {U V : X.affineOpens}
    (h : (V : X.Opens) ≤ U) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom p U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom p V
    ∀ z : Γ(X, U) ⊗[R] C,
      ((Scheme.Modules.pullback p).obj (tilde C)).presheaf.map (homOfLE h).op
        (pullbackTildeSectionsEquiv p C U z) =
      pullbackTildeSectionsEquiv p C V
        (TensorProduct.map (Scheme.TwoAffineOpenCover.restrictAlgHom p h).toLinearMap
          (LinearMap.id : C →ₗ[R] C) z) := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom p U
  let := Scheme.TwoAffineOpenCover.algebraOfHom p V
  intro z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a c =>
    rw [TensorProduct.map_tmul, pullbackTildeSectionsEquiv_tmul,
      pullbackTildeSectionsEquiv_tmul, Scheme.Modules.map_smul]
    congr 1
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl

end Langlands.Scheme.Modules


