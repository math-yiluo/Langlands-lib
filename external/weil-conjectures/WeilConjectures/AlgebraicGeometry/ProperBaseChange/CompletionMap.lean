/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicDerivedInverseLimit
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.CategoryTheory.Sites.CompatibleSheafification
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts

/-!
# The completion map in the explicit shifted-cone model

The strict reductions use one fixed K-flat
model. The target is `Cone(1-s)[-1]`; its lift has zero homotopy component.
-/

@[expose] public section

universe t

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
variable (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
variable (M : AdicKFlatModel X Λ K)

/-- The strict reduction complex at positive level n+1, with Λ scalars retained. -/
noncomputable abbrev adicReductionComplex (n : ℕ) :=
  adicRestrict X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
    (adicChange X (Ideal.Quotient.mk (d.ideal ^ (n + 1))) M.complex)

/-- The strict quotient transition on the fixed model. -/
noncomputable def adicReductionComplexStep (n : ℕ) :
    adicReductionComplex X d M (n + 1) ⟶ adicReductionComplex X d M n :=
  adicTransitionComplex X d.ideal M.complex
    ⟨(n + 1) + 1, Nat.succ_pos (n + 1)⟩ ⟨n + 1, Nat.succ_pos n⟩
    (Nat.le_succ (n + 1))

set_option backward.isDefEq.respectTransparency false in
/-- The quotient augmentation is uniquely determined by m ↦ 1 tensor m on local sections. -/
theorem adicReductionAugmentation_exists (n : ℕ) :
    ∃! f : M.complex ⟶ adicReductionComplex X d M n,
      ∀ (p : ℤ) (U : X.ProEtᵒᵖ) (m : (M.complex.X p).val.obj U),
        (f.f p).val.app U m =
          adicTensorSection X (Ideal.Quotient.mk (d.ideal ^ (n + 1))) _ U 1 m := by
  let : HasSheafify (ProEt.topology X) AddCommGrpCat.{t + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{t, 0} X
  let : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{t, 0} X
  let φ := Ideal.Quotient.mk (d.ideal ^ (n + 1))
  let α := adicConstantMap X φ
  let η (p : ℤ) := (PresheafOfModules.sheafificationAdjunction.{t + 1}
    (𝟙 (adicModuleRing X (Λ ⧸ d.ideal ^ (n + 1))).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1} α (M.complex.X p))
  let a (p : ℤ) : M.complex.X p ⟶ (adicReductionComplex X d M n).X p :=
    { val :=
      { app := fun U ↦
          (ModuleCat.extendRestrictScalarsAdj.{t + 1, t + 1, t + 1} (α.hom.app U).hom).unit.app
            ((M.complex.X p).val.obj U) ≫
          (ModuleCat.restrictScalars (α.hom.app U).hom).map ((η p).app U)
        naturality := by
          intro U V i
          ext m
          have h := PresheafOfModules.naturality_apply (η p) i
            ((1 : (adicConstantRing X (Λ ⧸ d.ideal ^ (n + 1))).obj.obj U)
              ⊗ₜ[(adicConstantRing X Λ).obj.obj U, (α.hom.app U).hom] m)
          change (η p).app V
            (SheafOfModules.changeOfRingsMap α (M.complex.X p) i _) = _ at h
          change (η p).app V _ = _
          rw [show SheafOfModules.changeOfRingsMap α (M.complex.X p) i _ = _ from
            Classical.choose_spec (SheafOfModules.exists_changeOfRingsMap
              α (M.complex.X p) i) 1 m, map_one] at h
          exact h }
    }
  have ha (p : ℤ) (U : X.ProEtᵒᵖ) (m : (M.complex.X p).val.obj U) :
      (a p).val.app U m = adicTensorSection X φ _ U 1 m := rfl
  let f : M.complex ⟶ adicReductionComplex X d M n :=
    { f := a
      comm' := by
        intro i j hij
        ext U m
        let b : SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1}
            α (M.complex.X i) ⟶
            SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1} α (M.complex.X j) :=
          { app := fun U ↦ (ModuleCat.extendScalars (α.hom.app U).hom).map
              ((M.complex.d i j).val.app U)
            naturality := SheafOfModules.changeOfRingsHom_naturality α _ (M.complex.d i j) }
        have hn := congrArg (fun q ↦ q.app U
          ((1 : (adicConstantRing X (Λ ⧸ d.ideal ^ (n + 1))).obj.obj U)
            ⊗ₜ[(adicConstantRing X Λ).obj.obj U, (α.hom.app U).hom] m))
          ((PresheafOfModules.sheafificationAdjunction
            (𝟙 (adicModuleRing X (Λ ⧸ d.ideal ^ (n + 1))).obj)).unit.naturality b)
        change (η j).app U (b.app U _) = _ at hn
        erw [ModuleCat.ExtendScalars.map_tmul] at hn
        exact hn.symm }
  refine ⟨f, ?_, ?_⟩
  · exact ha
  · intro g hg
    apply HomologicalComplex.hom_ext
    intro p
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext m
    exact (hg p U m).trans (ha p U m).symm

/-- The actual quotient chain map, selected by its unique local formula. -/
noncomputable def adicReductionAugmentation (n : ℕ) :
    M.complex ⟶ adicReductionComplex X d M n :=
  Classical.choose (adicReductionAugmentation_exists X d M n)

/-- The termwise product complex B. -/
noncomputable abbrev adicReductionProduct := ∏ᶜ (adicReductionComplex X d M)

/-- The product shift, whose n-th coordinate is the next projection then transition. -/
noncomputable def adicReductionProductShift :
    adicReductionProduct X d M ⟶ adicReductionProduct X d M :=
  towerProductShift (adicReductionComplexStep X d M)

/-- The explicit shifted cone; mappingCocone is definitionally Cone(1-s)[-1].
Its terms are B^(j-1) ⊕ B^j, with differential (-d y -(1-s)x, d x), after
exchanging the two summands of Mathlib's cone convention. -/
noncomputable def adicCompletionComplex :=
  CochainComplex.mappingCocone (𝟙 _ - adicReductionProductShift X d M)

/-- The derived completion target is the localization of the displayed cone complex. -/
noncomputable def adicCompletionObject : proEtaleDerivedCategory X Λ :=
  (adicLocalization X Λ).obj (adicCompletionComplex X d M)

/-- Projection from the shifted cone onto the product of reductions. -/
noncomputable def adicCompletionProjection :
    adicCompletionComplex X d M ⟶ adicReductionProduct X d M :=
  CochainComplex.mappingCocone.fst _

variable {L : proEtaleDerivedCategory X Λ} (N : AdicKFlatModel X Λ L)

-- Shift the strict mapping-cone map and characterize it by both cocone coordinates.
end AlgebraicGeometry.Scheme
