/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibility
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal

/-!
# Two-term resolutions of finite constant scalar models

Source: Bhatt--Scholze, Proposition 6.8.11(3), Lemma 6.8.2(1); Stacks Tags 093J,
093M (auxiliary; not a blueprint node).

The model functor first forms discrete constant modules, extends scalars by the map
sending a scalar to the constant continuous function, and applies the monoidal inverse
image from the point. Thus it is precisely B_T tensor over the discrete constant A,
not a tensor over the continuous coefficient ring on the point.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.ProEtale.FiniteConstantModel

variable (A : Type u) [CommRing A]

/-- The ordinary scalar action, as an integer-bilinear map on the lifted scalar ring.
Source: Stacks Tag 093J, constant modules
(auxiliary; not a blueprint node). -/
def scalarAction (P : ModuleCat.{u + 1} A) :
    AddCommGrpCat.of (ULift.{u + 1} A) ⊗ AddCommGrpCat.of P ⟶ AddCommGrpCat.of P :=
  AddCommGrpCat.ofHom (TensorProduct.lift (LinearMap.mk₂ ℤ
    (fun (a : ULift.{u + 1} A) (p : P) ↦ a.down • p)
    (fun _ _ _ ↦ add_smul _ _ _)
    (fun n a p ↦ by simp [mul_smul, Int.cast_smul_eq_zsmul])
    (fun _ _ _ ↦ smul_add _ _ _)
    (fun n a p ↦ by simp [smul_comm n a.down p]))).toAddMonoidHom

/-- The specified scalar action satisfies the internal module axioms.
Source: Stacks Tag 093J, constant modules
(auxiliary; not a blueprint node).
Proof: evaluate the unit equation on n tensor p and the associativity equation on
(a tensor b) tensor p. They become one_smul and mul_smul, respectively; integer
bilinearity extends these equalities to the whole tensor products. -/
theorem scalarAction_laws (P : ModuleCat.{u + 1} A) :
    MonObj.one (X := AddCommGrpCat.of (ULift.{u + 1} A)) ▷ AddCommGrpCat.of P ≫
        scalarAction A P = (λ_ (AddCommGrpCat.of P)).hom ∧
    MonObj.mul (X := AddCommGrpCat.of (ULift.{u + 1} A)) ▷ AddCommGrpCat.of P ≫
        scalarAction A P =
      (α_ _ _ _).hom ≫ AddCommGrpCat.of (ULift.{u + 1} A) ◁ scalarAction A P ≫
        scalarAction A P := by
  constructor
  · apply AddCommGrpCat.hom_ext_toIntLinearMap
    apply TensorProduct.ext'
    intro n p
    change (n.down : A) • p = n.down • p
    simp [Int.cast_smul_eq_zsmul]
  · apply AddCommGrpCat.hom_ext_toIntLinearMap
    apply TensorProduct.ext_threefold
    intro a b p
    change (a.down * b.down) • p = a.down • b.down • p
    exact mul_smul _ _ _

/-- The ordinary module, with its actual scalar action, as an internal abelian-group module.
Source: Stacks Tag 093J
(auxiliary; not a blueprint node). -/
instance scalarModule (P : ModuleCat.{u + 1} A) :
    ModObj (AddCommGrpCat.of (ULift.{u + 1} A)) (AddCommGrpCat.of P) :=
  ModObj.mk' _ (scalarAction A P) (scalarAction_laws A P).1 (scalarAction_laws A P).2

/-- Linearity is exactly compatibility with the specified internal action.
Source: Stacks Tag 093J
(auxiliary; not a blueprint node).
Proof: evaluate on a tensor p. Both sides are a times f(p), by f.map_smul;
the tensor universal property proves equality. -/
theorem scalarMap_linear {P Q : ModuleCat.{u + 1} A} (f : P ⟶ Q) :
    IsModHom (AddCommGrpCat.of (ULift.{u + 1} A))
      (AddCommGrpCat.ofHom f.hom.toAddMonoidHom) := by
  constructor
  apply AddCommGrpCat.hom_ext_toIntLinearMap
  apply TensorProduct.ext'
  intro a p
  change f.hom (a.down • p) = a.down • f.hom p
  exact f.hom.map_smul _ _

/-- The scalar module functor retains the underlying additive maps.
Source: Stacks Tag 093J
(auxiliary; not a blueprint node). -/
def scalarModules : ModuleCat.{u + 1} A ⥤ Mod Ab.{u + 1}
    (AddCommGrpCat.of (ULift.{u + 1} A)) where
  obj P := ⟨AddCommGrpCat.of P⟩
  map f :=
    { hom := AddCommGrpCat.ofHom f.hom.toAddMonoidHom
      isModHom := scalarMap_linear A f }

variable [TopologicalSpace A] [IsTopologicalRing A]

/-- Constant scalar functions, before sheafification.
Source: Bhatt--Scholze, Definition 6.8.1
(auxiliary; not a blueprint node). -/
def constantFunctions :
    (Functor.const Profinite.{u}ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A)) ⟶
      (Profinite.continuousCoefficientRingObj A).obj where
  app S := AddCommGrpCat.ofHom
    { toFun := fun a ↦ ULift.up (ContinuousMap.const S.unop a.down)
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  naturality _ _ _ := rfl

/-- The canonical discrete-constant-to-continuous coefficient map, by sheafification.
Source: Bhatt--Scholze, Definition 6.8.1; Stacks Tag 093J
(auxiliary; not a blueprint node). -/
def scalarToContinuous :
    (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} A)) ⟶ Profinite.continuousCoefficientRingObj A :=
  ((sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}).homEquiv _ _).symm
    (constantFunctions A)

/-- The constant scalar map preserves the ring operations.
Source: Bhatt--Scholze, Definition 6.8.1
(auxiliary; not a blueprint node).
Proof: constant functions preserve one and multiplication sectionwise. The monoidal
sheafification adjunction transports these two equations to scalarToContinuous. -/
theorem scalarToContinuous_isMonHom : IsMonHom (scalarToContinuous A) := by
  let : MonObj (Profinite.continuousCoefficientRingObj A).obj :=
    inferInstanceAs (MonObj (Profinite.continuousCoefficientRingPresheaf A ⋙
      forget₂ RingCat.{u + 1} Ab.{u + 1}))
  have : IsMonHom (constantFunctions A) :=
    { one_hom := by
        ext S n
        change ULift.up (ContinuousMap.const S.unop (n.down : A)) =
          (n.down : ULift.{u + 1} C(S.unop, A))
        ext x
        simp
      mul_hom := by
        ext S : 2
        apply AddCommGrpCat.hom_ext_toIntLinearMap
        apply TensorProduct.ext'
        intro a b
        rfl }
  have h : IsMonHom
      ((presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map
        (constantFunctions A) ≫
      (Sheaf.sheafifyRingPresheafIso (coherentTopology Profinite.{u})
        (Profinite.continuousCoefficientRingSheaf A)).hom) := inferInstance
  dsimp only [scalarToContinuous]
  rw [Adjunction.homEquiv_counit]
  exact @IsMonHom.of_eq _ _ _ _ _ _ _ _ _ _
    (Functor.monObjObj_comp (Functor.const Profinite.{u}ᵒᵖ)
      (presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      (AddCommGrpCat.of (ULift.{u + 1} A))).symm rfl h

attribute [instance] scalarToContinuous_isMonHom

set_option linter.unusedSectionVars false in
/-- The constant scalar ring is commutative for the transported monoidal structure.
Source: Stacks Tag 093J
(auxiliary; not a blueprint node).
Proof: multiplication before sheafification is commutative, since A is commutative.
Sheafification is symmetric monoidal, so it transports that equality. -/
theorem constantScalars_commutative :
    IsCommMonObj ((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} A))) := by
  let : (Functor.const Profinite.{u}ᵒᵖ :
      Ab.{u + 1} ⥤ Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}).LaxBraided :=
    { braided X Y := by
        apply NatTrans.ext
        funext S
        change 𝟙 (X ⊗ Y) ≫ (β_ X Y).hom = (β_ X Y).hom ≫ 𝟙 (Y ⊗ X)
        simp only [Category.id_comp, Category.comp_id] }
  exact Functor.isCommMonObj_obj (F :=
    (Functor.const Profinite.{u}ᵒᵖ : Ab.{u + 1} ⥤ Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}) ⋙
      presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1})

attribute [instance] constantScalars_commutative

/-- The canonical local model B_T tensor over discrete constant A with constant P.
The displayed composite also fixes its value on every scalar linear map.
Source: Bhatt--Scholze, Proposition 6.8.11(3), scalar extension construction
(auxiliary; not a blueprint node). -/
def modelFunctor (T : Scheme.{u}) : ModuleCat.{u + 1} A ⥤
    Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj A) T) :=
  scalarModules A ⋙
    (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).mapMod
      (AddCommGrpCat.of (ULift.{u + 1} A)) ⋙
    Mod.extendScalars (scalarToContinuous A) ⋙
    (upperStarFromPoint T).mapMod (Profinite.continuousCoefficientRingObj A)

/-- The finite scalar free module, with a harmless universe lift of its coordinates.
Source: Bhatt--Scholze, Proposition 6.8.11(3)
(auxiliary; not a blueprint node). -/
def freeScalars (n : ℕ) : ModuleCat.{u + 1} A :=
  ModuleCat.of A (Fin n → ULift.{u + 1} A)

end AlgebraicGeometry.ProEtale.FiniteConstantModel

namespace AlgebraicGeometry.ProEtale.FiniteConstantModel

universe uC vC

private def freeCoordinates (A : Type u) [CommRing A] (n : ℕ) :
    (Fin n → ULift.{u + 1} A) ≃ₗ[A] (Fin n → A) :=
  LinearEquiv.piCongrRight (fun _ ↦ ULift.moduleEquiv)

section FreeModels

variable (A : Type u) [CommRing A]

private lemma scalarModules_additive : (scalarModules A).Additive where
  map_add := by intros; rfl

private def scalarRegularIso :
    (scalarModules A).obj (ModuleCat.of A (ULift.{u + 1} A)) ≅
      Mod.regular (AddCommGrpCat.of (ULift.{u + 1} A)) :=
  Mod.isoMk (Iso.refl _) (by
    apply AddCommGrpCat.hom_ext_toIntLinearMap
    apply TensorProduct.ext'
    intro a b
    rfl)

private def scalarFiniteFreeIso (n : ℕ) :
    (scalarModules A).obj (freeScalars A n) ≅
      Mod.finiteFree (AddCommGrpCat.of (ULift.{u + 1} A)) n := by
  have : (scalarModules A).Additive := scalarModules_additive A
  exact (scalarModules A).mapIso
      (ModuleCat.biproductIsoPi (fun _ : Fin n ↦ ModuleCat.of A (ULift.{u + 1} A))).symm ≪≫
    (scalarModules A).mapBiproduct _ ≪≫ biproduct.mapIso (fun _ ↦ scalarRegularIso A)

private lemma scalarModules_preservesFiniteColimits :
    PreservesFiniteColimits (scalarModules A) := by
  let V : ModuleCat.{u + 1} A ⥤ Ab.{u + 1} := forget₂ _ _
  have : PreservesColimitsOfSize.{0, 0} V := by
    exact ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u, 0, 0} A
  have : PreservesFiniteColimits V := ⟨fun _ _ _ ↦ inferInstance⟩
  have : PreservesFiniteColimits (scalarModules A ⋙
      Mod.forget (AddCommGrpCat.of (ULift.{u + 1} A))) :=
    inferInstanceAs (PreservesFiniteColimits V)
  exact preservesFiniteColimits_of_reflects_of_preserves _
    (Mod.forget (AddCommGrpCat.of (ULift.{u + 1} A)))

variable [TopologicalSpace A] [IsTopologicalRing A]

end FreeModels

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]

end AlgebraicGeometry.ProEtale.FiniteConstantModel
