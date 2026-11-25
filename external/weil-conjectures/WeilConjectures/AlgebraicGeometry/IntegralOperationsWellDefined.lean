/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.AlgebraicGeometry.IntegralReductionTowerUnrestricted
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import all WeilConjectures.AlgebraicGeometry.IntegralReductionTowerUnrestricted
import Mathlib.CategoryTheory.Localization.Pi
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellationIndependentCoefficients
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KernelShiftedMappingCone
import WeilConjectures.Algebra.Homology.RingedKFlatSingleTensorComparison
import all WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
import WeilConjectures.AlgebraicGeometry.IntegralReductionTransitionSemilinear
import WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import WeilConjectures.CategoryTheory.StrictRoosComparison
import WeilConjectures.CategoryTheory.StrictRoosDerivation
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import all WeilConjectures.SecSmoothPurity.NormalizedScalarTensorTransitions

/-! # Well-definedness of integral pullback and completed tensor product

Source: Stacks Project, Tags 06YS, 06YT, 0G7E and 08TC; Bhatt--Scholze,
Definition 3.4.10 and Lemma 6.5.9(4)
(auxiliary; not a blueprint node).

The natural-number level n denotes exponent n+1. All towers and their maps are
constructed before localization; the Roos complex uses termwise products and the
specified shifted cone. The final descent includes its natural comparison data.

## Main definitions

* `integralOperationsPullbackComplexFunctor`: strict finite pullback followed by Roos.
* `integralOperationsTensorComplexFunctor`: direct-sum finite tensor followed by Roos.

## Main statements

* `integralOperationsWellDefined`: quasi-isomorphism invariance and normalized descent.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 512

universe t u a b c d r a' b' c' d'

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

-- Prefer the module's recorded tensor instances during private proof search.
attribute [-instance] SheafOfModules.cochainModulesMonoidal
  SheafOfModules.cochainModulesSymmetric SheafOfModules.cochainModulesPreadditive
  SheafOfModules.cochainTensorLocalizationIsMonoidal
  SheafOfModules.cochainTensorLeftPreservesColimits
  SheafOfModules.cochainTensorRightPreservesColimits

-- These proof imports carry broad diagram instances; prefer the concrete instances here.
attribute [local instance 1] CategoryTheory.CochainPullback.RingedPullback.additive
  CategoryTheory.CochainPullback.CoefficientSquare.additive'
  CategoryTheory.CochainPullback.StrictCoefficient.Diagram.additive
  CategoryTheory.CochainPullback.extensionFunctorAdditive

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

/-- The commutative-ring forgetful functor, recorded once for integral operations.
Source: Stacks Tag 03DA (auxiliary; not a blueprint node). -/
@[reducible] def WeilConjectures.integralOperationsRingForget : CommRingCat.{r} ⥤ RingCat.{r} :=
  forget₂ CommRingCat RingCat

universe wForget uForget vForget

/-- Forget commutativity in coefficient sheaves, with its functor data recorded once.
Source: Stacks Tag 03DA (auxiliary; not a blueprint node). -/
@[reducible] noncomputable def WeilConjectures.integralOperationsForgetSheaf
    {C : Type uForget} [Category.{vForget} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose WeilConjectures.integralOperationsRingForget.{wForget}] :
    Sheaf J CommRingCat.{wForget} ⥤ Sheaf J RingCat.{wForget} :=
  sheafCompose J WeilConjectures.integralOperationsRingForget

/-- Evaluation of a module-sheaf morphism, with the section coercions recorded once.
Source: Stacks Tag 03DA (auxiliary; not a blueprint node). -/
@[reducible] def WeilConjectures.integralOperationsSectionApply
    {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{r}} {M N : SheafOfModules.{r} R}
    (φ : M ⟶ N) (U : Cᵒᵖ) : M.val.obj U → N.val.obj U :=
  fun x ↦ φ.val.app U x

/-- Evaluation of a chain map, sharing the component and carrier coercions.
Source: Stacks Tag 012Z (auxiliary; not a blueprint node). -/
@[reducible] def WeilConjectures.integralOperationsComplexSectionApply
    {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{r}}
    {K L : CochainComplex (SheafOfModules.{r} R) ℤ}
    (φ : K ⟶ L) (n : ℤ) (U : Cᵒᵖ) : (K.X n).val.obj U → (L.X n).val.obj U :=
  fun x ↦ (φ.f n).val.app U x

/-- Evaluation of a natural chain map, sharing its object and component types.
Source: Stacks Tag 012Z (auxiliary; not a blueprint node). -/
@[reducible] def WeilConjectures.integralOperationsNaturalSectionApply
    {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{r}} {D : Type c} [Category.{d} D]
    {F G : D ⥤ CochainComplex (SheafOfModules.{r} R) ℤ}
    (φ : F ⟶ G) (P : D) (n : ℤ) (U : Cᵒᵖ) :
    ((F.obj P).X n).val.obj U → ((G.obj P).X n).val.obj U :=
  fun x ↦ ((φ.app P).f n).val.app U x

open WeilConjectures

/-- Scalar restriction preserves zero morphisms.
Source: Stacks Tag 03CY (auxiliary; not a blueprint node). -/
theorem SheafOfModules.integralOperationsRestrictScalarsZero
    {C : Type c} [Category.{d} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{r}} (q : R ⟶ S) :
    (SheafOfModules.restrictScalars.{r} q).PreservesZeroMorphisms :=
  @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
    (inferInstanceAs (SheafOfModules.restrictScalars.{r} q).Additive)

attribute [local instance 2000] SheafOfModules.integralOperationsRestrictScalarsZero

/-- Termwise coefficient restriction, with its complex functor data recorded once.
Source: Stacks Tag 03CY (auxiliary; not a blueprint node). -/
noncomputable def WeilConjectures.integralOperationsRestrictionComplex
    {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{r}} (f : R ⟶ S) :
    CochainComplex (SheafOfModules.{r} S) ℤ ⥤
      CochainComplex (SheafOfModules.{r} R) ℤ :=
  (SheafOfModules.restrictScalars f).mapHomologicalComplex (.up ℤ)

private theorem constantMap_surjective
    {C : Type c} [Category.{d} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J CommRingCat.{r}] [J.WEqualsLocallyBijective CommRingCat.{r}]
    {A B : CommRingCat.{r}} (q : A ⟶ B) (hq : Function.Surjective q) :
    Presheaf.IsLocallySurjective J ((constantSheaf J CommRingCat.{r}).map q).hom := by
  let k := (Functor.const Cᵒᵖ).map q
  have : Presheaf.IsLocallySurjective J k :=
    Presheaf.isLocallySurjective_of_surjective J k (fun _ ↦ hq)
  have h := (sheafificationAdjunction J CommRingCat.{r}).unit.naturality k
  apply Presheaf.isLocallySurjective_of_isLocallySurjective_fac J
    (f₁ := toSheafify J ((Functor.const Cᵒᵖ).obj A))
    (f₃ := k ≫ toSheafify J ((Functor.const Cᵒᵖ).obj B))
  exact h.symm

namespace AlgebraicGeometry.Scheme
attribute [local irreducible] coefficientProEtaleDirectRingMap
private theorem directRingMap_naturality {X Y : Scheme.{t}} (f : X ⟶ Y)
    {A B : CommRingCat.{max r (t + 1)}} (q : A ⟶ B) :
    (constantSheaf (ProEt.topology Y) CommRingCat.{max r (t + 1)}).map q ≫
        coefficientProEtaleDirectRingMap.{t, r} f B =
      coefficientProEtaleDirectRingMap.{t,r} f A ≫
        ((proEtaleBaseChange f).sheafPushforwardContinuous CommRingCat.{max r (t + 1)}
          (ProEt.topology Y) (ProEt.topology X)).map
            ((constantSheaf (ProEt.topology X) CommRingCat.{max r (t + 1)}).map q) := by
  apply ((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{max r (t + 1)}).homEquiv
    ((Functor.const Y.ProEtᵒᵖ).obj A) _).injective
  change (sheafificationAdjunction (ProEt.topology Y) CommRingCat.{max r (t + 1)}).homEquiv _ _
    ((presheafToSheaf (ProEt.topology Y) CommRingCat.{max r (t + 1)}).map
      ((Functor.const _).map q) ≫ _) = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  unfold coefficientProEtaleDirectRingMap
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext V
  exact congrArg (fun z ↦ z.app ((proEtaleBaseChange f).op.obj V))
    ((sheafificationAdjunction (ProEt.topology X) CommRingCat.{max r (t + 1)}).unit.naturality
      ((Functor.const _).map q))
end AlgebraicGeometry.Scheme

attribute [local irreducible] constantSheaf HasDerivedCategory.standard limit

namespace SheafOfModules.IntegralScalarProof
variable {C : Type c} [Category.{d} C] {J : GrothendieckTopology C}
  {S T : Sheaf J RingCat.{r}} (q : S ⟶ T)
  (M : SheafOfModules.{r} S) (N : SheafOfModules.{r} T)

private noncomputable def retypeMap
    (φ : (toSheaf S).obj M ⟶ (toSheaf T).obj N)
    (hφ : ∀ (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U),
      φ.hom.app U (s • x) = q.hom.app U s •
        (show N.val.obj U from φ.hom.app U x)) :
    M ⟶ (restrictScalars q).obj N where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        (X := M.val.obj U) (Y := ((restrictScalars q).obj N).val.obj U)
        { toFun := φ.hom.app U
          map_add' := _root_.map_add _
          map_smul' := hφ U }
      naturality := by
        intro U V a
        ext x
        exact CategoryTheory.congr_fun (φ.hom.naturality a) x }

section Composition

variable {C : Type c} [Category.{d} C] {J : GrothendieckTopology C}
  {R S T : Sheaf J RingCat.{r}} (f : R ⟶ S) (g : R ⟶ T) (q : S ⟶ T)
  (hq : f ≫ q = g) (M : SheafOfModules.{r} S) (N : SheafOfModules.{r} T)
include hq in
private theorem coefficient_comp (U : Cᵒᵖ) (s : R.obj.obj U) :
    q.hom.app U (f.hom.app U s) = g.hom.app U s :=
  ConcreteCategory.congr_hom (congrArg (fun k ↦ k.hom.app U) hq) s
private noncomputable def restrictMap (φ : M ⟶ (restrictScalars q).obj N) :
    (restrictScalars f).obj M ⟶ (restrictScalars g).obj N where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        (X := ((restrictScalars f).obj M).val.obj U)
        (Y := ((restrictScalars g).obj N).val.obj U)
        { toFun := φ.val.app U
          map_add' := _root_.map_add _
          map_smul' := fun s x ↦ by
            change φ.val.app U (f.hom.app U s • (show M.val.obj U from x)) =
              g.hom.app U s • (show N.val.obj U from φ.val.app U x)
            have h := (φ.val.app U).hom.map_smul (f.hom.app U s) (show M.val.obj U from x)
            change φ.val.app U (f.hom.app U s • (show M.val.obj U from x)) =
              q.hom.app U (f.hom.app U s) • (show N.val.obj U from φ.val.app U x) at h
            rw [coefficient_comp f g q hq] at h
            exact h }
      naturality := by
        intro U V a
        ext x
        exact PresheafOfModules.naturality_apply φ.val a x }
private noncomputable def liftMap [Presheaf.IsLocallySurjective J f.hom]
    (φ : (restrictScalars f).obj M ⟶ (restrictScalars g).obj N) :
    M ⟶ (restrictScalars q).obj N := by
  let φ' : (restrictScalars f).obj M ⟶
      (restrictScalars f).obj ((restrictScalars q).obj N) :=
    { val :=
        { app := fun U ↦ ModuleCat.ofHom
            (X := ((restrictScalars f).obj M).val.obj U)
            (Y := ((restrictScalars f).obj ((restrictScalars q).obj N)).val.obj U)
            { toFun := φ.val.app U
              map_add' := _root_.map_add _
              map_smul' := fun s x ↦ by
                have h := (φ.val.app U).hom.map_smul s x
                change φ.val.app U (f.hom.app U s • (show M.val.obj U from x)) =
                  q.hom.app U (f.hom.app U s) •
                    (show N.val.obj U from φ.val.app U x)
                rw [coefficient_comp f g q hq]
                exact h }
          naturality := by
            intro U V a
            ext x
            exact PresheafOfModules.naturality_apply φ.val a x } }
  exact ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective f.hom N.isSheaf).symm
    φ'.val⟩
private noncomputable def restrictComplexMap
    {P : CochainComplex (SheafOfModules.{r} S) ℤ}
    {Q : CochainComplex (SheafOfModules.{r} T) ℤ}
    (φ : P ⟶ (WeilConjectures.integralOperationsRestrictionComplex q).obj Q) :
    (WeilConjectures.integralOperationsRestrictionComplex f).obj P ⟶
      (WeilConjectures.integralOperationsRestrictionComplex g).obj Q where
  f j := restrictMap f g q hq (P.X j) (Q.X j) (φ.f j)
  comm' i j _ := by
    ext U x
    exact congrArg (fun k ↦ k.val.app U x) (φ.comm i j)

private theorem restrictComplexMap_naturality
    {P P' : CochainComplex (SheafOfModules.{r} S) ℤ}
    {Q Q' : CochainComplex (SheafOfModules.{r} T) ℤ}
    (a : P ⟶ (WeilConjectures.integralOperationsRestrictionComplex q).obj Q)
    (b : P' ⟶ (WeilConjectures.integralOperationsRestrictionComplex q).obj Q')
    (u : P ⟶ P') (v : Q ⟶ Q')
    (h : u ≫ b = a ≫ (WeilConjectures.integralOperationsRestrictionComplex q).map v) :
    (WeilConjectures.integralOperationsRestrictionComplex f).map u ≫
        restrictComplexMap f g q hq b =
      restrictComplexMap f g q hq a ≫
        (WeilConjectures.integralOperationsRestrictionComplex g).map v := by
  apply HomologicalComplex.hom_ext
  intro i
  ext U x
  exact congrArg (fun z ↦ (z.f i).val.app U x) h

end Composition

end SheafOfModules.IntegralScalarProof

namespace SheafOfModules.IntegralPullbackProof
variable {C : Type c} [Category.{d} C] {D : Type c'} [Category.{d'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (F : C ⥤ D) [F.IsContinuous J K]
  {R₀ R₁ : Sheaf K RingCat.{r}} {S₀ S₁ : Sheaf J RingCat.{r}}
  (qR : R₀ ⟶ R₁) (qS : S₀ ⟶ S₁)
  (φ₀ : S₀ ⟶ (F.sheafPushforwardContinuous RingCat.{r} J K).obj R₀)
  (φ₁ : S₁ ⟶ (F.sheafPushforwardContinuous RingCat.{r} J K).obj R₁)
  (h : qS ≫ φ₁ = φ₀ ≫ (F.sheafPushforwardContinuous RingCat.{r} J K).map qR)
private noncomputable def pushRestrictionIso :
    restrictScalars.{r} qR ⋙ pushforward φ₀ ≅
      pushforward φ₁ ⋙ restrictScalars qS :=
  pushforwardComp (G := 𝟭 D) φ₀ qR ≪≫ pushforwardCongr h.symm ≪≫
    (pushforwardComp (F := 𝟭 C) qS φ₁).symm
private theorem pushRestrictionIso_apply (N : SheafOfModules.{r} R₁)
    (U : Cᵒᵖ) (x : N.val.obj (F.op.obj U)) :
    (integralOperationsSectionApply ((pushRestrictionIso F qR qS φ₀ φ₁ h).inv.app N) U) x = x := by
  rfl
end SheafOfModules.IntegralPullbackProof

namespace IntegralMateProof
variable {A : Type a} [Category.{a'} A] {B : Type b} [Category.{b'} B]
  {C : Type c} [Category.{c'} C] {D : Type d} [Category.{d'} D]
  {L : A ⥤ B} {G : B ⥤ A} {L' : C ⥤ D} {G' : D ⥤ C}
  (adj : L ⊣ G) (adj' : L' ⊣ G') (U : C ⥤ A) (V : D ⥤ B)
  (e : V ⋙ G ≅ G' ⋙ U)
private def mate {M : A} {N : C} (f : M ⟶ U.obj N) : L.obj M ⟶ V.obj (L'.obj N) :=
  (adj.homEquiv _ _).symm (f ≫ U.map (adj'.unit.app N) ≫ e.inv.app (L'.obj N))
private theorem mate_unit {M : A} {N : C} (f : M ⟶ U.obj N) :
    adj.unit.app M ≫ G.map (mate adj adj' U V e f) =
      f ≫ U.map (adj'.unit.app N) ≫ e.inv.app (L'.obj N) := by
  exact (adj.homEquiv_unit _ _ _).symm.trans ((adj.homEquiv _ _).apply_symm_apply _)
private theorem mate_naturality {M₀ M₁ : A} {N₀ N₁ : C}
    (f₀ : M₀ ⟶ U.obj N₀) (f₁ : M₁ ⟶ U.obj N₁)
    (a : M₀ ⟶ M₁) (b : N₀ ⟶ N₁) (h : a ≫ f₁ = f₀ ≫ U.map b) :
    L.map a ≫ mate adj adj' U V e f₁ =
      mate adj adj' U V e f₀ ≫ V.map (L'.map b) := by
  apply adj.homEquiv_naturality_right_square
  have hu : b ≫ adj'.unit.app N₁ = adj'.unit.app N₀ ≫ G'.map (L'.map b) :=
    adj'.unit.naturality b
  have he : e.inv.app (L'.obj N₀) ≫ G.map (V.map (L'.map b)) =
      U.map (G'.map (L'.map b)) ≫ e.inv.app (L'.obj N₁) :=
    (e.inv.naturality (L'.map b)).symm
  calc
    a ≫ (f₁ ≫ U.map (adj'.unit.app N₁) ≫ e.inv.app (L'.obj N₁)) =
        (a ≫ f₁) ≫ U.map (adj'.unit.app N₁) ≫ e.inv.app (L'.obj N₁) :=
      (Category.assoc a f₁ _).symm
    _ = (f₀ ≫ U.map b) ≫ U.map (adj'.unit.app N₁) ≫ e.inv.app (L'.obj N₁) :=
      congrArg (fun z ↦ z ≫ U.map (adj'.unit.app N₁) ≫ e.inv.app (L'.obj N₁)) h
    _ = f₀ ≫ U.map (b ≫ adj'.unit.app N₁) ≫ e.inv.app (L'.obj N₁) := by
      simp only [U.map_comp, Category.assoc]
    _ = f₀ ≫ U.map (adj'.unit.app N₀ ≫ G'.map (L'.map b)) ≫
        e.inv.app (L'.obj N₁) := congrArg
      (fun z ↦ f₀ ≫ U.map z ≫ e.inv.app (L'.obj N₁)) hu
    _ = (f₀ ≫ U.map (adj'.unit.app N₀) ≫ e.inv.app (L'.obj N₀)) ≫
        G.map (V.map (L'.map b)) := by
      simp only [U.map_comp, Category.assoc]
      rw [he]
end IntegralMateProof

namespace SheafOfModules.IntegralPullbackProof
variable {C : Type c} [Category.{d} C] {D : Type c'} [Category.{d'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (F : C ⥤ D) [F.IsContinuous J K]
  {R₀ R₁ : Sheaf K RingCat.{r}} {S₀ S₁ : Sheaf J RingCat.{r}}
  (qR : R₀ ⟶ R₁) (qS : S₀ ⟶ S₁)
  (φ₀ : S₀ ⟶ (F.sheafPushforwardContinuous RingCat.{r} J K).obj R₀)
  (φ₁ : S₁ ⟶ (F.sheafPushforwardContinuous RingCat.{r} J K).obj R₁)
  (h : qS ≫ φ₁ = φ₀ ≫ (F.sheafPushforwardContinuous RingCat.{r} J K).map qR)
  {L₀ : SheafOfModules.{r} S₀ ⥤ SheafOfModules.{r} R₀}
  {L₁ : SheafOfModules.{r} S₁ ⥤ SheafOfModules.{r} R₁}
  (adj₀ : L₀ ⊣ pushforward φ₀) (adj₁ : L₁ ⊣ pushforward φ₁)

/-- A section of the pullback generated by the adjunction unit.
Source: Stacks Tag 03D2 (auxiliary; not a blueprint node). -/
private noncomputable def unitSection (M : SheafOfModules.{r} S₀) (U : Cᵒᵖ)
    (x : M.val.obj U) : (L₀.obj M).val.obj (F.op.obj U) :=
  ((adj₀.unit.app M).val.app U) x

private theorem mate_generator {M : SheafOfModules.{r} S₀} {N : SheafOfModules.{r} S₁}
    (a : M ⟶ (restrictScalars qS).obj N) (U : Cᵒᵖ) (x : M.val.obj U) :
    (integralOperationsSectionApply (IntegralMateProof.mate adj₀ adj₁ (restrictScalars qS)
      (restrictScalars qR)
      (pushRestrictionIso F qR qS φ₀ φ₁ h) a) (F.op.obj U))
        ((integralOperationsSectionApply (adj₀.unit.app M) U) x) =
      (integralOperationsSectionApply (adj₁.unit.app N) U) ((integralOperationsSectionApply a U)
        x) := by
  have he := congrArg (fun k ↦ k.val.app U x)
    (IntegralMateProof.mate_unit adj₀ adj₁ (restrictScalars qS) (restrictScalars qR)
      (pushRestrictionIso F qR qS φ₀ φ₁ h) a)
  exact he.trans (pushRestrictionIso_apply F qR qS φ₀ φ₁ h (L₁.obj N) U
    ((adj₁.unit.app N).val.app U (a.val.app U x)))
private noncomputable def mateData {M : SheafOfModules.{r} S₀} {N : SheafOfModules.{r} S₁}
    (a : M ⟶ (restrictScalars qS).obj N) :
    L₀.obj M ⟶ (restrictScalars qR).obj (L₁.obj N) :=
  IntegralMateProof.mate adj₀ adj₁ (restrictScalars qS) (restrictScalars qR)
    (pushRestrictionIso F qR qS φ₀ φ₁ h) a

private theorem mateData_unit_formula
    {M : SheafOfModules.{r} S₀} {N : SheafOfModules.{r} S₁}
    (a : M ⟶ (restrictScalars qS).obj N) (U : Cᵒᵖ) (x : M.val.obj U) :
    (integralOperationsSectionApply (mateData F qR qS φ₀ φ₁ h adj₀ adj₁ a) (F.op.obj U))
        (unitSection F φ₀ adj₀ M U x) =
      unitSection F φ₁ adj₁ N U ((integralOperationsSectionApply a U) x) := by
  exact mate_generator F qR qS φ₀ φ₁ h adj₀ adj₁ a U x

private theorem mateData_naturality
    {M M' : SheafOfModules.{r} S₀} {N N' : SheafOfModules.{r} S₁}
    (a : M ⟶ (restrictScalars qS).obj N) (b : M' ⟶ (restrictScalars qS).obj N')
    (u : M ⟶ M') (v : N ⟶ N') (hab : u ≫ b = a ≫ (restrictScalars qS).map v) :
    L₀.map u ≫ (mateData F qR qS φ₀ φ₁ h adj₀ adj₁ b) =
      (mateData F qR qS φ₀ φ₁ h adj₀ adj₁ a) ≫ (restrictScalars qR).map (L₁.map v) :=
  IntegralMateProof.mate_naturality adj₀ adj₁ (restrictScalars qS) (restrictScalars qR)
    (pushRestrictionIso F qR qS φ₀ φ₁ h) a b u v hab

private theorem restricted_hom_ext
    {R : Sheaf K RingCat.{r}} (π₀ : R ⟶ R₀) (π₁ : R ⟶ R₁)
    (hπ : π₀ ≫ qR = π₁) [Presheaf.IsLocallySurjective K π₀.hom]
    (M : SheafOfModules.{r} S₀) (N : SheafOfModules.{r} R₁)
    (a b : (restrictScalars π₀).obj (L₀.obj M) ⟶ (restrictScalars π₁).obj N)
    (hab : ∀ (U : Cᵒᵖ) (x : M.val.obj U),
      (integralOperationsSectionApply a (F.op.obj U)) (unitSection F φ₀ adj₀ M U x) =
        (integralOperationsSectionApply b (F.op.obj U)) (unitSection F φ₀ adj₀ M U x)) : a = b := by
  let lift := IntegralScalarProof.liftMap π₀ π₁ qR hπ (L₀.obj M) N
  have he : lift a = lift b := by
    apply (adj₀.homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    ext U x
    exact hab U x
  ext U x
  exact congrArg (fun k ↦ k.val.app U x) he

end SheafOfModules.IntegralPullbackProof

attribute [local irreducible] SheafOfModules.tensorObjIsoSheafification
  SheafOfModules.IntegralPullbackProof.mateData
  SheafOfModules.IntegralPullbackProof.pushRestrictionIso
  IntegralMateProof.mate

private theorem integralHasMap
    {A : Type a} [Category.{b} A] [Preadditive A] [MonoidalCategory A]
    [(MonoidalCategory.curriedTensor A).PreservesZeroMorphisms]
    [∀ M : A, ((MonoidalCategory.curriedTensor A).obj M).PreservesZeroMorphisms]
    [HasCountableCoproducts A] (P Q : CochainComplex A ℤ) :
    HomologicalComplex.HasMapBifunctor P Q
      (MonoidalCategory.curriedTensor A) (.up ℤ) := by
  infer_instance

private theorem scalarRestrictionAdditive
    {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{r}} (α : R ⟶ S) :
    (SheafOfModules.restrictScalars.{r} α).Additive := by
  infer_instance

namespace WeilConjectures

/-- Signed total tensor followed by a zero-preserving coefficient functor.
Source: Stacks Tags 012Z and 07A4
(auxiliary; not a blueprint node). -/
noncomputable def integralOperationsTensorComposite
    {D : Type a} [Category.{b} D] {A : Type c} [Category.{d} A]
    [Preadditive A] [MonoidalCategory A]
    [(MonoidalCategory.curriedTensor A).PreservesZeroMorphisms]
    [∀ X : A, ((MonoidalCategory.curriedTensor A).obj X).PreservesZeroMorphisms]
    [∀ P Q : CochainComplex A ℤ, HomologicalComplex.HasMapBifunctor P Q
      (MonoidalCategory.curriedTensor A) (.up ℤ)]
    {B : Type a'} [Category.{b'} B] [HasZeroMorphisms B]
    (F : D ⥤ CochainComplex A ℤ) (R : A ⥤ B) [R.PreservesZeroMorphisms] :
    D × D ⥤ CochainComplex B ℤ :=
  F.prod F ⋙ Functor.uncurry.obj
    (MonoidalCategory.curriedTensor A).map₂CochainComplex ⋙
      R.mapHomologicalComplex (.up ℤ)

section PrivateTensorTransition
attribute [local semireducible] constantSheaf HasDerivedCategory.standard limit
  SheafOfModules.tensorObjIsoSheafification
attribute [-instance] SheafOfModules.integralOperationsRestrictScalarsZero
set_option backward.isDefEq.respectTransparency true
attribute [local instance 2001] scalarRestrictionAdditive
attribute [local instance] CategoryTheory.CochainPullback.RingedPullback.additive
  CategoryTheory.CochainPullback.CoefficientSquare.additive'
  CategoryTheory.CochainPullback.StrictCoefficient.Diagram.additive
  CategoryTheory.CochainPullback.extensionFunctorAdditive
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local instance 2001] integralHasMap
attribute [local instance 3001]
  CategoryTheory.CochainPullback.StrictCoefficient.ScalarCalculation.tensorCoproducts
  CategoryTheory.CochainPullback.StrictCoefficient.ScalarCalculation.hasTensorTotal

universe v u' v'

namespace TensorTotalProof
open MonoidalCategory
variable {C : Type a} [Category.{b} C] [Preadditive C] [MonoidalCategory C]
  [(curriedTensor C).PreservesZeroMorphisms]
  [∀ X : C, ((curriedTensor C).obj X).PreservesZeroMorphisms]
  {P Q A B : CochainComplex C ℤ}
private theorem totalTensor_map
    (a : P ⟶ A) (b : Q ⟶ B)
    [∀ (K L : CochainComplex C ℤ),
      HomologicalComplex.HasMapBifunctor K L (curriedTensor C) (.up ℤ)] :
    (Functor.uncurry.obj (curriedTensor C).map₂CochainComplex).map
      (X := (P, Q)) (Y := (A, B)) (a, b) =
      HomologicalComplex.mapBifunctorMap a b (curriedTensor C) (.up ℤ) := by
  change HomologicalComplex.mapBifunctorMap a (𝟙 Q) _ _ ≫
    HomologicalComplex.mapBifunctorMap (𝟙 A) b _ _ = _
  simp [HomologicalComplex.mapBifunctorMap, ← HomologicalComplex₂.total.map_comp]

private theorem composite_map
    {D : Type a'} [Category.{b'} D] {B : Type c} [Category.{d} B]
    [HasZeroMorphisms B] (F : D ⥤ CochainComplex C ℤ) (R : C ⥤ B)
    [R.PreservesZeroMorphisms]
    [∀ (K L : CochainComplex C ℤ),
      HomologicalComplex.HasMapBifunctor K L (curriedTensor C) (.up ℤ)]
    {K L : D × D} (u : K ⟶ L) :
    (integralOperationsTensorComposite F R).map u =
      (R.mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.mapBifunctorMap (F.map u.1) (F.map u.2)
          (curriedTensor C) (.up ℤ)) := by
  exact congrArg (R.mapHomologicalComplex (.up ℤ)).map
    (totalTensor_map (F.map u.1) (F.map u.2))

end TensorTotalProof

section SignedTensorConstruction

set_option backward.isDefEq.respectTransparency true

set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] SheafOfModules.monoidalCategory
  PresheafOfModules.sheafificationAdjunction

open MonoidalCategory

variable (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ)

section GenericTensor

set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] SheafOfModules.monoidalCategory

@[no_expose] private noncomputable def pureTensor
    {C : Type a} [Category.{b} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose WeilConjectures.integralOperationsRingForget.{r}]
    (R : Sheaf J CommRingCat.{r})
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasWeakSheafify J AddCommGrpCat.{r}]
    (M N : SheafOfModules.{r} ((integralOperationsForgetSheaf.{r} J).obj R))
    (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    (M ⊗ N).val.obj U :=
  (SheafOfModules.tensorObjIsoSheafification (R := R) M N).inv.val.app U
    ((toSheafify J (M.val ⊗ N.val).presheaf).app U (x ⊗ₜ[R.obj.obj U] y))

/-- The common pure section is the image of the sheafification unit.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
private theorem moduleTmul_eq
    {C : Type a} [Category.{b} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose WeilConjectures.integralOperationsRingForget.{r}]
    (R : Sheaf J CommRingCat.{r})
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasWeakSheafify J AddCommGrpCat.{r}]
    (M N : SheafOfModules.{r} ((integralOperationsForgetSheaf.{r} J).obj R))
    (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    CochainPullback.moduleTmul (R := R) M N U x y =
    pureTensor R M N U x y := by
  exact congrArg (fun f ↦
    (SheafOfModules.tensorObjIsoSheafification (R := R) M N).inv.val.app U
      (f.app U (x ⊗ₜ[R.obj.obj U] y)))
    (PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app
      (R := (integralOperationsForgetSheaf.{r} J).obj R)
      (𝟙 _) (M.val ⊗ N.val))

/-- Maps from the sheaf tensor are determined by the common local pure sections.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
private theorem moduleTmul_hom_ext
    {C : Type a} [Category.{b} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose WeilConjectures.integralOperationsRingForget.{r}]
    (R : Sheaf J CommRingCat.{r})
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasWeakSheafify J AddCommGrpCat.{r}]
    (M N Z : SheafOfModules.{r} ((integralOperationsForgetSheaf.{r} J).obj R))
    (φ ψ : M ⊗ N ⟶ Z)
    (h : ∀ U (x : M.val.obj U) (y : N.val.obj U),
      (integralOperationsSectionApply φ U) (pureTensor R M N U x y) =
      (integralOperationsSectionApply ψ U) (pureTensor R M N U x y)) : φ = ψ := by
  apply CochainPullback.StrictCoefficient.ScalarCalculation.tensor_hom_ext M N Z
  intro U x y
  change φ.val.app U (CochainPullback.moduleTmul (R := R) M N U x y) =
    ψ.val.app U (CochainPullback.moduleTmul (R := R) M N U x y)
  simpa only [moduleTmul_eq] using h U x y

-- Explicit section maps avoid comparing the two coefficient-ring constructions in coercions.
private def forgetRestriction
    {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{r}} (α : R ⟶ S)
    (M : SheafOfModules.{r} S) (U : Cᵒᵖ) :
    ((SheafOfModules.restrictScalars α).obj M).val.obj U → M.val.obj U := id

private def intoRestriction
    {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{r}} (α : R ⟶ S)
    (M : SheafOfModules.{r} S) (U : Cᵒᵖ) :
    M.val.obj U → ((SheafOfModules.restrictScalars α).obj M).val.obj U := id

private theorem forgetRestriction_injective
    {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{r}} (α : R ⟶ S)
    (M : SheafOfModules.{r} S) (U : Cᵒᵖ) :
    Function.Injective (forgetRestriction α M U) := fun _ _ h ↦ h

private theorem liftMap_section
    {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat.{r}} (f : R ⟶ S) (g : R ⟶ T) (q : S ⟶ T)
    (hq : f ≫ q = g) [Presheaf.IsLocallySurjective J f.hom]
    (M : SheafOfModules.{r} S) (N : SheafOfModules.{r} T)
    (φ : (SheafOfModules.restrictScalars f).obj M ⟶
      (SheafOfModules.restrictScalars g).obj N) (U : Cᵒᵖ) (x : M.val.obj U) :
    forgetRestriction q N U
      ((integralOperationsSectionApply (SheafOfModules.IntegralScalarProof.liftMap f g q hq M N
        φ) U) x) =
      forgetRestriction g N U ((integralOperationsSectionApply φ U) (intoRestriction f M U x)) := by
  exact rfl

private theorem liftMap_injective
    {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat.{r}} (f : R ⟶ S) (g : R ⟶ T) (q : S ⟶ T)
    (hq : f ≫ q = g) [Presheaf.IsLocallySurjective J f.hom]
    (M : SheafOfModules.{r} S) (N : SheafOfModules.{r} T) :
    Function.Injective (SheafOfModules.IntegralScalarProof.liftMap f g q hq M N) := by
  intro φ ψ h
  ext U x
  exact congrArg (fun k ↦ k.val.app U x) h

private theorem restrictComplexMap_section
    {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat.{r}} (f : R ⟶ S) (g : R ⟶ T) (q : S ⟶ T)
    (hq : f ≫ q = g) {P : CochainComplex (SheafOfModules.{r} S) ℤ}
    {Q : CochainComplex (SheafOfModules.{r} T) ℤ}
    (φ : P ⟶ (WeilConjectures.integralOperationsRestrictionComplex q).obj Q)
    (j : ℤ) (U : Cᵒᵖ) (x : (P.X j).val.obj U) :
    forgetRestriction g (Q.X j) U
      ((integralOperationsComplexSectionApply
        (SheafOfModules.IntegralScalarProof.restrictComplexMap f g q hq φ) j U)
        (intoRestriction f (P.X j) U x)) =
      forgetRestriction q (Q.X j) U ((integralOperationsComplexSectionApply φ j U) x) := by
  rfl

end GenericTensor

attribute [local instance]
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

namespace TensorChainProof
open CategoryTheory.CochainPullback
open CategoryTheory.CochainPullback.StrictCoefficient
open CategoryTheory.CochainPullback.StrictCoefficient.ScalarCalculation
attribute [local instance 2000] SheafOfModules.cochainModulesSymmetric
  SheafOfModules.cochainModulesPreadditive
  SheafOfModules.cochainTensorLeftPreservesColimits
  SheafOfModules.cochainTensorRightPreservesColimits
  SheafOfModules.cochainModulesMonoidal
  GrothendieckTopology.hasSheafify_of_essentiallySmall
variable {C : Type a} [Category.{b} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose WeilConjectures.integralOperationsRingForget.{r}]
  (R S : Sheaf J CommRingCat.{r}) (α : R ⟶ S)

attribute [local instance] HomologicalComplex.monoidalCategoryStruct
  HomologicalComplex.monoidalCategory

private theorem totalMap_eq {A : Sheaf J CommRingCat.{r}}
    {P Q X Y : Complex A} (f : P ⟶ X) (g : Q ⟶ Y) :
    tensorTotalMap f g =
      HomologicalComplex.mapBifunctorMap f g (curriedTensor (Modules A)) (.up ℤ) := rfl

@[no_expose] private noncomputable def chainAdjunction :=
  (extensionAdjunction α).mapHomologicalComplex (.up ℤ)

@[no_expose] private noncomputable def transpose {K : Complex R} {L : Complex S}
    (f : K ⟶ (restrictComplex α).obj L) : (extend α).obj K ⟶ L :=
  (chainAdjunction R S α).homEquiv K L |>.symm <| f

private theorem transpose_section {K : Complex R} {L : Complex S}
    (f : K ⟶ (restrictComplex α).obj L) (p : ℤ) (U : Cᵒᵖ) (x : (K.X p).val.obj U) :
    ((transpose R S α f).f p).val.app U
      (extensionTmul α (K.X p) U 1 x) = (f.f p).val.app U x := by
  have h := congrArg (fun z ↦ (z.f p).val.app U x)
    ((chainAdjunction R S α).homEquiv K L
      |>.apply_symm_apply f)
  rw [Adjunction.homEquiv_unit] at h
  change ((transpose R S α f).f p).val.app U
    (((extensionAdjunction α).unit.app (K.X p)).val.app U x) = _ at h
  rw [KappaCalculation.extension_unit] at h
  exact h

@[no_expose] private noncomputable def map
    {P Q : CochainPullback.Complex R} {P' Q' : CochainPullback.Complex S}
    (a : P ⟶ (restrictComplex α).obj P')
    (b : Q ⟶ (restrictComplex α).obj Q') :
    total P Q ⟶ (restrictComplex α).obj (total P' Q') :=
  (chainAdjunction R S α).unit.app (total P Q) ≫
    (restrictComplex α).map
      ((tensorComparison (extensionPullback α) (extensionComparison α) P Q).hom ≫
        tensorTotalMap (transpose R S α a) (transpose R S α b))

private theorem totalPure_eq {P Q : CochainPullback.Complex R}
    (p q : ℤ) (U : Cᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    totalPure P Q p q (p+q) rfl U x y =
      (integralOperationsSectionApply (tensorι (A := R) P Q p q (p+q) rfl) U)
        (pureTensor R (P.X p) (Q.X q) U x y)  := by
  exact congrArg (integralOperationsSectionApply
    (tensorι (A := R) P Q p q (p + q) rfl) U)
    (moduleTmul_eq R (P.X p) (Q.X q) U x y)

private theorem pure
    {P Q : CochainPullback.Complex R} {P' Q' : CochainPullback.Complex S}
    (a : P ⟶ (restrictComplex α).obj P')
    (b : Q ⟶ (restrictComplex α).obj Q') (p q : ℤ) (U : Cᵒᵖ) (x : (P.X p).val.obj U)
    (y : (Q.X q).val.obj U) :
    ((map R S α a b).f (p+q)).val.app U
      (totalPure P Q p q (p+q) rfl U x y) =
    totalPure P' Q' p q (p+q) rfl U
      ((a.f p).val.app U x) ((b.f q).val.app U y) := by
  change ((tensorTotalMap (transpose R S α a) (transpose R S α b)).f (p+q)).val.app U
    (((tensorComparison (extensionPullback α) (extensionComparison α) P Q).hom.f
      (p+q)).val.app U
      (((extensionAdjunction α).unit.app ((total P Q).X (p+q))).val.app U
        (totalPure P Q p q (p+q) rfl U x y))) = _
  rw [KappaCalculation.extension_unit, scalarTotal_hom, totalMap_pure,
    transpose_section, transpose_section]
attribute [local irreducible] map transpose
private theorem map_naturality
    {P Q X Y : Complex R} {P' Q' X' Y' : Complex S}
    (a : P ⟶ (restrictComplex α).obj P')
    (b : Q ⟶ (restrictComplex α).obj Q')
    (a' : X ⟶ (restrictComplex α).obj X')
    (b' : Y ⟶ (restrictComplex α).obj Y')
    (f : P ⟶ X) (g : Q ⟶ Y) (f' : P' ⟶ X') (g' : Q' ⟶ Y')
    (ha : f ≫ a' = a ≫ (restrictComplex α).map f')
    (hb : g ≫ b' = b ≫ (restrictComplex α).map g') :
    tensorTotalMap f g ≫ map R S α a' b' =
      map R S α a b ≫ (restrictComplex α).map (tensorTotalMap f' g') := by
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  apply tensor_hom_ext
  intro U x y
  subst n
  change ((map R S α a' b').f (p+q)).val.app U
    (((tensorTotalMap f g).f (p+q)).val.app U
      (totalPure P Q p q (p+q) rfl U x y)) =
    ((tensorTotalMap f' g').f (p+q)).val.app U
      (((map R S α a b).f (p+q)).val.app U
        (totalPure P Q p q (p+q) rfl U x y))
  rw [totalMap_pure, pure, pure, totalMap_pure]
  exact congrArg₂ (totalPure X' Y' p q (p+q) rfl U)
    (congrArg (fun k ↦ (k.f p).val.app U x) ha)
    (congrArg (fun k ↦ (k.f q).val.app U y) hb)

end TensorChainProof

attribute [local irreducible] TensorChainProof.map TensorChainProof.transpose
  CategoryTheory.CochainPullback.StrictCoefficient.ScalarCalculation.tensorTotalMap
  CategoryTheory.CochainPullback.StrictCoefficient.ScalarCalculation.totalPure

attribute [local instance]
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

attribute [local instance] SheafOfModules.monoidalCategory
  SheafOfModules.isMonoidal_W_independentCoefficients

open CategoryTheory.CochainPullback.StrictCoefficient.ScalarCalculation in
private theorem genericRestrictedTotal_hom_ext
    {C : Type a} [Category.{b} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose WeilConjectures.integralOperationsRingForget.{r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasWeakSheafify J AddCommGrpCat.{r}]
    {R₀ : Sheaf J RingCat.{r}} (S T : Sheaf J CommRingCat.{r})
    (f : R₀ ⟶ (integralOperationsForgetSheaf.{r} J).obj S)
    (g : R₀ ⟶ (integralOperationsForgetSheaf.{r} J).obj T)
    (q₀ : (integralOperationsForgetSheaf.{r} J).obj S ⟶
      (integralOperationsForgetSheaf.{r} J).obj T)
    (hq₀ : f ≫ q₀ = g) [Presheaf.IsLocallySurjective J f.hom]
    (P Q : CochainComplex (SheafOfModules.{r}
      ((integralOperationsForgetSheaf.{r} J).obj S)) ℤ)
    (Z : SheafOfModules.{r}
      ((integralOperationsForgetSheaf.{r} J).obj T)) (j : ℤ)
    (a b : (SheafOfModules.restrictScalars
        f).obj
      ((CategoryTheory.CochainPullback.StrictCoefficient.total P Q).X j) ⟶
        (SheafOfModules.restrictScalars g).obj Z)
    (h : ∀ (p q : ℤ) (hpq : p + q = j) (U : Cᵒᵖ)
      (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
      forgetRestriction g Z U
        ((integralOperationsSectionApply a U) (intoRestriction f
          ((CategoryTheory.CochainPullback.StrictCoefficient.total P Q).X j) U
            ((integralOperationsSectionApply (tensorι (A := S) P Q
              p q j hpq) U)
              (pureTensor S _ _ U x y)))) =
      forgetRestriction g Z U
        ((integralOperationsSectionApply b U) (intoRestriction f
          ((CategoryTheory.CochainPullback.StrictCoefficient.total P Q).X j) U
            ((integralOperationsSectionApply (tensorι (A := S) P Q
              p q j hpq) U)
              (pureTensor S _ _ U x y))))) : a = b := by
  let lift := SheafOfModules.IntegralScalarProof.liftMap
    f g
    q₀ hq₀
    ((CategoryTheory.CochainPullback.StrictCoefficient.total P Q).X j) Z
  have he : lift a = lift b := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    apply moduleTmul_hom_ext S
    intro U x y
    apply forgetRestriction_injective q₀ Z U
    change forgetRestriction q₀ Z U
      ((lift a).val.app U _) =
      forgetRestriction q₀ Z U
        ((lift b).val.app U _)
    exact (liftMap_section f
      g _ hq₀ _ _ a U _).trans
      ((h p q hpq U x y).trans
        (liftMap_section f
          g _ hq₀
          _ _ b U _).symm)
  exact liftMap_injective f
    g _ hq₀ _ _ he

namespace TensorNaturalProof
open CategoryTheory.CochainPullback
open CategoryTheory.CochainPullback.StrictCoefficient
open CategoryTheory.CochainPullback.StrictCoefficient.ScalarCalculation
open MonoidalCategory
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.monoidalCategory
  SheafOfModules.monoidalPreadditive_independent
variable {C : Type a} [Category.{b} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose WeilConjectures.integralOperationsRingForget.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{r}]
  {D : Type c} [Category.{d} D]
  {R₀ : Sheaf J RingCat.{r}} (S T : Sheaf J CommRingCat.{r})
  (f : R₀ ⟶ (integralOperationsForgetSheaf.{r} J).obj S)
  (g : R₀ ⟶ (integralOperationsForgetSheaf.{r} J).obj T)
  (q₀ : S ⟶ T)
  (hq₀ : f ≫ ((integralOperationsForgetSheaf J).map q₀) = g)
  (F : D ⥤ CochainComplex (SheafOfModules.{r}
    ((integralOperationsForgetSheaf.{r} J).obj S)) ℤ)
  (G : D ⥤ CochainComplex (SheafOfModules.{r}
    ((integralOperationsForgetSheaf.{r} J).obj T)) ℤ)
  (θ : F ⟶ G ⋙ integralOperationsRestrictionComplex ((integralOperationsForgetSheaf J).map q₀))

@[no_expose] private noncomputable abbrev level
    (f : R₀ ⟶ (integralOperationsForgetSheaf.{r} J).obj S)
    (F : D ⥤ CochainComplex (SheafOfModules.{r}
      ((integralOperationsForgetSheaf.{r} J).obj S)) ℤ) :
    D × D ⥤ CochainComplex (SheafOfModules.{r} R₀) ℤ :=
  integralOperationsTensorComposite F (SheafOfModules.restrictScalars f)

@[no_expose] private noncomputable def sectionPure
    (F : D ⥤ CochainComplex (SheafOfModules.{r}
      ((integralOperationsForgetSheaf.{r} J).obj S)) ℤ)
    (P Q : D) (p q : ℤ) (U : Cᵒᵖ)
    (x : ((F.obj P).X p).val.obj U) (y : ((F.obj Q).X q).val.obj U) :
    ((total (F.obj P) (F.obj Q)).X (p + q)).val.obj U :=
  (integralOperationsSectionApply
    (tensorι (A := S) (F.obj P) (F.obj Q) p q (p+q) rfl) U)
    (pureTensor S _ _ U x y)

@[no_expose] private noncomputable def component (K : D × D) :
    (level S f F).obj K ⟶
      (level T g G).obj K :=
  SheafOfModules.IntegralScalarProof.restrictComplexMap f g ((integralOperationsForgetSheaf
    J).map q₀) hq₀
    (TensorChainProof.map S T q₀ (θ.app K.1) (θ.app K.2))

private theorem component_pure (P Q : D) (p q : ℤ) (U : Cᵒᵖ)
    (x : ((F.obj P).X p).val.obj U) (y : ((F.obj Q).X q).val.obj U) :
    (integralOperationsComplexSectionApply (component S T f g q₀ hq₀ F G θ (P,Q)) (p+q) U)
        (intoRestriction f _ U (sectionPure S F P Q p q U x y)) =
      intoRestriction g _ U (sectionPure T G P Q p q U
        (forgetRestriction ((integralOperationsForgetSheaf J).map q₀) _ U
          ((integralOperationsComplexSectionApply (θ.app
          P) p U) x))
        (forgetRestriction ((integralOperationsForgetSheaf J).map q₀) _ U
          ((integralOperationsComplexSectionApply (θ.app
          Q) q U) y))) := by
  have h := TensorChainProof.pure S T q₀ (θ.app P) (θ.app Q) p q U x y
  rw [TensorChainProof.totalPure_eq, TensorChainProof.totalPure_eq] at h
  apply forgetRestriction_injective g _ U
  exact (restrictComplexMap_section f g ((integralOperationsForgetSheaf J).map q₀) hq₀
    (TensorChainProof.map S T q₀ (θ.app P) (θ.app Q)) (p+q) U _).trans
      h

private theorem level_map_eq {K L : D × D} (a : K ⟶ L) :
    (level S f F).map a =
      (WeilConjectures.integralOperationsRestrictionComplex f).map
        (tensorTotalMap (F.map a.1) (F.map a.2)) := by
  exact (TensorTotalProof.composite_map F (SheafOfModules.restrictScalars f) a).trans
    (congrArg (WeilConjectures.integralOperationsRestrictionComplex f).map
      (TensorChainProof.totalMap_eq (F.map a.1) (F.map a.2)).symm)

@[no_expose] private noncomputable def candidate [Presheaf.IsLocallySurjective J f.hom] :
    level S f F ⟶ level T g G where
  app := component S T f g q₀ hq₀ F G θ
  naturality {K L} u := by
    rw [level_map_eq, level_map_eq]
    exact SheafOfModules.IntegralScalarProof.restrictComplexMap_naturality f g
      ((integralOperationsForgetSheaf J).map q₀) hq₀
      (TensorChainProof.map S T q₀ (θ.app K.1) (θ.app K.2))
      (TensorChainProof.map S T q₀ (θ.app L.1) (θ.app L.2))
      (tensorTotalMap (F.map u.1) (F.map u.2))
      (tensorTotalMap (G.map u.1) (G.map u.2))
      (TensorChainProof.map_naturality S T q₀ (θ.app K.1) (θ.app K.2)
        (θ.app L.1) (θ.app L.2) (F.map u.1) (F.map u.2) (G.map u.1) (G.map u.2)
        (θ.naturality u.1) (θ.naturality u.2))

attribute [local irreducible] component

include hq₀ in
private theorem existsUnique [hf : Presheaf.IsLocallySurjective J f.hom] :
    ∃! τ : level S f F ⟶ level T g G,
      ∀ (P Q : D) (p q : ℤ) (U : Cᵒᵖ)
        (x : ((F.obj P).X p).val.obj U) (y : ((F.obj Q).X q).val.obj U),
      forgetRestriction g _ U
        ((integralOperationsNaturalSectionApply τ (P,Q) (p+q) U)
          (intoRestriction f _ U (sectionPure S F P Q p q U x y))) =
        sectionPure T G P Q p q U
          (forgetRestriction ((integralOperationsForgetSheaf J).map q₀) _ U
            ((integralOperationsComplexSectionApply (θ.app
            P) p U) x))
          (forgetRestriction ((integralOperationsForgetSheaf J).map q₀) _ U
            ((integralOperationsComplexSectionApply (θ.app
            Q) q U) y)) := by
  refine ⟨candidate S T f g q₀ hq₀ F G θ, ?_, ?_⟩
  · intro P Q p q U x y
    exact congrArg (forgetRestriction g _ U)
      (component_pure S T f g q₀ hq₀ F G θ P Q p q U x y)
  · intro τ hτ
    apply NatTrans.ext
    funext K
    obtain ⟨P,Q⟩ := K
    apply HomologicalComplex.hom_ext
    intro j
    apply genericRestrictedTotal_hom_ext S T f g ((integralOperationsForgetSheaf J).map q₀) hq₀
    intro p q hpq U x y
    subst j
    exact (hτ P Q p q U x y).trans
      (congrArg (forgetRestriction g _ U)
        (component_pure S T f g q₀ hq₀ F G θ P Q p q U x y)).symm

end TensorNaturalProof

end SignedTensorConstruction

end PrivateTensorTransition

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The specified abelian sheafification in the coefficient universe.
Source: Stacks Tag 03DA (auxiliary; not a blueprint node). -/
noncomputable instance (priority := 2000) integralOperationsAbSheafify
    (W : AlgebraicGeometry.Scheme.{t}) :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W) AddCommGrpCat.{max u (t + 1)} :=
  integralCoefficientAbSheafify.{t, u} W

/-- The corresponding locally bijective criterion in exactly the same coefficient size.
Source: Stacks Tag 03DA (auxiliary; not a blueprint node). -/
noncomputable instance (priority := 2000) integralOperationsAbLocallyBijective
    (W : AlgebraicGeometry.Scheme.{t}) :
    (AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective.{t, u} W

/-- The finite module category at positive exponent n+1.
Source: Stacks Tag 06YL (auxiliary; not a blueprint node). -/
noncomputable abbrev integralOperationsFiniteModules (W : AlgebraicGeometry.Scheme.{t})
    (n : ℕ) :=
  SheafOfModules.{max u (t + 1)} (integralCoefficientSheaf l E W n)

/-- The pro-etale site is small relative to the coefficient universe.
Source: Stacks Tag 09A5 (auxiliary; not a blueprint node). -/
noncomputable instance (priority := low) integralOperationsSiteSmall
    (W : AlgebraicGeometry.Scheme.{t}) :
    EssentiallySmall.{max u (t + 1)} W.ProEt := essentiallySmallSelf _

/-- Standard localization for the commutative presentation of the same completed sheaf.
Source: Stacks Tag 05RU (auxiliary; not a blueprint node). -/
noncomputable instance integralOperationsCommHasDerivedCategory
    (W : AlgebraicGeometry.Scheme.{t}) :
    HasDerivedCategory (SheafOfModules.{max u (t + 1)}
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology W)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
          (completedIntegralCommRingSheafUnrestricted l E W))) :=
  HasDerivedCategory.standard _

attribute [local instance 3000] integralTowerHasDerivedCategory

/-- The presheaf tensor structure for the same finite ring, with commutativity retained.
Source: Stacks Tag 03EK (auxiliary; not a blueprint node). -/
noncomputable instance integralOperationsFinitePresheafMonoidal
    (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ) :
    MonoidalCategory (PresheafOfModules.{max u (t + 1)}
      (integralCoefficientSheaf l E W n).obj) :=
  PresheafOfModules.monoidalCategory
    (R := (integralCoefficientCommRingSheaf l E W n).obj)

/-- The recorded sheaf tensor structure on finite coefficients.
Source: Stacks Tag 03EK (auxiliary; not a blueprint node). -/
noncomputable instance integralOperationsFiniteMonoidal (W : AlgebraicGeometry.Scheme.{t})
    (n : ℕ) : MonoidalCategory (integralOperationsFiniteModules l E W n) :=
  letI : EssentiallySmall.{max u (t + 1)} W.ProEt := essentiallySmallSelf _
  letI := integralCoefficientAbSheafify.{t, u} W
  letI := integralCoefficientAbLocallyBijective.{t, u} W
  letI := SheafOfModules.isMonoidal_W_independentCoefficients
    (J := AlgebraicGeometry.Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W n)
  SheafOfModules.monoidalCategory (integralCoefficientCommRingSheaf l E W n)

/-- Tensoring finite sheaves preserves zero maps in the first variable.
Source: Stacks Tag 03EK (auxiliary; not a blueprint node). -/
noncomputable instance integralOperationsFiniteTensorZero
    (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ) :
    (MonoidalCategory.curriedTensor
      (integralOperationsFiniteModules l E W n)).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
    (integralCoefficientCommRingSheaf l E W n)

/-- Tensoring finite sheaves preserves zero maps in the second variable.
Source: Stacks Tag 03EK (auxiliary; not a blueprint node). -/
noncomputable instance integralOperationsFiniteTensorObjZero
    (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ) (M : integralOperationsFiniteModules l E W n) :
    ((MonoidalCategory.curriedTensor
      (integralOperationsFiniteModules l E W n)).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
    (integralCoefficientCommRingSheaf l E W n) M

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients

/-- The direct-sum total tensor exists in finite coefficient modules.
Source: Stacks Tag 012Z (auxiliary; not a blueprint node). -/
theorem integralOperationsFiniteHasMap
    (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ)
    (P Q : CochainComplex (integralOperationsFiniteModules l E W n) ℤ) :
    HomologicalComplex.HasMapBifunctor P Q
      (MonoidalCategory.curriedTensor (integralOperationsFiniteModules l E W n)) (.up ℤ) := by
  exact integralHasMap P Q

attribute [local instance 2000] integralOperationsFiniteHasMap

/-- The coefficient projection with its native ring-sheaf source explicit.
Source: Stacks Tag 03DA (auxiliary; not a blueprint node). -/
private noncomputable def integralOperationsProjection (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ) :
    completedIntegralCoefficientSheafUnrestricted l E W ⟶ integralCoefficientSheaf l E W n :=
  (integralOperationsForgetSheaf.{max u (t + 1)} (AlgebraicGeometry.Scheme.ProEt.topology W)).map
      (completedIntegralCommRingProjectionUnrestricted l E W n)

/-- Restriction along π_n, applied termwise, with unchanged underlying sheaves and maps.
Source: Stacks Tag 03DA (auxiliary; not a blueprint node). -/
noncomputable def integralOperationsRestrict (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ) :=
  (SheafOfModules.restrictScalars
    ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        (completedIntegralCommRingProjectionUnrestricted l E W n))).mapHomologicalComplex
          (ComplexShape.up ℤ)

/-- The canonical base-change functor, kept as a named functor during module calculations.
Source: Stacks Tag 09A5 (auxiliary; not a blueprint node). -/
private noncomputable def integralOperationsBaseChange {X Y : AlgebraicGeometry.Scheme.{t}}
    (f : X ⟶ Y) : Y.ProEt ⥤ X.ProEt :=
  AlgebraicGeometry.Scheme.proEtaleBaseChange f

/-- Continuity of the named base-change functor.
Source: Stacks Tag 09A5 (auxiliary; not a blueprint node). -/
private instance integralOperationsBaseChange_isContinuous
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y) :
    (integralOperationsBaseChange f).IsContinuous
      (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (AlgebraicGeometry.Scheme.ProEt.topology X) :=
  AlgebraicGeometry.Scheme.proEtaleBaseChange_isContinuous f

/-- Finite-level pullback, along the canonical constant-section coefficient map.
Source: Stacks Tag 03D2 (auxiliary; not a blueprint node). -/
noncomputable def integralOperationsLevelPullback {X Y : AlgebraicGeometry.Scheme.{t}}
    (f : X ⟶ Y) (n : ℕ) :=
  AlgebraicGeometry.Scheme.coefficientProEtaleModulePullback.{t, u} f
    (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))
@[instance]
theorem integralOperationsLevelPullback_additive {X Y : AlgebraicGeometry.Scheme.{t}}
    (f : X ⟶ Y) (n : ℕ) : (integralOperationsLevelPullback l E f n).Additive := by
  have : (AlgebraicGeometry.Scheme.coefficientProEtaleModuleDirectImage.{t, u} f
      (CommRingCat.of
        (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).Additive := by
    constructor
    intro M N a b
    rfl
  exact (AlgebraicGeometry.Scheme.coefficientProEtaleModuleAdjunction.{t, u} f
    (CommRingCat.of
      (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).left_adjoint_additive

/-- The nth pullback tower level Res_n f*(P_n), as a functor on complexes.
Source: Stacks Tags 03D2 and 06YT
(auxiliary; not a blueprint node). -/
noncomputable def integralOperationsPullbackLevel {X Y : AlgebraicGeometry.Scheme.{t}}
    (f : X ⟶ Y) (n : ℕ) :=
  unrestrictedIntegralFiniteComplex l E Y n ⋙
    (integralOperationsLevelPullback l E f n).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      integralOperationsRestrict l E X n

/-- The finite coefficient map, with its native ring sheaves explicit.
Source: Stacks Tag 03D2 (auxiliary; not a blueprint node). -/
private noncomputable def integralOperationsDirectRingMap
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    integralCoefficientSheaf l E Y n ⟶
      ((integralOperationsBaseChange f).sheafPushforwardContinuous
        RingCat.{max u (t + 1)} (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (AlgebraicGeometry.Scheme.ProEt.topology X)).obj
          (integralCoefficientSheaf l E X n) :=
  ⟨Functor.whiskerRight
    (AlgebraicGeometry.Scheme.coefficientProEtaleDirectRingMap.{t, u} f
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).hom
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})⟩

/-- The canonical finite pullback adjunction, with the native coefficient categories explicit.
Source: Stacks Tag 03D2 (auxiliary; not a blueprint node). -/
private noncomputable def integralOperationsPullbackAdjunction
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    integralOperationsLevelPullback l E f n ⊣
      SheafOfModules.pushforward (integralOperationsDirectRingMap l E f n) :=
  AlgebraicGeometry.Scheme.coefficientProEtaleModuleAdjunction.{t, u} f
    (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))

/-- The canonical generator in finite module pullback, given by its adjunction unit.
Source: Stacks Tag 03D2 (auxiliary; not a blueprint node). -/
noncomputable def integralOperationsPullbackGenerator {X Y : AlgebraicGeometry.Scheme.{t}}
    (f : X ⟶ Y) (n : ℕ)
    (M : integralOperationsFiniteModules l E Y n) (V : Y.ProEt) (x : M.val.obj (op V)) :=
  ((AlgebraicGeometry.Scheme.coefficientProEtaleModuleAdjunction.{t, u} f
    (CommRingCat.of
      (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).unit.app M).val.app
      (op V) x

section IntegralTensorTransitionProof

section FiniteLinearization

attribute [local irreducible] unrestrictedIntegralReductionExistence
  unrestrictedIntegralReductionFunctor unrestrictedIntegralTransition
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingProjectionUnrestricted

private noncomputable def integralFiniteStep (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ) :
    integralCoefficientCommRingSheaf l E W (n + 1) ⟶
      integralCoefficientCommRingSheaf l E W n :=
  (constantSheaf _ CommRingCat.{max u (t + 1)}).map
    (CommRingCat.ofHom
      ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
        ((Padic.coefficientExtensionTransition l E (n + 1)).comp
          (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom)))

private noncomputable abbrev integralFiniteRestrict
    (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ) :=
  SheafOfModules.restrictScalars (integralCoefficientSheafTransition l E W n)

private noncomputable def integralFiniteMap
    (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ)
    (P : CochainComplex (integralTowerModules l E W) ℤ) (i : ℤ) :
    (((unrestrictedIntegralFiniteComplex l E W (n + 1)).obj P).X i) ⟶
      (integralFiniteRestrict l E W n).obj
        (((unrestrictedIntegralFiniteComplex l E W n).obj P).X i) := by
  refine SheafOfModules.IntegralScalarProof.retypeMap
    (integralCoefficientSheafTransition l E W n) _ _ ?_ ?_
  · exact (SheafOfModules.toSheaf (completedIntegralCoefficientSheafUnrestricted l E W)).map
      (((unrestrictedIntegralTransition l E W n).app P).f i)
  · intro U s x
    exact unrestrictedIntegralTransition_smul l E W n P i U s x

private noncomputable def integralFiniteTransition
    (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ) :
    unrestrictedIntegralFiniteComplex l E W (n + 1) ⟶
      unrestrictedIntegralFiniteComplex l E W n ⋙
        (integralFiniteRestrict l E W n).mapHomologicalComplex (.up ℤ) where
  app P :=
    { f := integralFiniteMap l E W n P
      comm' := by
        intro i j _
        ext U x
        change _ = _
        exact congrArg (fun k ↦ k.val.app U x)
          (((unrestrictedIntegralTransition l E W n).app P).comm i j) }
  naturality := by
    intro P Q a
    apply HomologicalComplex.hom_ext
    intro i
    ext U x
    exact congrArg (fun k ↦ (k.f i).val.app U x)
      ((unrestrictedIntegralTransition l E W n).naturality a)

end FiniteLinearization

private theorem completedProjection_locallySurjective (W : AlgebraicGeometry.Scheme.{t})
    (n : ℕ) : Presheaf.IsLocallySurjective (AlgebraicGeometry.Scheme.ProEt.topology W)
      ((integralOperationsForgetSheaf.{max u (t + 1)} (AlgebraicGeometry.Scheme.ProEt.topology
        W)).map
        (completedIntegralCommRingProjectionUnrestricted l E W n)).hom := by
  let J := AlgebraicGeometry.Scheme.ProEt.topology W
  let : EssentiallySmall.{max u (t + 1)} W.ProEt := essentiallySmallSelf _
  let : J.WEqualsLocallyBijective CommRingCat.{max u (t + 1)} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  let q : CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)) ⟶
      CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))) :=
    CommRingCat.ofHom
      ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
        ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))).comp
          (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom))
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (y.down)
    refine ⟨⟨x⟩, ?_⟩
    apply ULift.ext
    exact hx
  have hc := constantMap_surjective J q hq
  have : Presheaf.IsLocallySurjective J (integralConstantQuotientOfUniverses l E W n).hom := by
    rw [Presheaf.isLocallySurjective_iff_whisker_forget]
    exact (Presheaf.isLocallySurjective_iff_whisker_forget J
      (((constantSheaf J CommRingCat.{max u (t + 1)}).map q).hom)).mp hc
  have hπ : Presheaf.IsLocallySurjective J
      (limit.π (integralCoefficientSheafSystem l E W) (op n)).hom := by
    exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac J
      (f₁ := (integralConstantToCompletionOfUniverses l E W).hom)
      (f₃ := (integralConstantQuotientOfUniverses l E W n).hom)
      (congrArg (fun k ↦ k.hom)
        (limit.lift_π (integralConstantConeOfUniverses l E W) (op n)))
  constructor
  intro U s
  apply J.superset_covering ?_ (Presheaf.imageSieve_mem J
    (limit.π (integralCoefficientSheafSystem l E W) (op n)).hom s)
  intro V f hf
  obtain ⟨x, hx⟩ := hf
  exact ⟨x, hx⟩

private theorem integralProjection_step (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ) :
    (integralOperationsForgetSheaf.{max u (t + 1)} (AlgebraicGeometry.Scheme.ProEt.topology W)).map
        (completedIntegralCommRingProjectionUnrestricted l E W (n + 1)) ≫
          integralCoefficientSheafTransition l E W n =
    (integralOperationsForgetSheaf.{max u (t + 1)} (AlgebraicGeometry.Scheme.ProEt.topology W)).map
        (completedIntegralCommRingProjectionUnrestricted l E W n) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  change (limit.π (integralCoefficientSheafSystem l E W) (op (n + 1))).hom.app U ≫
      (integralCoefficientSheafTransition l E W n).hom.app U =
    (limit.π (integralCoefficientSheafSystem l E W) (op n)).hom.app U
  have h := congrArg (fun k ↦ k.hom.app U)
    (limit.w (integralCoefficientSheafSystem l E W) (homOfLE (Nat.le_succ n)).op)
  simpa only [integralCoefficientSheafSystem, Functor.ofOpSequence_map_homOfLE_succ,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] using h

private noncomputable abbrev integralDirectRingMap
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :=
  integralOperationsDirectRingMap l E f n

private theorem integralDirectRingMap_square
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    integralCoefficientSheafTransition l E Y n ≫ integralDirectRingMap l E f n =
      integralDirectRingMap l E f (n + 1) ≫
        ((integralOperationsBaseChange f).sheafPushforwardContinuous
          RingCat.{max u (t + 1)} (AlgebraicGeometry.Scheme.ProEt.topology Y)
          (AlgebraicGeometry.Scheme.ProEt.topology X)).map
            (integralCoefficientSheafTransition l E X n) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  let q := CommRingCat.ofHom
    ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
      ((Padic.coefficientExtensionTransition l E (n + 1)).comp
        (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom))
  exact congrArg (fun k ↦ (integralOperationsRingForget).map (k.hom.app V))
    (AlgebraicGeometry.Scheme.directRingMap_naturality f q)

attribute [local irreducible]
  AlgebraicGeometry.Scheme.coefficientProEtaleModuleAdjunction
  AlgebraicGeometry.Scheme.coefficientProEtaleModulePullback Functor.leftAdjoint

private noncomputable abbrev integralPullbackAdj
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :=
  integralOperationsPullbackAdjunction l E f n

private noncomputable def integralPullbackFiniteData
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y) (n : ℕ)
    {M : integralOperationsFiniteModules l E Y (n + 1)}
    {N : integralOperationsFiniteModules l E Y n}
    (a : M ⟶ (integralFiniteRestrict l E Y n).obj N) :=
  SheafOfModules.IntegralPullbackProof.mateData
    (integralOperationsBaseChange f)
    (integralCoefficientSheafTransition l E X n) (integralCoefficientSheafTransition l E Y n)
    (integralDirectRingMap l E f (n + 1)) (integralDirectRingMap l E f n)
    (integralDirectRingMap_square l E f n)
    (integralPullbackAdj l E f (n + 1)) (integralPullbackAdj l E f n) a

private noncomputable def integralPullbackFiniteMap
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y) (n : ℕ)
    {M : integralOperationsFiniteModules l E Y (n + 1)}
    {N : integralOperationsFiniteModules l E Y n}
    (a : M ⟶ (integralFiniteRestrict l E Y n).obj N) :
    (integralOperationsLevelPullback l E f (n + 1)).obj M ⟶
      (integralFiniteRestrict l E X n).obj ((integralOperationsLevelPullback l E f n).obj N) :=
  integralPullbackFiniteData l E f n a

private theorem integralPullbackFiniteMap_naturality
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y) (n : ℕ)
    {M M' : integralOperationsFiniteModules l E Y (n + 1)}
    {N N' : integralOperationsFiniteModules l E Y n}
    (a : M ⟶ (integralFiniteRestrict l E Y n).obj N)
    (b : M' ⟶ (integralFiniteRestrict l E Y n).obj N')
    (u : M ⟶ M') (v : N ⟶ N')
    (h : u ≫ b = a ≫ (integralFiniteRestrict l E Y n).map v) :
    (integralOperationsLevelPullback l E f (n + 1)).map u ≫
        integralPullbackFiniteMap l E f n b =
      integralPullbackFiniteMap l E f n a ≫ (integralFiniteRestrict l E X n).map
        ((integralOperationsLevelPullback l E f n).map v) :=
  SheafOfModules.IntegralPullbackProof.mateData_naturality
    (integralOperationsBaseChange f)
    (integralCoefficientSheafTransition l E X n) (integralCoefficientSheafTransition l E Y n)
    (integralDirectRingMap l E f (n + 1)) (integralDirectRingMap l E f n)
    (integralDirectRingMap_square l E f n)
    (integralPullbackAdj l E f (n + 1)) (integralPullbackAdj l E f n) a b u v h

private noncomputable def integralPullbackFiniteComplexMap
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y) (n : ℕ)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    ((integralOperationsLevelPullback l E f (n + 1)).mapHomologicalComplex (.up ℤ)).obj
        ((unrestrictedIntegralFiniteComplex l E Y (n + 1)).obj P) ⟶
      ((integralFiniteRestrict l E X n).mapHomologicalComplex (.up ℤ)).obj
        (((integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ)).obj
          ((unrestrictedIntegralFiniteComplex l E Y n).obj P)) where
  f i := integralPullbackFiniteMap l E f n (((integralFiniteTransition l E Y n).app P).f i)
  comm' i j _ := by
    exact (integralPullbackFiniteMap_naturality l E f n
      (((integralFiniteTransition l E Y n).app P).f i)
      (((integralFiniteTransition l E Y n).app P).f j)
      (((unrestrictedIntegralFiniteComplex l E Y (n + 1)).obj P).d i j)
      (((unrestrictedIntegralFiniteComplex l E Y n).obj P).d i j)
      (((integralFiniteTransition l E Y n).app P).comm i j).symm).symm

attribute [local irreducible] unrestrictedIntegralReductionExistence
  unrestrictedIntegralReductionFunctor unrestrictedIntegralTransition
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingProjectionUnrestricted

private noncomputable abbrev integralCompletedProjection
    (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ) := integralOperationsProjection l E W n

private noncomputable abbrev integralCompletedRestrict (W : AlgebraicGeometry.Scheme.{t})
    (n : ℕ) : integralOperationsFiniteModules l E W n ⥤ integralTowerModules l E W :=
  SheafOfModules.restrictScalars.{max u (t + 1)} (integralCompletedProjection l E W n)

private noncomputable def integralPullbackTransitionCandidate
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    integralOperationsPullbackLevel l E f (n + 1) ⟶ integralOperationsPullbackLevel l E f n where
  app P := by
    refine SheafOfModules.IntegralScalarProof.restrictComplexMap
      (R := completedIntegralCoefficientSheafUnrestricted l E X)
      (S := integralCoefficientSheaf l E X (n + 1))
      (T := integralCoefficientSheaf l E X n)
      (integralCompletedProjection l E X (n + 1))
      (integralCompletedProjection l E X n)
      (integralCoefficientSheafTransition l E X n) (integralProjection_step l E X n)
      ?_
    exact integralPullbackFiniteComplexMap l E f n P
  naturality := by
    intro P Q a
    apply HomologicalComplex.hom_ext
    intro i
    ext U x
    have h := congrArg (fun k ↦ k.f i) ((integralFiniteTransition l E Y n).naturality a)
    have h' := integralPullbackFiniteMap_naturality l E f n
      (((integralFiniteTransition l E Y n).app P).f i)
      (((integralFiniteTransition l E Y n).app Q).f i)
      (((unrestrictedIntegralFiniteComplex l E Y (n + 1)).map a).f i)
      (((unrestrictedIntegralFiniteComplex l E Y n).map a).f i) h
    exact congrArg (fun k ↦ k.val.app U x) h'

private theorem integralPullback_restricted_hom_ext
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y) (n : ℕ)
    (M : integralOperationsFiniteModules l E Y (n + 1))
    (N : integralOperationsFiniteModules l E X n)
    (a b : (integralCompletedRestrict l E X (n + 1)).obj
        ((integralOperationsLevelPullback l E f (n + 1)).obj M) ⟶
      (integralCompletedRestrict l E X n).obj N)
    (h : ∀ (V : Y.ProEt) (x : M.val.obj (op V)),
      (integralOperationsSectionApply a ((integralOperationsBaseChange f).op.obj (op V)))
          (integralOperationsPullbackGenerator l E f (n + 1) M V x) =
        (integralOperationsSectionApply b ((integralOperationsBaseChange f).op.obj (op V)))
          (integralOperationsPullbackGenerator l E f (n + 1) M V x)) : a = b := by
  have : Presheaf.IsLocallySurjective (AlgebraicGeometry.Scheme.ProEt.topology X)
      (integralCompletedProjection l E X (n + 1)).hom :=
    completedProjection_locallySurjective l E X (n + 1)
  apply SheafOfModules.IntegralPullbackProof.restricted_hom_ext
    (integralOperationsBaseChange f)
    (integralCoefficientSheafTransition l E X n)
    (integralDirectRingMap l E f (n + 1)) (integralPullbackAdj l E f (n + 1))
    (integralCompletedProjection l E X (n + 1)) (integralCompletedProjection l E X n)
    (integralProjection_step l E X n) M N a b
  intro U x
  change a.val.app _ (SheafOfModules.IntegralPullbackProof.unitSection
    (integralOperationsBaseChange f) (integralDirectRingMap l E f (n + 1))
    (integralPullbackAdj l E f (n + 1)) M U x) = _
  exact h U.unop x

end IntegralTensorTransitionProof

/-- The pullback transitions are the unique natural chain maps carrying the generator
of a finite reduction to the generator of its next reduction. These are the maps
f⁻¹(x)⊗a ↦ f⁻¹(r_n)(f⁻¹(x))⊗ρ_n(a), with the completed scalar actions.
Source: Stacks Tags 03D2 and 06YT
(auxiliary; not a blueprint node).
Proof: on module Kan-extension generators use the given reduction r_n; reduce the
coefficient by ρ_n. The maps c_A commute with coefficient reduction because their
adjoints send each coefficient to its constant section. Thus the map is balanced,
linear over the completion, compatible with restrictions, and commutes with the
differential. Sheafification gives the chain maps. Naturality is the same equality
on generators. Conversely a completed-linear map with the unit equation has this
action on all scalar multiples of every Kan-extension generator: the completed
projection to A_(n+1) is locally surjective. Those generators locally generate the
sheafified pullback. Thus the unit equation determines the transition uniquely. -/
theorem integralOperationsPullbackTransition_existsUnique
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    ∃! τ : integralOperationsPullbackLevel l E f (n + 1) ⟶
      integralOperationsPullbackLevel l E f n,
      ∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ) (V : Y.ProEt)
        (x : (((unrestrictedIntegralFiniteComplex l E Y (n + 1)).obj P).X i).val.obj (op V)),
        ((τ.app P).f i).val.app (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange f).obj V))
          (integralOperationsPullbackGenerator l E f (n + 1)
            (((unrestrictedIntegralFiniteComplex l E Y (n + 1)).obj P).X i) V x) =
        integralOperationsPullbackGenerator l E f n
          (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) V
          ((((unrestrictedIntegralTransition l E Y n).app P).f i).val.app (op V) x) := by
  let τ := integralPullbackTransitionCandidate l E f n
  have hτ : ∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ)
      (V : Y.ProEt)
      (x : (((unrestrictedIntegralFiniteComplex l E Y (n + 1)).obj P).X i).val.obj
        (op V)),
      ((τ.app P).f i).val.app (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange f).obj V))
        (integralOperationsPullbackGenerator l E f (n + 1)
          (((unrestrictedIntegralFiniteComplex l E Y (n + 1)).obj P).X i) V x) =
      integralOperationsPullbackGenerator l E f n
        (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) V
        ((((unrestrictedIntegralTransition l E Y n).app P).f i).val.app (op V) x) := by
    intro P i V x
    exact SheafOfModules.IntegralPullbackProof.mateData_unit_formula
      (integralOperationsBaseChange f)
      (integralCoefficientSheafTransition l E X n) (integralCoefficientSheafTransition l E Y n)
      (integralDirectRingMap l E f (n + 1)) (integralDirectRingMap l E f n)
      (integralDirectRingMap_square l E f n)
      (integralPullbackAdj l E f (n + 1)) (integralPullbackAdj l E f n)
      (((integralFiniteTransition l E Y n).app P).f i) (op V) x
  refine ⟨τ, hτ, ?_⟩
  intro τ' hτ'
  apply NatTrans.ext
  funext P
  apply HomologicalComplex.hom_ext
  intro i
  apply integralPullback_restricted_hom_ext l E f n
    (((unrestrictedIntegralFiniteComplex l E Y (n + 1)).obj P).X i)
    ((integralOperationsLevelPullback l E f n).obj
      (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i))
  intro V x
  exact (hτ' P i V x).trans (hτ P i V x).symm

/-- The pullback transition, fixed uniquely by the module unit formula.
Source: Stacks Tag 03D2 (auxiliary; not a blueprint node). -/
noncomputable def integralOperationsPullbackTransition
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    integralOperationsPullbackLevel l E f (n + 1) ⟶ integralOperationsPullbackLevel l E f n :=
  (integralOperationsPullbackTransition_existsUnique l E f n).exists.choose

/-- The direct-sum total tensor of the two finite reductions, with restricted action.
The total differential is d_P⊗1+(-1)^p 1⊗d_Q on the (p,q)-summand.
Source: Stacks Tags 012Z and 06YM
(auxiliary; not a blueprint node). -/
noncomputable def integralOperationsTensorLevel (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ) :
    (CochainComplex (integralTowerModules l E W) ℤ) ×
      (CochainComplex (integralTowerModules l E W) ℤ) ⥤
        CochainComplex (integralTowerModules l E W) ℤ :=
  integralOperationsTensorComposite (unrestrictedIntegralFiniteComplex l E W n)
    (SheafOfModules.restrictScalars ((integralOperationsForgetSheaf.{max u (t + 1)}
      (AlgebraicGeometry.Scheme.ProEt.topology W)).map
        (completedIntegralCommRingProjectionUnrestricted l E W n)))

/-- A sheafified pure tensor in the recorded finite-coefficient tensor product.
Source: Stacks Tag 03EK (auxiliary; not a blueprint node). -/
noncomputable def integralOperationsTensorSection (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ)
    (M N : integralOperationsFiniteModules l E W n)
    (U : W.ProEtᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    (MonoidalCategory.tensorObj M N).val.obj U :=
  letI : EssentiallySmall.{max u (t + 1)} W.ProEt := essentiallySmallSelf _
  letI := integralCoefficientAbSheafify.{t, u} W
  letI := integralCoefficientAbLocallyBijective.{t, u} W
  letI := SheafOfModules.isMonoidal_W_independentCoefficients
    (J := AlgebraicGeometry.Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W n)
  ((SheafOfModules.tensorObjIsoSheafification
    (R := integralCoefficientCommRingSheaf l E W n) M N).inv.val.app U)
    ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology W)
      ((MonoidalCategory.tensorObj M.val N.val).presheaf :
        W.ProEtᵒᵖ ⥤ AddCommGrpCat.{max u (t + 1)})).app U
        (x ⊗ₜ[(integralCoefficientCommRingSheaf l E W n).obj.obj U] y))

/-- A tensor generator in the (p,q)-summand of the direct-sum total tensor complex.
Source: Stacks Tags 012Z and 03EK
(auxiliary; not a blueprint node). -/
noncomputable def integralOperationsTotalTensorSection (W : AlgebraicGeometry.Scheme.{t})
    (n : ℕ) (P Q : CochainComplex (integralTowerModules l E W) ℤ)
    (p q : ℤ) (U : W.ProEtᵒᵖ)
    (x : (((unrestrictedIntegralFiniteComplex l E W n).obj P).X p).val.obj U)
    (y : (((unrestrictedIntegralFiniteComplex l E W n).obj Q).X q).val.obj U) :=
  (CochainComplex.ιMapBifunctor
    ((unrestrictedIntegralFiniteComplex l E W n).obj P)
    ((unrestrictedIntegralFiniteComplex l E W n).obj Q)
    (MonoidalCategory.curriedTensor (integralOperationsFiniteModules l E W n))
    p q (p + q) rfl).val.app U
      (integralOperationsTensorSection l E W n
        (((unrestrictedIntegralFiniteComplex l E W n).obj P).X p)
        (((unrestrictedIntegralFiniteComplex l E W n).obj Q).X q) U x y)

section TensorTransitionSpecialization
attribute [local instance 2001] SheafOfModules.monoidalCategory
  SheafOfModules.isMonoidal_W_independentCoefficients

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency true in
/-- The tensor tower transition is uniquely fixed on every direct-sum tensor generator.
Source: Stacks Tags 012Z, 03EK and 06YT
(auxiliary; not a blueprint node).
Proof: send x⊗y in degree (p,q) to r_n(x)⊗r_n(y). Coefficient compatibility makes
this balanced over A_(n+1) and linear over the completion. Form the direct-sum map
in each total degree; it commutes with d_P⊗1+(-1)^p 1⊗d_Q. Sheafification makes
it a chain map. Naturality in both input complexes is equality on generators.
Conversely pure tensors generate the presheaf tensor, sheafification extends their
equalities uniquely, and the coproduct injections jointly determine a map. This
proves uniqueness of the natural transformation. -/
theorem integralOperationsTensorTransition_existsUnique
    (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ) :
    ∃! τ : integralOperationsTensorLevel l E W (n + 1) ⟶
      integralOperationsTensorLevel l E W n,
      ∀ (P Q : CochainComplex (integralTowerModules l E W) ℤ) (p q : ℤ) (U : W.ProEtᵒᵖ)
        (x : (((unrestrictedIntegralFiniteComplex l E W (n + 1)).obj P).X p).val.obj U)
        (y : (((unrestrictedIntegralFiniteComplex l E W (n + 1)).obj Q).X q).val.obj U),
        ((τ.app (P, Q)).f (p + q)).val.app U
          (integralOperationsTotalTensorSection l E W (n + 1) P Q p q U x y) =
        integralOperationsTotalTensorSection l E W n P Q p q U
          ((((unrestrictedIntegralTransition l E W n).app P).f p).val.app U x)
          ((((unrestrictedIntegralTransition l E W n).app Q).f q).val.app U y) := by
  let : EssentiallySmall.{max u (t + 1)} W.ProEt := essentiallySmallSelf _
  let := integralCoefficientAbSheafify.{t, u} W
  let := integralCoefficientAbLocallyBijective.{t, u} W
  have h := TensorNaturalProof.existsUnique
    (C := W.ProEt) (J := AlgebraicGeometry.Scheme.ProEt.topology W)
    (D := CochainComplex (integralTowerModules l E W) ℤ)
    (R₀ := completedIntegralCoefficientSheafUnrestricted l E W)
    (integralCoefficientCommRingSheaf l E W (n+1)) (integralCoefficientCommRingSheaf l E W n)
    (integralOperationsProjection l E W (n + 1))
    (integralOperationsProjection l E W n)
    (integralFiniteStep l E W n) (integralProjection_step l E W n)
    (unrestrictedIntegralFiniteComplex l E W (n+1)) (unrestrictedIntegralFiniteComplex l E W n)
    (integralFiniteTransition l E W n)
    (hf := completedProjection_locallySurjective l E W (n+1))
  exact h

end TensorTransitionSpecialization

/-- The tensor transition with the uniquely prescribed pure-tensor formula.
Source: Stacks Tag 03EK (auxiliary; not a blueprint node). -/
noncomputable def integralOperationsTensorTransition
    (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ) :
    integralOperationsTensorLevel l E W (n + 1) ⟶ integralOperationsTensorLevel l E W n :=
  (integralOperationsTensorTransition_existsUnique l E W n).exists.choose

section Roos

variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]

/-- The transition maps of a strict tower of complexes.
Source: Stacks Tag 08TC (auxiliary; not a blueprint node). -/
def integralOperationsTowerStep (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) (n : ℕ) :=
  C.map (homOfLE (Nat.le_succ n)).op

/-- The Roos complex Cone(1-s)[-1], with products computed termwise.
Source: Stacks Tag 08TC (auxiliary; not a blueprint node). -/
noncomputable def integralOperationsRoos (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) :=
  CochainComplex.mappingCocone
    (towerTransitionEndomorphism (K := fun n ↦ C.obj (op n)) (integralOperationsTowerStep C))

/-- A strict tower morphism gives the commutative square for 1-s.
Source: Stacks Tag 08TC (auxiliary; not a blueprint node).
Proof: after the nth product projection both composites are
pr_n a_n - pr_(n+1) t_n a_n; naturality of a identifies t_n a_n with
 a_(n+1) t'_n. Product extensionality gives the square. -/
theorem integralOperationsRoos_square
    {C C' : ℕᵒᵖ ⥤ CochainComplex A ℤ} (α : C ⟶ C') :
    towerTransitionEndomorphism (K := fun n ↦ C.obj (op n)) (integralOperationsTowerStep C) ≫
        Limits.Pi.map (fun n ↦ α.app (op n)) =
      Limits.Pi.map (fun n ↦ α.app (op n)) ≫
        towerTransitionEndomorphism (K := fun n ↦ C'.obj (op n))
          (integralOperationsTowerStep C') := by
  apply Eq.symm
  apply towerTransitionEndomorphism_natural_backward
  intro n
  exact (α.naturality (homOfLE (Nat.le_succ n)).op).symm

/-- The induced map on the two shifted-cone summands is the diagonal product map.
Source: Stacks Tag 08TC (auxiliary; not a blueprint node). -/
noncomputable def integralOperationsRoosMap
    {C C' : ℕᵒᵖ ⥤ CochainComplex A ℤ} (α : C ⟶ C') :
    integralOperationsRoos C ⟶ integralOperationsRoos C' :=
  (shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).map
    (HomologicalComplex.homotopyCofiber.mapArrowHom
      (towerTransitionEndomorphism (K := fun n ↦ C.obj (op n)) (integralOperationsTowerStep C))
      (towerTransitionEndomorphism (K := fun n ↦ C'.obj (op n)) (integralOperationsTowerStep C'))
      (fun j ↦ ⟨j - 1, Int.sub_add_cancel j 1⟩)
      (Arrow.homMk (Limits.Pi.map (fun n ↦ α.app (op n)))
        (Limits.Pi.map (fun n ↦ α.app (op n))) (integralOperationsRoos_square α).symm))

/-- The diagonal product map preserves identities.
Source: Stacks Tag 08TC (auxiliary; not a blueprint node).
Proof: the product map of identity components is identity; the mapping-cone map
and the shift preserve identity maps. -/
theorem integralOperationsRoosMap_id (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    integralOperationsRoosMap (𝟙 C) = 𝟙 (integralOperationsRoos C) := by
  have h : Limits.Pi.map (fun n ↦ 𝟙 (C.obj (op n))) = 𝟙 _ := by
    apply Limits.Pi.hom_ext
    intro n
    simp
  have ha : Arrow.homMk (Limits.Pi.map (fun n ↦ 𝟙 (C.obj (op n))))
      (Limits.Pi.map (fun n ↦ 𝟙 (C.obj (op n))))
      (integralOperationsRoos_square (𝟙 C)).symm =
      𝟙 (Arrow.mk (towerTransitionEndomorphism
        (K := fun n ↦ C.obj (op n)) (integralOperationsTowerStep C))) := by
    apply Arrow.hom_ext <;> exact h
  change (shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).map
      (HomologicalComplex.homotopyCofiber.mapArrowHom _ _
        (fun j ↦ ⟨j - 1, Int.sub_add_cancel j 1⟩)
        (Arrow.homMk (Limits.Pi.map (fun n ↦ 𝟙 (C.obj (op n))))
          (Limits.Pi.map (fun n ↦ 𝟙 (C.obj (op n))))
          (integralOperationsRoos_square (𝟙 C)).symm)) = _
  erw [ha, HomologicalComplex.homotopyCofiber.mapArrowHom_id]
  exact (shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).map_id _

/-- The diagonal product map preserves composition.
Source: Stacks Tag 08TC (auxiliary; not a blueprint node).
Proof: composition of product maps is the product of componentwise composites;
the mapping-cone map and shift preserve composition. -/
theorem integralOperationsRoosMap_comp
    {C C' C'' : ℕᵒᵖ ⥤ CochainComplex A ℤ} (α : C ⟶ C') (β : C' ⟶ C'') :
    integralOperationsRoosMap (α ≫ β) =
      integralOperationsRoosMap α ≫ integralOperationsRoosMap β := by
  unfold integralOperationsRoosMap
  rw [← Functor.map_comp, ← HomologicalComplex.homotopyCofiber.mapArrowHom_comp]
  congr 2
  apply Arrow.hom_ext <;> apply Limits.Pi.hom_ext <;> intro n <;> simp

/-- The functorial strict-complex Roos construction; this makes no choice of cones
in a bare triangulated category.
Source: Stacks Tag 08TC (auxiliary; not a blueprint node). -/
noncomputable def integralOperationsRoosFunctor :
    (ℕᵒᵖ ⥤ CochainComplex A ℤ) ⥤ CochainComplex A ℤ where
  obj := integralOperationsRoos
  map := integralOperationsRoosMap
  map_id := integralOperationsRoosMap_id
  map_comp := integralOperationsRoosMap_comp

end Roos

/-- Countable products of completed-coefficient module sheaves.
Source: Stacks Tag 08TC (auxiliary; not a blueprint node). -/
noncomputable instance integralOperationsCountableProducts (W : AlgebraicGeometry.Scheme.{t}) :
    HasCountableProducts (integralTowerModules l E W) :=
  (AlgebraicGeometry.Scheme.ProEt.countableProducts_exact.{t, u, 0} W
    (completedIntegralCommRingSheafUnrestricted l E W)).1
@[instance]
theorem integralOperationsDerivedCountableProducts (W : AlgebraicGeometry.Scheme.{t}) :
    HasCountableProducts (DerivedCategory (integralTowerModules l E W)) := by
  let A := integralTowerModules l E W
  have : CountableAB4Star A :=
    ⟨fun I _ ↦ AlgebraicGeometry.Scheme.ProEt.products_exact.{t, u, 0} W
      (SheafOfModules.derivedChangeRingIndependentCoefficients
        (AlgebraicGeometry.Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)) I⟩
  exact (derivedCategory_countableProducts_core.{0} A).choose

/-- The strict pullback tower, functorial in the input complex.
Source: Stacks Tags 03D2 and 06YT
(auxiliary; not a blueprint node). -/
noncomputable def integralOperationsPullbackTowerFunctor
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y) :=
  (Functor.ofOpSequence (X := fun n ↦ integralOperationsPullbackLevel l E f n)
    (integralOperationsPullbackTransition l E f)).flip

/-- The strict total-tensor tower, functorial in both input complexes.
Source: Stacks Tags 012Z and 06YT
(auxiliary; not a blueprint node). -/
noncomputable def integralOperationsTensorTowerFunctor (W : AlgebraicGeometry.Scheme.{t}) :=
  (Functor.ofOpSequence (X := fun n ↦ integralOperationsTensorLevel l E W n)
    (integralOperationsTensorTransition l E W)).flip

/-- T_f(P)=Cone(1-s)[-1] on the strict tower Res_n f*(P_n).
Source: Stacks Tag 08TC (auxiliary; not a blueprint node). -/
noncomputable def integralOperationsPullbackComplexFunctor
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y) :=
  integralOperationsPullbackTowerFunctor l E f ⋙ integralOperationsRoosFunctor

/-- T(P,Q)=Cone(1-s)[-1] on the strict tower of restricted finite total tensors.
Source: Stacks Tags 012Z and 08TC
(auxiliary; not a blueprint node). -/
noncomputable def integralOperationsTensorComplexFunctor (W : AlgebraicGeometry.Scheme.{t}) :=
  integralOperationsTensorTowerFunctor l E W ⋙ integralOperationsRoosFunctor

/-- The full subcategory of K-flat complexes with flat terms, without a boundedness condition.
Source: Stacks Tags 06YN and 03ER
(auxiliary; not a blueprint node). -/
def integralOperationsGoodComplex (W : AlgebraicGeometry.Scheme.{t}) :
    ObjectProperty (CochainComplex (integralTowerModules l E W) ℤ) :=
  fun P ↦ CochainComplex.IsKFlatIndependentCoefficients
    (J := AlgebraicGeometry.Scheme.ProEt.topology W)
    (R := completedIntegralCommRingSheafUnrestricted l E W) P ∧
      ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)}
        (R := completedIntegralCommRingSheafUnrestricted l E W) (P.X i)

/-- Localization of the full subcategory of good representatives into D(W_proet,O_E).
Source: Stacks Tags 06YS and 06YT
(auxiliary; not a blueprint node). -/
noncomputable def integralOperationsGoodLocalization (W : AlgebraicGeometry.Scheme.{t}) :=
  (integralOperationsGoodComplex l E W).ι ⋙ DerivedCategory.Q

/-- The complex pullback construction on the good representative subcategory, localized.
Source: Stacks Tags 06YT and 08TC
(auxiliary; not a blueprint node). -/
noncomputable def integralOperationsPullbackOnGood
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y) :=
  (integralOperationsGoodComplex l E Y).ι ⋙
    integralOperationsPullbackComplexFunctor l E f ⋙ DerivedCategory.Q

/-- The total tensor construction on pairs of good representatives, localized.
Source: Stacks Tags 06YT and 08TC
(auxiliary; not a blueprint node). -/
noncomputable def integralOperationsTensorOnGood (W : AlgebraicGeometry.Scheme.{t}) :=
  ((integralOperationsGoodComplex l E W).ι.prod
    (integralOperationsGoodComplex l E W).ι) ⋙
      integralOperationsTensorComplexFunctor l E W ⋙ DerivedCategory.Q

/-- The Roos derived-limit property of the actual strict tower, using its localized
transition maps and the chosen product in the derived category.
Source: Stacks Tag 08TC (auxiliary; not a blueprint node). -/
def integralOperationsDerivedLimitProperty (W : AlgebraicGeometry.Scheme.{t})
    (C : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E W) ℤ)
    (K : DerivedCategory (integralTowerModules l E W)) : Prop :=
  IsDerivedLimit (K := fun n ↦ DerivedCategory.Q.obj (C.obj (op n)))
    (fun n ↦ DerivedCategory.Q.map (integralOperationsTowerStep C n)) K

attribute [local instance 3000] Algebra.toModule

-- Prefer the exact completed-module presentation during private proof search.
attribute [local instance 3000] integralTowerHasDerivedCategory

section IntegralOperationsRoosQuasiIsoInvariantProof
set_option Elab.async true

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

end IntegralOperationsRoosQuasiIsoInvariantProof

section IntegralOperationsPullbackQuasiIsoInvariantProof

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

attribute [local irreducible] SheafOfModules.monoidalCategory
  CochainComplex.IsKFlatIndependentCoefficients
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  WeilConjectures.unrestrictedIntegralReductionExistence

set_option backward.isDefEq.respectTransparency false

end IntegralOperationsPullbackQuasiIsoInvariantProof

section IntegralOperationsTensorQuasiIsoInvariantProof

attribute [local irreducible] SheafOfModules.monoidalCategory

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  WeilConjectures.unrestrictedIntegralReductionExistence

namespace IntegralTensorProof

universe x y z

open SheafOfModules MonoidalCategory
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

end IntegralTensorProof

set_option backward.isDefEq.respectTransparency false

end IntegralOperationsTensorQuasiIsoInvariantProof

section IntegralOperationsGoodLocalizationProof

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ZeroObject

end IntegralOperationsGoodLocalizationProof

section IntegralOperationsTensorDescentProof

attribute [local irreducible] integralOperationsGoodLocalization
  integralOperationsPullbackOnGood

attribute [local irreducible] integralOperationsPullbackComplexFunctor
  integralOperationsTensorComplexFunctor integralOperationsPullbackTowerFunctor
  integralOperationsTensorTowerFunctor integralOperationsGoodComplex
  completedIntegralCoefficientSheafUnrestricted

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
open CategoryTheory

end IntegralOperationsTensorDescentProof

section IntegralOperationsComparisonExistsProof

attribute [local irreducible] integralOperationsGoodLocalization
  integralOperationsTensorOnGood

attribute [local irreducible] integralOperationsPullbackComplexFunctor
  integralOperationsTensorComplexFunctor integralOperationsPullbackTowerFunctor
  integralOperationsTensorTowerFunctor integralOperationsGoodComplex
  completedIntegralCoefficientSheafUnrestricted

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
open CategoryTheory

end IntegralOperationsComparisonExistsProof

section IntegralOperationsNormalizedDescentProof

attribute [local irreducible] integralOperationsGoodLocalization
  integralOperationsTensorOnGood integralOperationsPullbackOnGood

attribute [local irreducible] integralOperationsPullbackComplexFunctor
  integralOperationsTensorComplexFunctor integralOperationsPullbackTowerFunctor
  integralOperationsTensorTowerFunctor integralOperationsGoodComplex
  completedIntegralCoefficientSheafUnrestricted

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

end IntegralOperationsNormalizedDescentProof

section IntegralOperationsRoosDerivedLimitProof

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

end IntegralOperationsRoosDerivedLimitProof

section IntegralOperationsDerivedDescentProof

attribute [local irreducible] integralOperationsPullbackComplexFunctor
  integralOperationsTensorComplexFunctor integralOperationsPullbackTowerFunctor
  integralOperationsTensorTowerFunctor integralOperationsGoodComplex
  completedIntegralCoefficientSheafUnrestricted

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

end IntegralOperationsDerivedDescentProof

attribute [local irreducible] integralOperationsPullbackComplexFunctor
  integralOperationsTensorComplexFunctor integralOperationsPullbackTowerFunctor
  integralOperationsTensorTowerFunctor integralOperationsDerivedLimitProperty
  integralOperationsGoodComplex integralOperationsGoodLocalization
  integralOperationsPullbackOnGood

end WeilConjectures
