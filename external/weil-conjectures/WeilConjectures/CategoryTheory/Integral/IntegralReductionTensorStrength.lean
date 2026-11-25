/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Tensor.IntegralTensorNativeComparison
import Mathlib.CategoryTheory.Adjunction.Whiskering
import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralReductionTensorStrengthKFlat
import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralReductionTensorStrengthRepresentatives

/-! # The scalar tensor strength of normalized reduction

Source: Stacks 03CZ, 06YY, 07A4; integral Hom reduction, paragraphs 1--2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

open CategoryTheory CategoryTheory.MonoidalCategory

namespace CategoryTheory

/-- The tensor mate, before any internal Hom is taken.
Source: Stacks 03CZ and 07A4.
(blueprint: lem-sf-reduction-tensor-strength-invertible). -/
def scalarTensorStrength {C D : Type*} [Category C] [Category D]
    (T : C × C ⥤ C) (S : D × D ⥤ D) {F : C ⥤ D} {U : D ⥤ C}
    (adj : F ⊣ U) (mu : T ⋙ F ≅ F.prod F ⋙ S) :
    (𝟭 C).prod (F ⋙ U) ⋙ T ⟶ T ⋙ F ⋙ U :=
  (adj.whiskerRight (C × C)).homEquiv _ _
    (Functor.whiskerLeft ((𝟭 C).prod (F ⋙ U)) mu.hom ≫
      Functor.whiskerRight
        (NatTrans.prod (𝟙 F) (Functor.whiskerLeft F adj.counit)) S ≫ mu.inv)

/-- Component formula for the tensor mate.
Source: the unit formula for the adjunction Hom equivalence.
(blueprint: lem-sf-reduction-tensor-strength-invertible). -/
theorem scalarTensorStrength_app {C D : Type*} [Category C] [Category D]
    (T : C × C ⥤ C) (S : D × D ⥤ D) {F : C ⥤ D} {U : D ⥤ C}
    (adj : F ⊣ U) (mu : T ⋙ F ≅ F.prod F ⋙ S) (K V : C) :
    (scalarTensorStrength T S adj mu).app (K, V) =
      adj.homEquiv _ _ (mu.hom.app (K, U.obj (F.obj V)) ≫
        S.map (Prod.mkHom (𝟙 (F.obj K)) (adj.counit.app (F.obj V))) ≫
        mu.inv.app (K, V)) := by
  simp only [scalarTensorStrength, Adjunction.homEquiv_unit,
    NatTrans.comp_app, Adjunction.whiskerRight_unit_app_app]
  simp [Functor.whiskeringRight, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, NatTrans.prod, CategoryTheory.Functor.map_comp]

/-- Transport a tensor strength along a tensor presentation comparison.
Source: Stacks 06YY, uniqueness of localization.
(blueprint: lem-sf-reduction-tensor-strength-invertible). -/
def nativeScalarTensorStrength {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] (T : C × C ⥤ C) (S : D × D ⥤ D)
    {F : C ⥤ D} {U : D ⥤ C} (adj : F ⊣ U) (mu : T ⋙ F ≅ F.prod F ⋙ S)
    (e : T ≅ tensor C) :
    (𝟭 C).prod (F ⋙ U) ⋙ tensor C ⟶ tensor C ⋙ F ⋙ U :=
  Functor.whiskerLeft ((𝟭 C).prod (F ⋙ U)) e.inv ≫
    scalarTensorStrength T S adj mu ≫ Functor.whiskerRight e.hom (F ⋙ U)

end CategoryTheory

universe d t u
open CategoryTheory.Limits
namespace WeilConjectures.IntegralHom

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The scalar tensor mate of normalized reduction is invertible on arbitrary inputs.
This assertion has no internal Hom, evaluation, or coefficient-duality conclusion.

Source: Stacks 03CZ, 05V4, 06YY and 07A4; integral Hom reduction, paragraph 2.
Proof: resolve the first input P by a K-flat complex. On complexes the balanced
contraction P tensor Res(Ext Q) to Res(Ext(P tensor Q)) sends
x tensor (s tensor y) to s tensor (x tensor y). The sheaf tensor cancellation
isomorphism proves it invertible, degreewise and then on signed total complexes.
For the derived calculation, resolve the restricted extension of the second
input again by a K-flat complex. The normalization square of mu on these two
K-flat pairs identifies its scalar adjunct with that contraction. The derived
scalar unit is the localized ordinary unit x to 1 tensor x, so the counit in the
displayed mate is precisely the contraction counit. Cancel the invertible K-flat
comparison maps. Naturality and localization extend the result to all inputs.
No boundedness, flatness of the quotient, or nonempty-site hypothesis is used.
(blueprint: lem-sf-reduction-tensor-strength-invertible). -/
theorem reductionTensorStrength_isIso
    (a : TensorPresentation.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl))
    (n : ℕ) (m : ReductionPresentation l E Y D hl a n)
    (K V : completedIntegralDerivedCategory l E Y D hl) :
    IsIso ((scalarTensorStrength a.tensor m.target.tensor
      (derivedScalarExtensionRestrictionAdjunction l E Y n).choose m.mu).app (K, V)) := by
  classical
  let adj := (derivedScalarExtensionRestrictionAdjunction l E Y n).choose
  have hK : ∃ P, CochainComplex.IsKFlatIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) P ∧
      Nonempty ((DerivedCategory.Q.obj P : completedIntegralDerivedCategory l E Y D hl) ≅ K) := by
    exact exists_reduction_kflat_representative
      (C := AlgebraicGeometry.Scheme.ProEt Y)
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) K
  obtain ⟨P, hP, ⟨eP⟩⟩ := hK
  have hV : ∃ Q, CochainComplex.IsKFlatIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) Q ∧
      Nonempty ((DerivedCategory.Q.obj Q : completedIntegralDerivedCategory l E Y D hl) ≅ V) := by
    exact exists_reduction_kflat_representative
      (C := AlgebraicGeometry.Scheme.ProEt Y)
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) V
  obtain ⟨Q, hQ, ⟨eQ⟩⟩ := hV
  let τ := scalarTensorStrength a.tensor m.target.tensor adj m.mu
  have hPQ : IsIso (τ.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) := by
    dsimp only [τ]
    rw [scalarTensorStrength_app]
    exact scalarTensorStrength_on_kflat_representatives l E Y D hl a n m P Q hP hQ
  let e : ((DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) :
      completedIntegralDerivedCategory l E Y D hl × completedIntegralDerivedCategory l E Y D hl) ⟶
      (K, V) :=
    Prod.mkHom eP.hom eQ.hom
  have : IsIso e := by
    dsimp [e]
    rw [isIso_prod_iff]
    constructor <;> infer_instance
  have hn := τ.naturality e
  have hright : IsIso (τ.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      (a.tensor ⋙ scalarReductionDerivedExtension l E Y n ⋙
        scalarReductionDerivedRestriction l E Y n).map e) := by
    infer_instance
  have hcomp : IsIso (((𝟭 _).prod
      (scalarReductionDerivedExtension l E Y n ⋙
        scalarReductionDerivedRestriction l E Y n) ⋙ a.tensor).map e ≫
      τ.app (K, V)) := by
    rw [hn]
    exact hright
  have hτ : IsIso (τ.app (K, V)) :=
    IsIso.of_isIso_comp_left
      (((𝟭 _).prod (scalarReductionDerivedExtension l E Y n ⋙
        scalarReductionDerivedRestriction l E Y n) ⋙ a.tensor).map e)
      (τ.app (K, V))
  simpa only [τ, adj] using hτ

end WeilConjectures.IntegralHom
