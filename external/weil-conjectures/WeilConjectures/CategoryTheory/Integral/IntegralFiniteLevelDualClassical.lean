/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralDerivedCoefficientData
public import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.Integral.ClassicalModuleDefinition
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom

import all WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
import WeilConjectures.CategoryTheory.Integral.IntegralConstantModelLocalResolution
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedLisseProEtaleLocality
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingTensorTor
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableShortExact
import WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientResolutionNormalization
import all WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
import WeilConjectures.SixFunctors.ProEtale.Comparison.ForgetUpperStar
import WeilConjectures.CategoryTheory.Integral.FiniteLevelScalarDescent
import WeilConjectures.CategoryTheory.Integral.FiniteLevelUniformizerMultiple
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMorphismDualizable
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalSheavesModules

/-!
# Classicality of the finite-level integral dual tensor

Source: `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-int-compactness/`
`sk-lem-int-ext-bound.proof.md`, second and third finite-reduction bullets
(blueprint: lem-sfb-integral-finite-level-dual-classical).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry Scheme
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem ab_classical_iso {X : Scheme.{u}}
    {M N : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} (e : M ≅ N)
    (hM : IsClassicalAbelian M) : IsClassicalAbelian N :=
  (ProEtale.isClassical_iso_iff
    ((sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).mapIso e)).mp hM

private theorem ab_classical_image (X : Scheme.{u})
    (M : Sheaf X.smallEtaleTopology Ab.{u + 1}) :
    IsClassicalAbelian ((comparisonUpperStar Ab.{u + 1} X).obj M) := by
  apply (classical_iff_counit X _).mpr
  infer_instance

private theorem integral_model_dualizable
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (S : Scheme.{u}) [IsNoetherian S]
    (L : supportModules (integralCoefficientRing l E) S)
    (hL : HasFiniteConstantLocalModel (integralCoefficientRing l E) S L) :
    IsDualizable ((DerivedCategory.singleFunctor _ 0).obj L) := by
  obtain ⟨U, hU⟩ := integral_constantModel_localResolution l E S L hL
  let Λ : Profinite.CondensedRing.{u} := ⟨integralCoefficientRing l E⟩
  apply (condensed_dualizable_iff_proetale_cover Λ S U
    ((DerivedCategory.singleFunctor _ 0).obj L)).mpr
  intro a
  obtain ⟨T, hT, h₁, h₂, ⟨e⟩⟩ := hU a
  have h := DerivedCategory.isDualizable_singleFunctor_obj_of_shortExact hT h₁ h₂
  exact h.of_iso
    ((DerivedCategory.singleFunctor _ 0).mapIso e ≪≫
      (((upperStar (integralCoefficientRing l E) (U.f a)).mapDerivedCategorySingleFunctor
        0).app L).symm)

private theorem finite_dualizable_tensor_classical
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [Finite A] [DiscreteTopology A]
    (S : Scheme.{u}) [IsNoetherian S]
    (K : DerivedCategory (FiniteDiscreteOrdinary.Internal A S)) (hK : IsDualizable K)
    (F : FiniteDiscreteOrdinary.Internal A S) (hF : IsClassicalAbelian F.X)
    (q : ℤ) :
    IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj
      (K ⊗ (DerivedCategory.singleFunctor _ 0).obj F)).X := by
  classical
  obtain ⟨e⟩ := FiniteDiscreteOrdinary.encoding_exists A S
  obtain ⟨m⟩ := (FiniteDiscreteOrdinary.encoding_tensor_tor A S e).1
  let := m
  let G := e.ordinary.functor ⋙ e.fixed.functor
  let U := sheafCompose (Scheme.ProEt.topology S)
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} A)) Ab.{u + 1})
  have underlying (M : FiniteDiscreteOrdinary.Internal A S) :
      U.obj (G.obj M) ≅ M.X := by
    dsimp only [G, Functor.comp_obj]
    rw [e.ordinary_functor, e.fixed_functor]
    exact ObjectProperty.isoMk _
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl))
  have hd : IsDualizable (e.fixedDerived.functor.obj K) :=
    hK.map e.fixedDerived.functor
  have hbc := (ProEtale.DerivedCategory.constructibleFiniteTor_of_isDualizable
    (ULift.{u + 1} A) hd).1
  obtain ⟨J, hJ, ⟨eJ⟩⟩ :=
    (ProEtale.DerivedCategory.boundedConstructible_iff _ _ _).mp hbc
  obtain ⟨_, _, _, _, _, origin⟩ := proEtaleClassicalSheavesModules S (ULift.{u + 1} A)
  have hGF : IsClassicalAbelian (U.obj (G.obj F)) :=
    ab_classical_iso (underlying F).symm hF
  have hGF' : IsClassical ((sheafCompose (Scheme.ProEt.topology S)
      (forget (ModuleCat.{u + 1} (ULift.{u + 1} A)))).obj (G.obj F)) := hGF
  obtain ⟨F', ⟨eF⟩⟩ := (origin (G.obj F)).mp hGF'
  let C := comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) S
  let P := (DerivedCategory.singleFunctor _ 0).obj F'
  let dF : C.mapDerivedCategory.obj P ≅
      e.fixedDerived.functor.obj ((DerivedCategory.singleFunctor _ 0).obj F) :=
    (C.mapDerivedCategorySingleFunctor 0).app F' ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso eF ≪≫
      ((G.mapDerivedCategorySingleFunctor 0).app F).symm
  let d : C.mapDerivedCategory.obj (J ⊗ P) ≅
      e.fixedDerived.functor.obj (K ⊗ (DerivedCategory.singleFunctor _ 0).obj F) :=
    (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso _ J).app P ≪≫
      tensorIso eJ dF ≪≫
      (Functor.Monoidal.μIso e.fixedDerived.functor _ _)
  let H := (DerivedCategory.homologyFunctor _ q).obj (J ⊗ P)
  let dH := (C.mapDerivedCategoryHomologyFunctorIso q).app (J ⊗ P) ≪≫
    (DerivedCategory.homologyFunctor _ q).mapIso d
  have hc : IsClassicalAbelian
      (U.obj ((DerivedCategory.homologyFunctor _ q).obj
        (G.mapDerivedCategory.obj (K ⊗ (DerivedCategory.singleFunctor _ 0).obj F)))) :=
    ab_classical_iso
      ((sheafComposeForget₂CompComparisonUpperStarIso (ULift.{u + 1} A) S).app H ≪≫
        U.mapIso dH) (ab_classical_image S _)
  let Z : DerivedCategory (FiniteDiscreteOrdinary.Internal A S) :=
    K ⊗ (DerivedCategory.singleFunctor _ 0).obj F
  let H₀ := (DerivedCategory.homologyFunctor (FiniteDiscreteOrdinary.Internal A S) q).obj Z
  let H₁ := (DerivedCategory.homologyFunctor
    (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} (ULift.{u + 1} A))) q).obj
      (G.mapDerivedCategory.obj Z)
  let eH : U.obj H₁ ≅ H₀.X :=
    U.mapIso ((G.mapDerivedCategoryHomologyFunctorIso q).app Z).symm ≪≫ underlying H₀
  exact @ab_classical_iso S (U.obj H₁) H₀.X eH (@hc)

private theorem integral_quotient_tensor_classical
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (S : Scheme.{u}) [IsNoetherian S] (n : ℕ)
    (D : integralDerived l E S) (hD : IsDualizable D)
    (F : supportModules (integralCoefficientRing l E) S)
    (B : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (DerivedNakayama.quotientRing l E (n + 1)) S))
    (eF : (Mod.comap
      (coefficientMap (DerivedNakayama.reductionRing l E (n + 1)) S)).obj B ≅ F)
    (hF : IsClassicalAbelian F.X) (q : ℤ) :
    IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj
      (D ⊗ (DerivedCategory.singleFunctor _ 0).obj F)).X := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let : TopologicalSpace (Padic.coefficientExtensionRing l E (n + 1)) :=
    AdicCompletion.finiteTopology l E (n + 1)
  let : DiscreteTopology (Padic.coefficientExtensionRing l E (n + 1)) :=
    DerivedNakayama.quotientDiscrete l E (n + 1)
  let φ := coefficientMap (DerivedNakayama.reductionRing l E (n + 1)) S
  let Q := (Mod.extendScalars φ).leftDerivedFunctor
  let R := Mod.comap (D := Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) φ
  let W := Mod.forget (D := Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
    (condensedRingObj (integralCoefficientRing l E) S)
  let := Mod.extendScalarsMonoidal φ
  let := (Mod.extendScalars φ).leftDerivedFunctorMonoidal
  let adj := Mod.derivedExtendMapDerivedCategoryAdjunction φ
  have hp := adj.isIso_leftProjectionMorphism_of_isDualizable hD
    ((DerivedCategory.singleFunctor _ 0).obj B)
  let := hp
  let d : D ⊗ (DerivedCategory.singleFunctor _ 0).obj F ≅
      R.mapDerivedCategory.obj
        (Q.obj D ⊗ (DerivedCategory.singleFunctor _ 0).obj B) :=
    tensorIso (Iso.refl _) ((R.mapDerivedCategorySingleFunctor 0).app B ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso eF).symm ≪≫
      asIso (adj.leftProjectionMorphism D ((DerivedCategory.singleFunctor _ 0).obj B))
  let : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    ((IntegralQuotient.integral_quotient_resolution_normalization l E).2.1 n).2.1
  have hB : IsClassicalAbelian B.X := ab_classical_iso (W.mapIso eF).symm hF
  have hc := @finite_dualizable_tensor_classical
    (Padic.coefficientExtensionRing l E (n + 1)) _ _ _ _ _ S _
    (Q.obj D) (hD.map Q) B (@hB) q
  exact @ab_classical_iso S _ _
    (W.mapIso ((R.mapDerivedCategoryHomologyFunctorIso q).app _) ≪≫
      W.mapIso ((DerivedCategory.homologyFunctor _ q).mapIso d.symm)) (@hc)

private def pointScalarMultiply
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (a : Padic.coefficientExtensionIntegers l E) :
    DerivedNakayama.integerRing l E ⟶ DerivedNakayama.integerRing l E := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  refine ⟨{ app := fun S ↦ ?_, naturality := ?_ }⟩
  · exact AddCommGrpCat.ofHom
      { toFun := fun x ↦ ULift.up ((ContinuousMap.const S.unop a) * x.down)
        map_zero' := by apply ULift.ext; exact mul_zero _
        map_add' := by intro x y; apply ULift.ext; exact mul_add _ _ _ }
  · intro S T g
    rfl

private theorem quotient_action_zero
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (S : Scheme.{u}) (n r : ℕ) (a : Padic.coefficientExtensionIntegers l E)
    (ha : Padic.coefficientExtensionUniformizer l E ^ (n + 1) = (l ^ r) * a)
    (F : supportModules (integralCoefficientRing l E) S)
    (hkill : (l ^ r) • 𝟙 F.X = 0) :
    (upperStarFromPoint S).map
        ((DerivedNakayama.uniformizerEnd l E ^ (n + 1)).asHom.hom) ▷ F.X ≫
      ModObj.smul (M := condensedRingObj (integralCoefficientRing l E) S) (X := F.X) = 0 := by
  have hpoint : (DerivedNakayama.uniformizerEnd l E ^ (n + 1)).asHom.hom =
      (l ^ r) • pointScalarMultiply l E a := by
    let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext T
    ext x
    apply ULift.ext
    apply ContinuousMap.ext
    intro t
    change (((DerivedNakayama.uniformizerEnd l E ^ (n + 1)).asHom.hom.hom.app T) x).down t =
      (l ^ r) • (a * x.down t)
    rw [DerivedNakayama.uniformizerPower_apply, ha, nsmul_eq_mul,
      Nat.cast_pow]
    exact _root_.mul_assoc _ _ _
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint S) :=
    (pointUpperStarLowerStarAdjunction.comp
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ S))).leftAdjoint_preservesColimits
  have : PreservesBinaryBiproducts (upperStarFromPoint S) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : (upperStarFromPoint S).Additive := Functor.additive_of_preservesBinaryBiproducts _
  change (tensorRight F.X).map ((upperStarFromPoint S).map
    ((DerivedNakayama.uniformizerEnd l E ^ (n + 1)).asHom.hom)) ≫ _ = 0
  rw [hpoint, Functor.map_nsmul, Functor.map_nsmul, Preadditive.nsmul_comp]
  calc
    _ = ((tensorRight F.X).map ((upperStarFromPoint S).map
        (pointScalarMultiply l E a)) ≫
        ModObj.smul (M := condensedRingObj (integralCoefficientRing l E) S) (X := F.X)) ≫
        ((l ^ r) • 𝟙 F.X) := by
      rw [Preadditive.comp_nsmul, Category.comp_id]
    _ = 0 := by rw [hkill, comp_zero]

/-- Finite-level classicality and annihilation of the ordinary integral dual tensor.

Source: latest blueprint, `sk-prop-int-compactness/sk-lem-int-ext-bound.proof.md`,
second and third finite-reduction bullets
(blueprint: lem-sfb-integral-finite-level-dual-classical).

Proof:
1. A finite constant integral model has a local two-term resolution by dualizable
   modules. Its degree-zero derived object is dualizable on every chart, hence globally
   by pro-etale descent. Its ordinary internal dual is therefore dualizable as well.
2. DVR factorization supplies a positive uniformizer power divisible by l^r. The actual
   continuous finite quotient by this power is a coefficient cokernel. Its kernel acts
   trivially on F, so the action descends to the quotient by the cokernel universal property.
3. Derived extension of scalars is strong monoidal and preserves dualizable objects.
   Under the normalized finite discrete coefficient equivalence, the reduced dual is
   dualizable over a finite ring. The published perfect local-model theorem makes it
   bounded constructible and of etale origin. The module comparison also descends F
   with its given quotient action, since its underlying sheaf is classical.
4. The monoidal derived comparison identifies their tensor with inverse image of the
   tensor on the etale site. Exact inverse image commutes with cohomology, giving
   classical underlying abelian cohomology sheaves in every degree.
5. The projection formula at the dualizable integral dual identifies the original tensor
   with exact scalar restriction of this finite tensor. Restriction leaves underlying
   abelian sheaves unchanged. Finally apply the additive composite of degree-zero
   inclusion, tensor by the dual, cohomology and forgetting scalars to l^r id_F = 0.
-/
theorem integral_finite_level_dual_classical
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (S : Scheme.{u}) [IsNoetherian S]
    (L : CategoryTheory.Mod
      (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (integralCoefficientRing l E) S))
    (hL : HasFiniteConstantLocalModel (integralCoefficientRing l E) S L)
    (F : CategoryTheory.Mod
      (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (integralCoefficientRing l E) S))
    (hF : IsClassicalAbelian F.X)
    (r : ℕ) (hr : 1 ≤ r)
    (hkill : (l ^ r) • 𝟙 F.X = 0) :
    ∀ q : ℤ,
      IsClassicalAbelian
        ((DerivedCategory.homologyFunctor _ q).obj
          (((derivedTensor (integralCoefficientRing l E) S).obj
            (((derivedHom (integralCoefficientRing l E) S).obj
              (op ((DerivedCategory.singleFunctor _ 0).obj L))).obj
              (𝟙_ (integralDerived l E S)))).obj
            ((DerivedCategory.singleFunctor _ 0).obj F))).X ∧
      (l ^ r) • 𝟙
        ((DerivedCategory.homologyFunctor _ q).obj
          (((derivedTensor (integralCoefficientRing l E) S).obj
            (((derivedHom (integralCoefficientRing l E) S).obj
              (op ((DerivedCategory.singleFunctor _ 0).obj L))).obj
              (𝟙_ (integralDerived l E S)))).obj
            ((DerivedCategory.singleFunctor _ 0).obj F))).X = 0 := by
  classical
  let Λ : Profinite.CondensedRing.{u} := ⟨integralCoefficientRing l E⟩
  let := condensedDerivedBraiding Λ S
  let D : integralDerived l E S := (((derivedHom (integralCoefficientRing l E) S).obj
    (op ((DerivedCategory.singleFunctor _ 0).obj L))).obj
      (𝟙_ (integralDerived l E S)))
  have hD : IsDualizable D := (integral_model_dualizable l E S L hL).ihom_unit
  obtain ⟨N, hN, a, ha⟩ := Padic.exists_uniformizer_power_multiple l E r hr
  let n := N - 1
  have hn : n + 1 = N := by omega
  have hzact := quotient_action_zero l E S n r a (by simpa only [hn] using ha) F hkill
  let W := Mod.forget (D := Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
    (condensedRingObj (integralCoefficientRing l E) S)
  let P := ShortComplex.mk (DerivedNakayama.uniformizerEnd l E ^ (n + 1)).asHom
    (DerivedNakayama.reductionHom l E (n + 1))
    (DerivedNakayama.reduction_zero l E (n + 1))
  let C := (P.map (DerivedNakayama.pullback l E S)).map W
  have hseq : C.ShortExact :=
    ((DerivedNakayama.pointResolution l E (n + 1)).map_of_exact
      (DerivedNakayama.pullback l E S)).map_of_exact W
  have hq : Epi (coefficientMap (DerivedNakayama.reductionRing l E (n + 1)) S) :=
    hseq.epi_g
  let := hq
  obtain ⟨B, ⟨eB⟩⟩ := Mod.exists_quotient_module
    (coefficientMap (DerivedNakayama.reductionRing l E (n + 1)) S)
    ((upperStarFromPoint S).map
      ((DerivedNakayama.uniformizerEnd l E ^ (n + 1)).asHom.hom)) C.zero hseq.exact F hzact
  intro q
  refine ⟨@integral_quotient_tensor_classical l _ E _ _ _ S _ n D hD F B eB (@hF) q, ?_⟩
  have hk : (l ^ r) • 𝟙 F = 0 := by
    apply Mod.hom_ext
    change (l ^ r) • 𝟙 F.X = 0
    exact hkill
  let : (tensorLeft D).Additive := DerivedCategory.additive_tensorLeft D
  let T : supportModules (integralCoefficientRing l E) S ⥤
      Sheaf (Scheme.ProEt.topology S) Ab.{u + 1} :=
    (DerivedCategory.singleFunctor (supportModules (integralCoefficientRing l E) S) 0) ⋙
      tensorLeft D ⋙
      DerivedCategory.homologyFunctor (supportModules (integralCoefficientRing l E) S) q ⋙ W
  calc
    _ = (l ^ r) • T.map (𝟙 F) :=
      congrArg (fun f ↦ (l ^ r) • f) (T.map_id F).symm
    _ = T.map ((l ^ r) • 𝟙 F) := T.map_nsmul.symm
    _ = T.map 0 := congrArg T.map hk
    _ = 0 := T.map_zero F F

end AlgebraicGeometry.ProEtale.CondensedRing
