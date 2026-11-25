/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedLineTensor.CompletedLineTensorOrdinaryData
public import WeilConjectures.SmoothPurity.CompletedLineTensor.CompletedScalarOrdinaryCoherence
public import WeilConjectures.FourierTransform.CompletedLineTensor.CompletedLineTensorComplete
public import WeilConjectures.SmoothPurity.CompletedLineTensor.CompletedLinePairData
import WeilConjectures.TraceFormula.Integral.IntegralScalarOrdinaryModelCoherence
import WeilConjectures.SmoothPurity.CompletedLineTensor.CompletedLineOrdinaryEvaluation
public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
public import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.DeligneLaumon.SfScalarExtensionComposition

public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.SmoothPurity.CompletedScalarAssociator.CompletedScalarAssociator
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import WeilConjectures.SmoothPurity.CompletedLineTensor.CompletedScalarIdentityUnit
import WeilConjectures.SmoothPurity.Derived.DerivedCompleteUnrestrictedIso
import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationComponentIso
import WeilConjectures.SmoothPurity.Supporting.Tensor.ExactTensorCoefficientLinear

/-! # Completed scalar extension and compatible coefficient lines

Source: Bhatt--Scholze, Definitions 3.4.10 and 3.5.2, Lemma 3.4.12,
Proposition 3.5.1; blueprint sk-def-sp-tate-twist-locally-free, Proof (3).
(blueprint: lem-pur-completed-line-tensor-coherence)

## Main definitions and statements

* `power`, `tensor`, `pairData`: signed lines and normalized ordinary comparisons.
* `beta`, `associator`, `unit`: conjugation by the recorded strict-completion comparison.
* `tower`, `beta_natural_evaluation`, `scalar_coherence`: the integral coherence equations.
* `rational_tower`, `rational_evaluation`, `rational_repeated`: their rationalized forms.
-/

@[expose] public noncomputable section
set_option Elab.async false
attribute [local instance 5000] CategoryTheory.HasSheafify.isRightAdjoint
attribute [local instance 5000] Algebra.toModule
attribute [local irreducible] Padic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local irreducible] HasDerivedCategory.standard
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
universe t u
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
namespace WeilConjectures
namespace CompletedLineTensor

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted completedCoefficientMap
  completedOrdinaryScalarExtension completedDerivedScalarExtension
  completedScalarCounit completedScalarTensorSection integralScalarExtensionOfUniverses
  completedScalarChangeData completedOrdinaryScalarComplex

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})
variable (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (ι : E →ₐ[ℚ_[l]] F)
variable (G : Type u) [Field G] [Algebra ℚ_[l] G] [FiniteDimensional ℚ_[l] G]
  (j : F →ₐ[ℚ_[l]] G)

/-- Existence and uniqueness of all ordinary signed-line comparisons with their
representative formulas. Source: Stacks 03EL, 03EO, 06YY; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: tensor powers of b use the canonical binary comparison, including its
multiplication unitor at zero. The negative map is uniquely determined by evaluation
and becomes an isomorphism after trivializing the line. Define the ordinary comparison
on pure tensors by ((x tensor a) tensor s) mapped to (x tensor s) tensor b_m(a tensor 1).
Balancedness and sheafification give an isomorphism natural in the module. A line is
flat; tensor with it preserves flat-term K-flat complexes. Apply the K-flat localization
equivalence, using the specified universal counits. The displayed equation fixes the
derived comparison uniquely and proves independence from the representative. -/
theorem pairData_existsUnique (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (N : integralTowerModules l F X) [N.IsFiniteLocallyFreeOfRank 1]
    (b : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N) :
    ∃! p : PairData l E X F ι L N, IsPairNormalized l E X F ι L N b p := by
  obtain ⟨d, hd, -⟩ := pairData_exists l E X F ι L N b
  exact ⟨d, hd, fun d' hd' ↦ pairData_unique l E X F ι L N b hd' hd⟩

/-- The unique normalized ordinary signed-line comparison package.
Source: blueprint Proof (3) (blueprint: lem-pur-completed-line-tensor-coherence). -/
def pairData (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (N : integralTowerModules l F X) [N.IsFiniteLocallyFreeOfRank 1]
    (b : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N) : PairData l E X F ι L N :=
  (pairData_existsUnique l E X F ι L N b).exists.choose

/-- The specified chi, viewed as an isomorphism only at a derived-complete input.
Source: Bhatt--Scholze, Proposition 3.5.1
(blueprint: lem-pur-completed-line-tensor-coherence). -/
def chi (K : DerivedCategory (integralTowerModules l E X))
    (hK : IsDerivedCompleteUnrestricted l E X K) :
    (completedDerivedScalarExtension l E F ι X).obj K ≅
      (integralScalarExtensionOfUniverses l E F ι X).obj K :=
  @asIso _ _ _ _ ((completedScalarComparison l E F ι X).app K)
    ((finiteFreeCompletedScalarComparison l E F ι X).2.1 K hK).1

/-- The completed comparison beta is exactly the specified conjugation by chi.
This construction uses no inverse chain map to completion.
Source: Bhatt--Scholze, Proposition 3.5.1; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence). -/
def beta (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (N : integralTowerModules l F X) [N.IsFiniteLocallyFreeOfRank 1]
    (b : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N)
    (m : ℤ) (K : DerivedCategory (integralTowerModules l E X))
    (hK : IsDerivedCompleteUnrestricted l E X K) :
    (integralScalarExtensionOfUniverses l E F ι X).obj ((tensor l E X L m).obj K) ≅
      (tensor l F X N m).obj ((integralScalarExtensionOfUniverses l E F ι X).obj K) :=
  (chi l E X F ι _ (complete l E X L m K hK)).symm ≪≫
    ((pairData l E X F ι L N b).ordinary m).app K ≪≫
      (tensor l F X N m).mapIso (chi l E X F ι K hK)

attribute [local irreducible] beta chi pairData

attribute [local semireducible] completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted

private theorem complete_of_iso
    {K M : DerivedCategory (integralTowerModules l E X)} (e : K ≅ M)
    (hK : IsDerivedCompleteUnrestricted l E X K) :
    IsDerivedCompleteUnrestricted l E X M := by
  exact isDerivedCompleteUnrestricted_of_iso l E X e hK

/-- Completed extension preserves completeness on complete inputs.
Source: Bhatt--Scholze, Proposition 3.5.1
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: the finite-free comparison makes ordinary extension complete and identifies
it with the specified strict completion. Transport its augmented Roos triangle through
that isomorphism, with the canonical quotient legs. -/
theorem extension_complete (K : DerivedCategory (integralTowerModules l E X))
    (hK : IsDerivedCompleteUnrestricted l E X K) :
    IsDerivedCompleteUnrestricted l F X
      ((integralScalarExtensionOfUniverses l E F ι X).obj K) := by
  exact complete_of_iso l F X (chi l E X F ι K hK)
    ((finiteFreeCompletedScalarComparison l E F ι X).2.1 K hK).2

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted

/-- The completed associator is ordinary associativity conjugated by the specified chi.
Source: Bhatt--Scholze, Proposition 3.5.1; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence). -/
def associator (K : DerivedCategory (integralTowerModules l E X))
    (hK : IsDerivedCompleteUnrestricted l E X K) :
    (integralScalarExtensionOfUniverses l F G j X).obj
        ((integralScalarExtensionOfUniverses l E F ι X).obj K) ≅
      (integralScalarExtensionOfUniverses l E G (j.comp ι) X).obj K :=
  (chi l F X G j _ (extension_complete l E X F ι K hK)).symm ≪≫
    (completedDerivedScalarExtension l F G j X).mapIso (chi l E X F ι K hK).symm ≪≫
    (associatorData l E X F ι G j).derived.app K ≪≫ chi l E X G (j.comp ι) K hK

attribute [local irreducible] associator associatorData

private theorem conjugate_evaluation {A D : Type*} [Category A] [Category D]
    (B C : A ⥤ D) (T S : A ⥤ A) (V W : D ⥤ D)
    (e : T ⋙ S ⟶ 𝟭 A) (f : V ⋙ W ⟶ 𝟭 D) (K : A)
    (x : B.obj K ≅ C.obj K) (y : B.obj (T.obj K) ≅ C.obj (T.obj K))
    (z : B.obj (S.obj (T.obj K)) ≅ C.obj (S.obj (T.obj K)))
    (p : B.obj (T.obj K) ⟶ V.obj (B.obj K))
    (q : B.obj (S.obj (T.obj K)) ⟶ W.obj (B.obj (T.obj K)))
    (ho : q ≫ W.map p ≫ f.app (B.obj K) = B.map (e.app K))
    (hc : B.map (e.app K) ≫ x.hom = z.hom ≫ C.map (e.app K)) :
    (z.inv ≫ q ≫ W.map y.hom) ≫ W.map (y.inv ≫ p ≫ V.map x.hom) ≫
      f.app (C.obj K) = C.map (e.app K) := by
  simp only [Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_assoc]
  simp only [Functor.map_comp, Category.assoc]
  have hn := f.naturality x.hom
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [hn]
  rw [← Category.assoc (W.map p), ← Category.assoc q, ho]
  apply (cancel_epi z.hom).mp
  simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp] using hc

/- Naturality and compatibility with evaluation for exactly the conjugated beta.
Source: blueprint Proof (3), completed line/scalar coherence
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: every factor defining beta is natural and invertible on complete inputs;
completeness of all intermediate twists follows from complete. To check evaluation,
precompose by chi at T_-m T_m K. Substitute beta*chi_T = T(chi)*bar-beta twice.
Naturality of evaluation moves chi outside. On ordinary pure tensors both paths
are multiplication by the evaluated line scalar, by the negative clause of
IsPairNormalized. Naturality
of chi identifies this with C(epsilon)*chi. Cancel the invertible chi. The proof
includes zero, positive and negative m and never inverts a chain completion map. -/
/-- The evaluation component of beta compatibility, isolated from naturality.
Source: blueprint Proof (3), completed line/scalar coherence
(blueprint: new-lem-pur-beta-evaluation-compatibility).
Proof: expand both conjugated beta maps and the derived evaluation. Naturality
of chi cancels the completion comparisons. The normalized pairing equation in
`IsPairNormalized` identifies the remaining ordinary pure-tensor map; the
localization comparison then gives the displayed equality. -/
theorem beta_evaluation_compatibility (L : integralTowerModules l E X)
    [L.IsFiniteLocallyFreeOfRank 1] (N : integralTowerModules l F X)
    [N.IsFiniteLocallyFreeOfRank 1]
    (b : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N) :
    ∀ (m : ℤ) (K : DerivedCategory (integralTowerModules l E X))
      (hK : IsDerivedCompleteUnrestricted l E X K),
      (beta l E X F ι L N b (-m) ((tensor l E X L m).obj K)
          (complete l E X L m K hK)).hom ≫
        (tensor l F X N (-m)).map (beta l E X F ι L N b m K hK).hom ≫
        (epsilon l F X N m).hom.app
          ((integralScalarExtensionOfUniverses l E F ι X).obj K) =
      (integralScalarExtensionOfUniverses l E F ι X).map
        ((epsilon l E X L m).hom.app K) := by
  intro m K hK
  have hd : IsPairNormalized l E X F ι L N b (pairData l E X F ι L N b) := by
    unfold pairData
    exact (pairData_existsUnique l E X F ι L N b).exists.choose_spec
  have ho := ordinary_evaluation_compatibility l E X F ι L N b
    (pairData l E X F ι L N b) hd m K
  have hc := (completedScalarComparison l E F ι X).naturality
    ((epsilon l E X L m).hom.app K)
  simpa only [beta, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom] using
    conjugate_evaluation
      (completedDerivedScalarExtension l E F ι X)
      (integralScalarExtensionOfUniverses l E F ι X)
      (tensor l E X L m) (tensor l E X L (-m))
      (tensor l F X N m) (tensor l F X N (-m))
      (epsilon l E X L m).hom (epsilon l F X N m).hom K
      (chi l E X F ι K hK)
      (chi l E X F ι _ (complete l E X L m K hK))
      (chi l E X F ι _
        (complete l E X L (-m) _ (complete l E X L m K hK)))
      (((pairData l E X F ι L N b).ordinary m).hom.app K)
      (((pairData l E X F ι L N b).ordinary (-m)).hom.app
        ((tensor l E X L m).obj K)) ho
      (by simpa only [chi, asIso_hom, Functor.comp_obj, Functor.id_obj] using hc)

theorem beta_natural_evaluation (L : integralTowerModules l E X)
    [L.IsFiniteLocallyFreeOfRank 1] (N : integralTowerModules l F X)
    [N.IsFiniteLocallyFreeOfRank 1]
    (b : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N) :
    (∀ (m : ℤ) (K M : DerivedCategory (integralTowerModules l E X))
      (hK : IsDerivedCompleteUnrestricted l E X K)
      (hM : IsDerivedCompleteUnrestricted l E X M) (f : K ⟶ M),
      (integralScalarExtensionOfUniverses l E F ι X).map ((tensor l E X L m).map f) ≫
          (beta l E X F ι L N b m M hM).hom =
        (beta l E X F ι L N b m K hK).hom ≫
          (tensor l F X N m).map ((integralScalarExtensionOfUniverses l E F ι X).map f)) ∧
    (∀ (m : ℤ) (K : DerivedCategory (integralTowerModules l E X))
      (hK : IsDerivedCompleteUnrestricted l E X K),
      (beta l E X F ι L N b (-m) ((tensor l E X L m).obj K)
          (complete l E X L m K hK)).hom ≫
        (tensor l F X N (-m)).map (beta l E X F ι L N b m K hK).hom ≫
        (epsilon l F X N m).hom.app ((integralScalarExtensionOfUniverses l E F ι X).obj K) =
      (integralScalarExtensionOfUniverses l E F ι X).map ((epsilon l E X L m).hom.app K)) := by
  constructor
  · intro m K M hK hM f
    unfold beta
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
    have hχinv :
        (integralScalarExtensionOfUniverses l E F ι X).map
            ((tensor l E X L m).map f) ≫
            (chi l E X F ι ((tensor l E X L m).obj M)
              (complete l E X L m M hM)).inv =
          (chi l E X F ι ((tensor l E X L m).obj K)
              (complete l E X L m K hK)).inv ≫
            (completedDerivedScalarExtension l E F ι X).map
              ((tensor l E X L m).map f) := by
      apply (cancel_mono (chi l E X F ι ((tensor l E X L m).obj M)
        (complete l E X L m M hM)).hom).1
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      unfold chi
      simp only [CategoryTheory.asIso_hom]
      rw [(completedScalarComparison l E F ι X).naturality]
      simp only [CategoryTheory.asIso_inv]
      rw [CategoryTheory.IsIso.inv_hom_id_assoc]
    have hd := ((pairData l E X F ι L N b).ordinary m).hom.naturality f
    simp only [Functor.comp_map] at hd
    have hd' :
        (completedDerivedScalarExtension l E F ι X).map
            ((tensor l E X L m).map f) ≫
            ((pairData l E X F ι L N b).ordinary m).hom.app M =
          ((pairData l E X F ι L N b).ordinary m).hom.app K ≫
            (tensor l F X N m).map
              ((completedDerivedScalarExtension l E F ι X).map f) := by
      simpa using hd
    have hχordinary :
        (completedDerivedScalarExtension l E F ι X).map f ≫
            (chi l E X F ι M hM).hom =
          (chi l E X F ι K hK).hom ≫
            (integralScalarExtensionOfUniverses l E F ι X).map f := by
      unfold chi
      simp only [CategoryTheory.asIso_hom]
      exact (completedScalarComparison l E F ι X).naturality _
    have happM :
        (((pairData l E X F ι L N b).ordinary m).app M).hom =
          ((pairData l E X F ι L N b).ordinary m).hom.app M := rfl
    have happK :
        (((pairData l E X F ι L N b).ordinary m).app K).hom =
          ((pairData l E X F ι L N b).ordinary m).hom.app K := rfl
    rw [happM, happK]
    calc
      (integralScalarExtensionOfUniverses l E F ι X).map
          ((tensor l E X L m).map f) ≫
          (chi l E X F ι ((tensor l E X L m).obj M)
            (complete l E X L m M hM)).inv ≫
          ((pairData l E X F ι L N b).ordinary m).hom.app M ≫
          (tensor l F X N m).map
            (chi l E X F ι M hM).hom =
        ((integralScalarExtensionOfUniverses l E F ι X).map
            ((tensor l E X L m).map f) ≫
          (chi l E X F ι ((tensor l E X L m).obj M)
            (complete l E X L m M hM)).inv) ≫
          ((pairData l E X F ι L N b).ordinary m).hom.app M ≫
          (tensor l F X N m).map
            (chi l E X F ι M hM).hom := by
            simp only [Category.assoc]
      _ = ((chi l E X F ι ((tensor l E X L m).obj K)
          (complete l E X L m K hK)).inv ≫
          (completedDerivedScalarExtension l E F ι X).map
            ((tensor l E X L m).map f)) ≫
          ((pairData l E X F ι L N b).ordinary m).hom.app M ≫
          (tensor l F X N m).map
            (chi l E X F ι M hM).hom := by
            rw [hχinv]
      _ = (chi l E X F ι ((tensor l E X L m).obj K)
          (complete l E X L m K hK)).inv ≫
          ((completedDerivedScalarExtension l E F ι X).map
            ((tensor l E X L m).map f) ≫
            ((pairData l E X F ι L N b).ordinary m).hom.app M) ≫
          (tensor l F X N m).map
            (chi l E X F ι M hM).hom := by
            simp only [Category.assoc]
      _ = (chi l E X F ι ((tensor l E X L m).obj K)
          (complete l E X L m K hK)).inv ≫
          (((pairData l E X F ι L N b).ordinary m).hom.app K ≫
            (tensor l F X N m).map
              ((completedDerivedScalarExtension l E F ι X).map f)) ≫
          (tensor l F X N m).map
            (chi l E X F ι M hM).hom := by
            rw [hd']
      _ = (chi l E X F ι ((tensor l E X L m).obj K)
          (complete l E X L m K hK)).inv ≫
          ((pairData l E X F ι L N b).ordinary m).hom.app K ≫
          (tensor l F X N m).map
            ((completedDerivedScalarExtension l E F ι X).map f ≫
              (chi l E X F ι M hM).hom) := by
            simp only [Category.assoc, ← Functor.map_comp]
      _ = (chi l E X F ι ((tensor l E X L m).obj K)
          (complete l E X L m K hK)).inv ≫
          ((pairData l E X F ι L N b).ordinary m).hom.app K ≫
          (tensor l F X N m).map
            ((chi l E X F ι K hK).hom ≫
              (integralScalarExtensionOfUniverses l E F ι X).map f) := by
            rw [hχordinary]
      _ = (chi l E X F ι ((tensor l E X L m).obj K)
          (complete l E X L m K hK)).inv ≫
          ((pairData l E X F ι L N b).ordinary m).hom.app K ≫
          (tensor l F X N m).map (chi l E X F ι K hK).hom ≫
          (tensor l F X N m).map
            ((integralScalarExtensionOfUniverses l E F ι X).map f) := by
            simp only [Functor.map_comp]
  · exact beta_evaluation_compatibility l E X F ι L N b

/-- The completed identity comparison is the unitor conjugated by chi.
Source: Bhatt--Scholze, Proposition 3.5.1
(blueprint: lem-pur-completed-line-tensor-coherence). -/
def unit (K : DerivedCategory (integralTowerModules l E X))
    (hK : IsDerivedCompleteUnrestricted l E X K) :
    (integralScalarExtensionOfUniverses l E E (AlgHom.id ℚ_[l] E) X).obj K ≅ K :=
  (chi l E X E (AlgHom.id ℚ_[l] E) K hK).symm ≪≫ (ordinaryUnit l E X).app K

attribute [local irreducible] unit ordinaryUnit

attribute [local semireducible] unit ordinaryUnit chi

private theorem line_unit_conjugation
    {C : Type*} [Category C] {A B A' B' K M : C}
    (cK : A ≅ B) (cM : A' ≅ B') (uK : A ⟶ K) (uM : A' ⟶ M)
    (f : A ⟶ A') (g : B ⟶ B') (k : K ⟶ M)
    (hc : f ≫ cM.hom = cK.hom ≫ g) (hu : f ≫ uM = uK ≫ k) :
    g ≫ (cM.inv ≫ uM) = (cK.inv ≫ uK) ≫ k := by
  have hc' : g ≫ cM.inv = cK.inv ≫ f := by
    apply (cK.eq_inv_comp).mpr
    rw [← Category.assoc, ← hc, Category.assoc, cM.hom_inv_id, Category.comp_id]
  calc
    g ≫ (cM.inv ≫ uM) = (g ≫ cM.inv) ≫ uM := (Category.assoc _ _ _).symm
    _ = (cK.inv ≫ f) ≫ uM := congrArg (fun z ↦ z ≫ uM) hc'
    _ = (cK.inv ≫ uK) ≫ k := by rw [Category.assoc, hu, Category.assoc]

/-- The inverse completed unit is exactly the natural completeness map, including
its zero shifted-product component, and is natural on complete inputs.
Source: Bhatt--Scholze, Definition 3.5.2; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: the finite-free comparison identifies chi with the chain multiplication
followed by the directly constructed quotient augmentation. Substitute the unitor's
normalization and cancel multiplication. This gives the displayed representative
formula. Naturality follows from the naturality of chi and ordinary multiplication. -/
theorem unit_normalization :
    (∀ (P : (integralOperationsGoodComplex l E X).FullSubcategory)
      (hP : IsDerivedCompleteUnrestricted l E X (DerivedCategory.Q.obj P.obj)),
      (unit l E X (DerivedCategory.Q.obj P.obj) hP).inv ≫
          (integralScalarExtensionComparisonOfUniverses l E E (AlgHom.id ℚ_[l] E) X).hom.app P =
        DerivedCategory.Q.map ((completedScalarIdentityUnit l E X).app P.obj)) ∧
    (∀ (K M : DerivedCategory (integralTowerModules l E X))
      (hK : IsDerivedCompleteUnrestricted l E X K)
      (hM : IsDerivedCompleteUnrestricted l E X M) (f : K ⟶ M),
      (integralScalarExtensionOfUniverses l E E (AlgHom.id ℚ_[l] E) X).map f ≫
          (unit l E X M hM).hom = (unit l E X K hK).hom ≫ f) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    constructor
    · intro P hP
      have hχ := (finiteFreeCompletedScalarComparison l E E (AlgHom.id ℚ_[l] E) X).2.2 P
      have hμ := (ordinaryUnit_existsUnique l E X).exists.choose_spec P
      change (ordinaryUnit l E X).hom.app _ = _ at hμ
      change ((ordinaryUnit l E X).inv.app _ ≫
        (completedScalarComparison l E E (AlgHom.id ℚ_[l] E) X).app _) ≫ _ = _
      rw [Category.assoc]
      have hχ' :
          (completedScalarComparison l E E (AlgHom.id ℚ_[l] E) X).app
              (DerivedCategory.Q.obj P.obj) ≫
              (integralScalarExtensionComparisonOfUniverses l E E
                (AlgHom.id ℚ_[l] E) X).hom.app P =
            (ordinaryUnit l E X).hom.app (DerivedCategory.Q.obj P.obj) ≫
              DerivedCategory.Q.map ((completedScalarIdentityUnit l E X).app P.obj) := by
        rw [hμ, Category.assoc]
        exact hχ
      erw [hχ']
      simp only [Iso.inv_hom_id_app_assoc]
    · intro K M hK hM f
      exact line_unit_conjugation
        (chi l E X E (AlgHom.id ℚ_[l] E) K hK)
        (chi l E X E (AlgHom.id ℚ_[l] E) M hM)
        ((ordinaryUnit l E X).hom.app K) ((ordinaryUnit l E X).hom.app M)
        ((completedDerivedScalarExtension l E E (AlgHom.id ℚ_[l] E) X).map f)
        ((integralScalarExtensionOfUniverses l E E (AlgHom.id ℚ_[l] E) X).map f) f
        ((completedScalarComparison l E E (AlgHom.id ℚ_[l] E) X).naturality f)
        ((ordinaryUnit l E X).hom.naturality f)

/-- Conjugating the image of a morphism by the components of a natural comparison
recovers its image under the target functor.
Source: blueprint Proof (3) (blueprint: lem-pur-completed-line-tensor-coherence). -/
private theorem conj_map {A B : Type*} [Category A] [Category B] {C C' : A ⥤ B}
    (χ : C ⟶ C') {K M : A} (eK : C.obj K ≅ C'.obj K) (eM : C.obj M ≅ C'.obj M)
    (hK : eK.hom = χ.app K) (hM : eM.hom = χ.app M) (f : K ⟶ M) :
    eK.inv ≫ C.map f ≫ eM.hom = C'.map f := by
  rw [hM, χ.naturality, ← hK, Iso.inv_hom_id_assoc]

/-- The inverse form of `conj_map`.
Source: blueprint Proof (3) (blueprint: lem-pur-completed-line-tensor-coherence). -/
private theorem conj_map_inv {A B : Type*} [Category A] [Category B] {C C' : A ⥤ B}
    (χ : C ⟶ C') {K M : A} (eK : C.obj K ≅ C'.obj K) (eM : C.obj M ≅ C'.obj M)
    (hK : eK.hom = χ.app K) (hM : eM.hom = χ.app M) (f : K ⟶ M) :
    C'.map f ≫ eM.inv = eK.inv ≫ C.map f := by
  rw [Iso.comp_inv_eq, Category.assoc, conj_map χ eK eM hK hM f]

/-- A pentagon for associators conjugated by comparison isomorphisms follows from the
pentagon of the original associators.
Source: blueprint Proof (3) (blueprint: lem-pur-completed-line-tensor-coherence).
Proof: move the outer comparison inside by naturality, cancel the inverse pairs and
apply the original pentagon and naturality of the third associator. -/
private theorem conj_pentagon {A B C D : Type*} [Category A] [Category B] [Category C]
    [Category D] {F₁ : A ⥤ B} {F₂ : B ⥤ C} {F₃ F₃' : C ⥤ D} {F₁₂ : A ⥤ C} {F₂₃ : B ⥤ D}
    {F₁₂₃ : A ⥤ D} (χ₃ : F₃ ⟶ F₃')
    (a : F₁ ⋙ F₂ ⟶ F₁₂) (b : F₁₂ ⋙ F₃ ⟶ F₁₂₃) (c : F₂ ⋙ F₃ ⟶ F₂₃) (d : F₁ ⋙ F₂₃ ⟶ F₁₂₃)
    {K : A} {K₁ : B} {K₂ K₁₂ : C} {K₁₂₃ K₂₃ : D}
    (e₁ : F₁.obj K ≅ K₁) (e₂ : F₂.obj K₁ ≅ K₂) (e₃ : F₁₂.obj K ≅ K₁₂)
    (e₄ : F₃.obj K₁₂ ≅ F₃'.obj K₁₂) (e₅ : F₁₂₃.obj K ≅ K₁₂₃)
    (e₆ : F₃.obj K₂ ≅ F₃'.obj K₂) (e₇ : F₂₃.obj K₁ ≅ K₂₃)
    (h₄ : e₄.hom = χ₃.app K₁₂) (h₆ : e₆.hom = χ₃.app K₂)
    (hp : F₃.map (a.app K) ≫ b.app K = c.app (F₁.obj K) ≫ d.app K) :
    F₃'.map (e₂.inv ≫ F₂.map e₁.inv ≫ a.app K ≫ e₃.hom) ≫
        (e₄.inv ≫ F₃.map e₃.inv ≫ b.app K ≫ e₅.hom) =
      (e₆.inv ≫ F₃.map e₂.inv ≫ c.app K₁ ≫ e₇.hom) ≫
        (e₇.inv ≫ F₂₃.map e₁.inv ≫ d.app K ≫ e₅.hom) := by
  have h₁ := conj_map_inv χ₃ e₆ e₄ h₆ h₄ (e₂.inv ≫ F₂.map e₁.inv ≫ a.app K ≫ e₃.hom)
  have hc := c.naturality e₁.inv
  simp only [Functor.comp_map] at hc
  calc _ = (F₃'.map (e₂.inv ≫ F₂.map e₁.inv ≫ a.app K ≫ e₃.hom) ≫ e₄.inv) ≫
          F₃.map e₃.inv ≫ b.app K ≫ e₅.hom := by simp only [Category.assoc]
    _ = (e₆.inv ≫ F₃.map (e₂.inv ≫ F₂.map e₁.inv ≫ a.app K ≫ e₃.hom)) ≫
          F₃.map e₃.inv ≫ b.app K ≫ e₅.hom := by rw [h₁]
    _ = _ := by
      simp only [Functor.map_comp, Category.assoc]
      rw [← F₃.map_comp_assoc e₃.hom e₃.inv, Iso.hom_inv_id, F₃.map_id, Category.id_comp,
        reassoc_of% hp, reassoc_of% hc, Iso.hom_inv_id_assoc]

/-- A tower identity for line comparisons conjugated by comparison isomorphisms follows
from the original tower identity.
Source: blueprint Proof (3) (blueprint: lem-pur-completed-line-tensor-coherence).
Proof: move the outer comparison inside by naturality, use naturality of the second line
comparison, cancel the inverse pairs and apply the original tower identity. -/
private theorem conj_tower {A B C : Type*} [Category A] [Category B] [Category C]
    {T₀ : A ⥤ A} {T₁ : B ⥤ B} {T₂ : C ⥤ C} {F₁ : A ⥤ B} {F₂ F₂' : B ⥤ C} {F₁₂ : A ⥤ C}
    (χ₂ : F₂ ⟶ F₂') (o₁ : T₀ ⋙ F₁ ⟶ F₁ ⋙ T₁) (o₂ : T₁ ⋙ F₂ ⟶ F₂ ⋙ T₂)
    (o₁₂ : T₀ ⋙ F₁₂ ⟶ F₁₂ ⋙ T₂) (a : F₁ ⋙ F₂ ⟶ F₁₂)
    {K : A} {K₁ K₁T : B} {K₁₂ K₁₂T : C}
    (e₁ : F₁.obj K ≅ K₁) (e₁' : F₁.obj (T₀.obj K) ≅ K₁T)
    (e₂ : F₂.obj (T₁.obj K₁) ≅ F₂'.obj (T₁.obj K₁)) (e₂' : F₂.obj K₁ ≅ F₂'.obj K₁)
    (e₃ : F₁₂.obj K ≅ K₁₂) (e₄ : F₂.obj K₁T ≅ F₂'.obj K₁T) (e₅ : F₁₂.obj (T₀.obj K) ≅ K₁₂T)
    (h₂ : e₂.hom = χ₂.app _) (h₄ : e₄.hom = χ₂.app _)
    (ht : F₂.map (o₁.app K) ≫ o₂.app (F₁.obj K) ≫ T₂.map (a.app K) =
      a.app (T₀.obj K) ≫ o₁₂.app K) :
    F₂'.map (e₁'.inv ≫ o₁.app K ≫ T₁.map e₁.hom) ≫
        (e₂.inv ≫ o₂.app K₁ ≫ T₂.map e₂'.hom) ≫
        T₂.map (e₂'.inv ≫ F₂.map e₁.inv ≫ a.app K ≫ e₃.hom) =
      (e₄.inv ≫ F₂.map e₁'.inv ≫ a.app (T₀.obj K) ≫ e₅.hom) ≫
        (e₅.inv ≫ o₁₂.app K ≫ T₂.map e₃.hom) := by
  have h₁ := conj_map_inv χ₂ e₄ e₂ h₄ h₂ (e₁'.inv ≫ o₁.app K ≫ T₁.map e₁.hom)
  have hn := o₂.naturality e₁.hom
  simp only [Functor.comp_map] at hn
  calc _ = (F₂'.map (e₁'.inv ≫ o₁.app K ≫ T₁.map e₁.hom) ≫ e₂.inv) ≫ o₂.app K₁ ≫
          T₂.map e₂'.hom ≫ T₂.map (e₂'.inv ≫ F₂.map e₁.inv ≫ a.app K ≫ e₃.hom) := by
        simp only [Category.assoc]
    _ = (e₄.inv ≫ F₂.map (e₁'.inv ≫ o₁.app K ≫ T₁.map e₁.hom)) ≫ o₂.app K₁ ≫
          T₂.map e₂'.hom ≫ T₂.map (e₂'.inv ≫ F₂.map e₁.inv ≫ a.app K ≫ e₃.hom) := by rw [h₁]
    _ = _ := by
      simp only [Functor.map_comp, Category.assoc]
      rw [← T₂.map_comp_assoc e₂'.hom e₂'.inv, Iso.hom_inv_id, T₂.map_id, Category.id_comp,
        reassoc_of% hn, ← T₂.map_comp_assoc (F₂.map e₁.hom) (F₂.map e₁.inv), ← F₂.map_comp,
        Iso.hom_inv_id, F₂.map_id, T₂.map_id, Category.id_comp, reassoc_of% ht,
        Iso.hom_inv_id_assoc]

/-- Both unit laws and the scalar associativity pentagon on derived-complete inputs.
Source: Stacks 06YY, 07A4; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: ordinary associators multiply the scalar factors. For three transitions both
routes send u tensor (t tensor (s tensor x)) to u*k(t)*k(j(s)) tensor x. Multiplication
units obey both unit laws. These identities descend from pure tensors through
sheafification and K-flat localization. Conjugating by successive chi maps identifies
the completed and ordinary composites. Expand each completed edge, move intermediate
chi maps by naturality and cancel inverse pairs. This reduces the completed pentagon
and both unit equations to the ordinary ones. Repeated fields use the actual unit
isomorphisms, including their natural completeness maps, and no strict equality C_ii=1. -/
theorem scalar_coherence :
    (∀ (K : DerivedCategory (integralTowerModules l E X))
      (hK : IsDerivedCompleteUnrestricted l E X K),
      (associator l E X E (AlgHom.id ℚ_[l] E) F ι K hK).hom =
        (integralScalarExtensionOfUniverses l E F ι X).map (unit l E X K hK).hom) ∧
    (∀ (K : DerivedCategory (integralTowerModules l E X))
      (hK : IsDerivedCompleteUnrestricted l E X K),
      (associator l E X F ι F (AlgHom.id ℚ_[l] F) K hK).hom =
        (unit l F X ((integralScalarExtensionOfUniverses l E F ι X).obj K)
          (extension_complete l E X F ι K hK)).hom) ∧
    (∀ (H : Type u) [Field H] [Algebra ℚ_[l] H] [FiniteDimensional ℚ_[l] H]
      (k : G →ₐ[ℚ_[l]] H) (K : DerivedCategory (integralTowerModules l E X))
      (hK : IsDerivedCompleteUnrestricted l E X K),
      (integralScalarExtensionOfUniverses l G H k X).map
          (associator l E X F ι G j K hK).hom ≫
        (associator l E X G (j.comp ι) H k K hK).hom =
      (associator l F X G j H k ((integralScalarExtensionOfUniverses l E F ι X).obj K)
          (extension_complete l E X F ι K hK)).hom ≫
        (associator l E X F ι H (k.comp j) K hK).hom) := by
  refine ⟨fun K hK ↦ ?_, fun K hK ↦ ?_, fun H _ _ _ k K hK ↦ ?_⟩
  · unfold associator unit
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom]
    rw [associatorData_derived_source_unit]
    have hc := conj_map (completedScalarComparison l E F ι X)
      (chi l E X F ι _ (extension_complete l E X E (AlgHom.id ℚ_[l] E) K hK))
      (chi l E X F ι K hK) rfl rfl
      ((chi l E X E (AlgHom.id ℚ_[l] E) K hK).inv ≫ (ordinaryUnit l E X).hom.app K)
    rw [Functor.map_comp, Category.assoc] at hc
    exact hc
  · unfold associator unit
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom]
    rw [associatorData_derived_target_unit]
    have hn := (ordinaryUnit l F X).hom.naturality (chi l E X F ι K hK).inv
    dsimp only [Functor.id_map, Functor.id_obj] at hn
    have h₂ : (completedDerivedScalarExtension l F F (AlgHom.id ℚ_[l] F) X).map
          (chi l E X F ι K hK).inv ≫
        (ordinaryUnit l F X).hom.app ((completedDerivedScalarExtension l E F ι X).obj K) ≫
          (chi l E X F ι K hK).hom =
        (ordinaryUnit l F X).hom.app ((integralScalarExtensionOfUniverses l E F ι X).obj K) := by
      rw [reassoc_of% hn, Iso.inv_hom_id, Category.comp_id]
    exact congrArg (fun z ↦ (chi l F X F (AlgHom.id ℚ_[l] F) _
      (extension_complete l E X F ι K hK)).inv ≫ z) h₂
  · unfold associator
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom]
    exact conj_pentagon (completedScalarComparison l G H k X)
      (associatorData l E X F ι G j).derived.hom
      (associatorData l E X G (j.comp ι) H k).derived.hom
      (associatorData l F X G j H k).derived.hom
      (associatorData l E X F ι H (k.comp j)).derived.hom
      (chi l E X F ι K hK)
      (chi l F X G j _ (extension_complete l E X F ι K hK))
      (chi l E X G (j.comp ι) K hK)
      (chi l G X H k _ (extension_complete l E X G (j.comp ι) K hK))
      (chi l E X H (k.comp (j.comp ι)) K hK)
      (chi l G X H k _ (extension_complete l F X G j _ (extension_complete l E X F ι K hK)))
      (chi l F X H (k.comp j) _ (extension_complete l E X F ι K hK)) rfl rfl
      (associatorData_derived_pentagon l E X F ι G j H k K)

/-- The chosen ordinary comparison package is normalized.
Source: blueprint Proof (3) (blueprint: lem-pur-completed-line-tensor-coherence). -/
private theorem pairData_normalized (L : integralTowerModules l E X)
    [L.IsFiniteLocallyFreeOfRank 1] (N : integralTowerModules l F X)
    [N.IsFiniteLocallyFreeOfRank 1]
    (b : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N) :
    IsPairNormalized l E X F ι L N b (pairData l E X F ι L N b) := by
  unfold pairData
  exact (pairData_existsUnique l E X F ι L N b).exists.choose_spec

/-- The completed line comparison commutes with a compatible three-field tower.
Source: blueprint Proof (3), final sentence
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: the signed-power scalar maps are compatible with composition: for positive
powers use the normalized binary associator square, for negative powers evaluate on
positive powers and use the dual formula. On ordinary pure tensors, both tower paths
send ((x tensor a) tensor s) tensor t to (x tensor j(s)t) tensor b_20,m(a tensor 1).
For the completed square precompose by chi_21,C_10 * B_21(chi_10) at T_0,m K.
Substitute the definitions of beta and associator. Naturality moves intermediate chi
maps next to their inverses, which cancel, leaving the ordinary tower equality.
All objects at which chi is inverted are complete. Cancel the initial isomorphism. -/
theorem tower (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (N : integralTowerModules l F X) [N.IsFiniteLocallyFreeOfRank 1]
    (P : integralTowerModules l G X) [P.IsFiniteLocallyFreeOfRank 1]
    (b10 : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N)
    (b21 : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l F G j X) N ≅ P)
    (b20 : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E G (j.comp ι) X) L ≅ P)
    (hb : ∀ (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
      (t : (completedIntegralCommRingSheafUnrestricted l G X).obj.obj U) (x : L.val.obj U),
      b21.hom.val.app U (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max u (t
        + 1)}
          (completedCoefficientMap l F G j X) N U t
          (b10.hom.val.app U (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max
            u (t + 1)}
            (completedCoefficientMap l E F ι X) L U s x))) =
        b20.hom.val.app U (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max u
          (t + 1)}
          (completedCoefficientMap l E G (j.comp ι) X) L U
          (t * (completedCoefficientMap l F G j X).hom.app U s) x))
    (m : ℤ) (K : DerivedCategory (integralTowerModules l E X))
    (hK : IsDerivedCompleteUnrestricted l E X K) :
    (integralScalarExtensionOfUniverses l F G j X).map
        (beta l E X F ι L N b10 m K hK).hom ≫
      (beta l F X G j N P b21 m
        ((integralScalarExtensionOfUniverses l E F ι X).obj K)
        (extension_complete l E X F ι K hK)).hom ≫
      (tensor l G X P m).map (associator l E X F ι G j K hK).hom =
    (associator l E X F ι G j ((tensor l E X L m).obj K)
        (complete l E X L m K hK)).hom ≫
      (beta l E X G (j.comp ι) L P b20 m K hK).hom := by
  unfold beta associator
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom]
  exact conj_tower (completedScalarComparison l F G j X)
    ((pairData l E X F ι L N b10).ordinary m).hom
    ((pairData l F X G j N P b21).ordinary m).hom
    ((pairData l E X G (j.comp ι) L P b20).ordinary m).hom
    (associatorData l E X F ι G j).derived.hom
    (chi l E X F ι K hK) (chi l E X F ι _ (complete l E X L m K hK))
    (chi l F X G j _ (complete l F X N m _ (extension_complete l E X F ι K hK)))
    (chi l F X G j _ (extension_complete l E X F ι K hK))
    (chi l E X G (j.comp ι) K hK)
    (chi l F X G j _ (extension_complete l E X F ι _ (complete l E X L m K hK)))
    (chi l E X G (j.comp ι) _ (complete l E X L m K hK)) rfl rfl
    (pairData_ordinary_tower l E X F ι G j L N P b10 b21 b20 hb
      (pairData_normalized l E X F ι L N b10) (pairData_normalized l F X G j N P b21)
      (pairData_normalized l E X G (j.comp ι) L P b20) m K)

private theorem line_map_heq {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X X' Y Y' : C} (hX : X = X') (hY : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hX
  cases hY
  cases h
  rfl

private theorem line_localizedIso
    {R : Type*} [CommRing R] {S : Type*} [CommRing S]
    {C : Type*} [Category C] [Preadditive C] [Linear R C]
    {D : Type*} [Category D] [Preadditive D] [Linear S D]
    (t : R) (v : S) (ψ : Localization.Away t → Localization.Away v)
    (F₀ G₀ : C ⥤ D) (e : F₀ ≅ G₀)
    (F G : ScalarLocalization R C t ⥤ ScalarLocalization S D v)
    [F.Additive] [G.Additive]
    (hF : ∀ K, F.obj K = ⟨F₀.obj K.obj⟩)
    (hG : ∀ K, G.obj K = ⟨G₀.obj K.obj⟩)
    (mF : ∀ (K K' : C) (f : K ⟶ K') (a : Localization.Away t),
      HEq (F.map (a ⊗ₜ[R] f : ScalarLocalization.mk (R := R) (p := t) K ⟶ ⟨K'⟩))
        (ψ a ⊗ₜ[S] F₀.map f : ScalarLocalization.mk (R := S) (p := v) (F₀.obj K) ⟶
          ⟨F₀.obj K'⟩))
    (mG : ∀ (K K' : C) (f : K ⟶ K') (a : Localization.Away t),
      HEq (G.map (a ⊗ₜ[R] f : ScalarLocalization.mk (R := R) (p := t) K ⟶ ⟨K'⟩))
        (ψ a ⊗ₜ[S] G₀.map f : ScalarLocalization.mk (R := S) (p := v) (G₀.obj K) ⟶
          ⟨G₀.obj K'⟩)) :
    ∃! a : F ≅ G, ∀ K, HEq (a.hom.app K)
      ((ScalarLocalization.localization S D v).map (e.hom.app K.obj)) := by
  exact ScalarLocalization.existsUnique_iso_of_component_formulas
    t v ψ F₀ G₀ e F G hF hG mF mG

private theorem line_app_heq {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (α : F ⟶ G) {X X' : C} (h : X = X') :
    HEq (α.app X) (α.app X') := by
  cases h
  rfl

private theorem line_comp_heq {C : Type*} [Category C]
    {X X' Y Y' Z Z' : C} (hX : X = X') (hY : Y = Y') (hZ : Z = Z')
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y ⟶ Z} {g' : Y' ⟶ Z'}
    (hf : HEq f f') (hg : HEq g g') : HEq (f ≫ g) (f' ≫ g') := by
  cases hX
  cases hY
  cases hZ
  cases hf
  cases hg
  rfl

section Rational

attribute [local irreducible] sfIntegralConstructible
  integralCoefficientLinear integralScalarConstant
  sfIntegralCoefficientLinear
  sfIntegralConstructibleLinear

variable (Y : AlgebraicGeometry.Scheme.{u})

/-- Precisely the conditional constructible-preservation hypothesis in the node.
Source: blueprint Proof (3) (blueprint: lem-pur-completed-line-tensor-coherence). -/
def PreservesConstructible (L : integralTowerModules l E Y) [L.IsFiniteLocallyFreeOfRank 1] :
    Prop := ∀ (m : ℤ) (K : DerivedCategory (integralTowerModules l E Y)),
  sfIntegralConstructible l E Y K →
    sfIntegralConstructible l E Y ((tensor l E Y L m).obj K)

/-- Restriction of the actual line tensor to the recorded integral constructible category.
Source: blueprint Proof (3) (blueprint: lem-pur-completed-line-tensor-coherence). -/
def integralTwist (L : integralTowerModules l E Y) [L.IsFiniteLocallyFreeOfRank 1]
    (hL : PreservesConstructible l E Y L) (m : ℤ) :
    sfIntegralConstructibleCategory l E Y ⥤ sfIntegralConstructibleCategory l E Y :=
  (sfIntegralConstructible l E Y).lift
    ((sfIntegralConstructible l E Y).ι ⋙ tensor l E Y L m)
    (fun K ↦ hL m K.obj K.property)

attribute [local irreducible] integralTwist

section IntegralTwistLinearProof

attribute [local semireducible] sfIntegralCoefficientLinear sfIntegralConstructibleLinear

/-- The restriction is additive and linear for the recorded constant-section scalar action.
Source: Stacks 03EL; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: ordinary tensor maps scalar multiplication to the same scalar on pure tensors.
Sheafification and the exact derived localization preserve this equality. The full
subcategory inherits exactly the ambient Hom actions, so the same identities hold
for integralTwist. Additivity follows in the same way from tensor additivity. -/
theorem integralTwist_linear (L : integralTowerModules l E Y) [L.IsFiniteLocallyFreeOfRank 1]
    (hL : PreservesConstructible l E Y L) (m : ℤ) :
    (integralTwist l E Y L hL m).Additive ∧
      (integralTwist l E Y L hL m).Linear (Padic.coefficientExtensionIntegers l E) := by
  let R := Padic.coefficientExtensionIntegers l E
  let T := SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
    (A := completedIntegralCommRingSheafUnrestricted l E Y) (power l E Y L m)
  have hAdd : T.Additive := by
    simpa only [T, sheaf] using additive l E Y L m
  have hLim : PreservesFiniteLimits T := by
    simpa only [T, sheaf] using finiteLimits l E Y L m
  have hColim : PreservesFiniteColimits T := by
    simpa only [T, sheaf] using finiteColimits l E Y L m
  have hd : (tensor l E Y L m).Linear R := by
    unfold tensor sheaf
    delta sfIntegralCoefficientLinear
    exact exactTensorCoefficientLinear l E Y (power l E Y L m)
  have hdt : (tensor l E Y L m).Additive := by
    unfold tensor
    infer_instance
  have hι : (sfIntegralConstructible l E Y).ι.Linear R := by
    constructor
    intro K M f a
    rfl
  have hc : (integralTwist l E Y L hL m ⋙ (sfIntegralConstructible l E Y).ι).Linear R := by
    unfold integralTwist
    exact Functor.linear_of_iso R
      ((sfIntegralConstructible l E Y).liftCompιIso _ _).symm
  have hcAdd : (integralTwist l E Y L hL m ⋙ (sfIntegralConstructible l E Y).ι).Additive := by
    unfold integralTwist
    exact Functor.additive_of_iso
      ((sfIntegralConstructible l E Y).liftCompιIso _ _).symm
  constructor
  · exact Functor.additive_of_comp_faithful _ (sfIntegralConstructible l E Y).ι
  · constructor
    intro K M f a
    apply (sfIntegralConstructible l E Y).ι.map_injective
    rw [(sfIntegralConstructible l E Y).ι.map_smul]
    exact (integralTwist l E Y L hL m ⋙ (sfIntegralConstructible l E Y).ι).map_smul a f

end IntegralTwistLinearProof

/-- Additivity inherited by integral line tensor.
Source: blueprint Proof (3) (blueprint: lem-pur-completed-line-tensor-coherence). -/
instance integralTwistAdditive (L : integralTowerModules l E Y)
    [L.IsFiniteLocallyFreeOfRank 1] (hL : PreservesConstructible l E Y L) (m : ℤ) :
    (integralTwist l E Y L hL m).Additive := (integralTwist_linear l E Y L hL m).1

/-- The constant-section coefficient action is preserved by integral line tensor.
Source: blueprint Proof (3) (blueprint: lem-pur-completed-line-tensor-coherence). -/
instance integralTwistLinear (L : integralTowerModules l E Y)
    [L.IsFiniteLocallyFreeOfRank 1] (hL : PreservesConstructible l E Y L) (m : ℤ) :
    (integralTwist l E Y L hL m).Linear (Padic.coefficientExtensionIntegers l E) :=
  (integralTwist_linear l E Y L hL m).2

attribute [local instance 5000] integralTwistAdditive integralTwistLinear

/-- The actual raw scalar-localized line tensor, with unchanged objects and tensor Hom maps.
Source: blueprint Proof (3); rationalization definition
(blueprint: lem-pur-completed-line-tensor-coherence). -/
def rationalTwist (L : integralTowerModules l E Y) [L.IsFiniteLocallyFreeOfRank 1]
    (hL : PreservesConstructible l E Y L) (m : ℤ) :
    sfRationalConstructibleCategory l E Y ⥤ sfRationalConstructibleCategory l E Y :=
  ScalarLocalization.map (Padic.coefficientExtensionIntegers l E)
    (sfIntegralConstructibleCategory l E Y) (Padic.coefficientExtensionUniformizer l E)
    (integralTwist l E Y L hL m)

private instance rationalTwist_additive (L : integralTowerModules l E Y)
    [L.IsFiniteLocallyFreeOfRank 1] (hL : PreservesConstructible l E Y L) (m : ℤ) :
    (rationalTwist l E Y L hL m).Additive := by
  unfold rationalTwist
  infer_instance

attribute [local semireducible] sfIntegralConstructible

attribute [local semireducible] integralTwist

/-- Intrinsic integral objects satisfy the recorded augmented quotient-tower completeness.
Source: Bhatt--Scholze, Definition 3.5.2
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: the intrinsic predicate contains its canonical augmented reduction triangle.
The standard derived restriction and K-flat counits identify its legs with those of
the unrestricted reduction tower. This transports the same distinguished triangle;
the auxiliary finite-field presentation in the old predicate is immaterial. -/
theorem intrinsic_complete (K : sfIntegralConstructibleCategory l E Y) :
    IsDerivedCompleteUnrestricted l E Y K.obj := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    obtain ⟨q, hq, hprime⟩ := Nat.exists_infinite_primes (l + 1)
    let : Fact q.Prime := ⟨hprime⟩
    let D : FiniteFieldDatum.{0} :=
      { p := q
        a := 1
        q := q
        prime := hprime
        exponent_pos := le_refl 1
        cardinality_eq := (pow_one q).symm
        k₀ := ZMod q
        card_base := by simp [Nat.card_eq_fintype_card]
        k := AlgebraicClosure (ZMod q) }
    have hlD : l ≠ D.p := by
      change l ≠ q
      omega
    exact ⟨D, hlD, (sfDerivedComplete_iff_legacy l E Y D hlD K.obj).mp K.property.1⟩

/-- Restriction of evaluation, fixed on every integral object by the ambient evaluation.
Source: blueprint Proof (3) (blueprint: lem-pur-completed-line-tensor-coherence).
Proof: preservation by both signed tensors puts both endpoints in the full subcategory.
Full faithfulness restricts the evaluation and its inverse uniquely. Its naturality
and inverse identities are inherited from epsilon. -/
theorem integralEpsilon_existsUnique (L : integralTowerModules l E Y)
    [L.IsFiniteLocallyFreeOfRank 1] (hL : PreservesConstructible l E Y L) (m : ℤ) :
    ∃! e : integralTwist l E Y L hL m ⋙ integralTwist l E Y L hL (-m) ≅ 𝟭 _,
      ∀ K : sfIntegralConstructibleCategory l E Y,
        (e.hom.app K).hom = (epsilon l E Y L m).hom.app K.obj := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    let e : integralTwist l E Y L hL m ⋙ integralTwist l E Y L hL (-m) ≅ 𝟭 _ :=
      NatIso.ofComponents
        (fun K ↦ (sfIntegralConstructible l E Y).isoMk ((epsilon l E Y L m).app K.obj))
        (by
          intro K M f
          apply (sfIntegralConstructible l E Y).ι.map_injective
          exact (epsilon l E Y L m).hom.naturality f.hom)
    refine ⟨e, fun _ ↦ rfl, ?_⟩
    intro e' he'
    apply Iso.ext
    apply NatTrans.ext
    funext K
    apply (sfIntegralConstructible l E Y).ι.map_injective
    exact he' K

/-- The restricted evaluation is uniquely fixed by the ambient sheaf evaluation.
Source: blueprint Proof (3) (blueprint: lem-pur-completed-line-tensor-coherence). -/
def integralEpsilon (L : integralTowerModules l E Y) [L.IsFiniteLocallyFreeOfRank 1]
    (hL : PreservesConstructible l E Y L) (m : ℤ) :
    integralTwist l E Y L hL m ⋙ integralTwist l E Y L hL (-m) ≅ 𝟭 _ :=
  (integralEpsilon_existsUnique l E Y L hL m).exists.choose

/-- Rationalized evaluation, with components equal to the localization of the integral ones.
Source: blueprint Proof (3) (blueprint: lem-pur-completed-line-tensor-coherence).
Proof: apply localization to both integral evaluation components. Naturality on a pure
Hom tensor is integral naturality multiplied by its scalar; extend over sums. The
integral inverse equations remain inverse equations after localization. Every raw
rational object is an integral representative, proving uniqueness. -/
theorem rationalEpsilon_existsUnique (L : integralTowerModules l E Y)
    [L.IsFiniteLocallyFreeOfRank 1] (hL : PreservesConstructible l E Y L) (m : ℤ) :
    ∃! e : rationalTwist l E Y L hL m ⋙ rationalTwist l E Y L hL (-m) ≅ 𝟭 _,
      ∀ K : sfIntegralConstructibleCategory l E Y,
        e.hom.app ((sfRationalConstructibleLocalization l E Y).obj K) =
          (sfRationalConstructibleLocalization l E Y).map
            ((integralEpsilon l E Y L hL m).hom.app K) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    let R := Padic.coefficientExtensionIntegers l E
    let C := sfIntegralConstructibleCategory l E Y
    let π := Padic.coefficientExtensionUniformizer l E
    let T := integralTwist l E Y L hL m
    let S := integralTwist l E Y L hL (-m)
    have h := line_localizedIso π π id (T ⋙ S) (𝟭 _)
      (integralEpsilon l E Y L hL m)
      (rationalTwist l E Y L hL m ⋙ rationalTwist l E Y L hL (-m)) (𝟭 _)
      (fun _ ↦ rfl) (fun _ ↦ rfl)
      (by
        intro K M f a
        apply heq_of_eq
        change ScalarLocalization.mapHom R C π S _ _
          (ScalarLocalization.mapHom R C π T _ _ (a ⊗ₜ[R] f)) =
          a ⊗ₜ[R] S.map (T.map f)
        simp only [ScalarLocalization.mapHom, LinearMap.baseChange_tmul]
        rfl)
      (by intros; rfl)
    obtain ⟨e, he, hu⟩ := h
    refine ⟨e, fun K ↦ eq_of_heq (he ⟨K⟩), ?_⟩
    intro e' he'
    exact hu e' (fun K ↦ heq_of_eq (he' K.obj))

/-- The actual scalar-localized evaluation.
Source: blueprint Proof (3) (blueprint: lem-pur-completed-line-tensor-coherence). -/
def rationalEpsilon (L : integralTowerModules l E Y) [L.IsFiniteLocallyFreeOfRank 1]
    (hL : PreservesConstructible l E Y L) (m : ℤ) :
    rationalTwist l E Y L hL m ⋙ rationalTwist l E Y L hL (-m) ≅ 𝟭 _ :=
  (rationalEpsilon_existsUnique l E Y L hL m).exists.choose

variable (p : ℕ) (hl : l ≠ p)

attribute [local semireducible] integralScalarExtensionOfUniverses

/-- Restricting the completed beta to the full constructible subcategories.
Source: blueprint Proof (3) (blueprint: lem-pur-completed-line-tensor-coherence).
Proof: both line twists preserve the subcategories by hypothesis and completed scalar
extension preserves them by its constructibility theorem. Full faithfulness restricts
beta and its inverse uniquely, with their inherited naturality equations. -/
theorem integralBeta_existsUnique (L : integralTowerModules l E Y)
    [L.IsFiniteLocallyFreeOfRank 1] (hL : PreservesConstructible l E Y L)
    (N : integralTowerModules l F Y) [N.IsFiniteLocallyFreeOfRank 1]
    (hN : PreservesConstructible l F Y N)
    (b : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
      (completedCoefficientMap l E F ι Y) L ≅ N) (m : ℤ) :
    ∃! e : integralTwist l E Y L hL m ⋙
        sfConstructibleIntegralScalarExtension p l hl E F ι Y ≅
      sfConstructibleIntegralScalarExtension p l hl E F ι Y ⋙ integralTwist l F Y N hN m,
      ∀ K : sfIntegralConstructibleCategory l E Y,
        HEq (e.hom.app K).hom (beta l E Y F ι L N b m K.obj
          (intrinsic_complete l E Y K)).hom := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    let e : integralTwist l E Y L hL m ⋙
        sfConstructibleIntegralScalarExtension p l hl E F ι Y ≅
        sfConstructibleIntegralScalarExtension p l hl E F ι Y ⋙ integralTwist l F Y N hN m :=
      NatIso.ofComponents
        (fun K ↦ (sfIntegralConstructible l F Y).isoMk
          (beta l E Y F ι L N b m K.obj (intrinsic_complete l E Y K)))
        (by
          intro K M f
          apply (sfIntegralConstructible l F Y).ι.map_injective
          exact (beta_natural_evaluation l E Y F ι L N b).1 m K.obj M.obj
            (intrinsic_complete l E Y K) (intrinsic_complete l E Y M) f.hom)
    refine ⟨e, fun _ ↦ HEq.rfl, ?_⟩
    intro e' he'
    apply Iso.ext
    apply NatTrans.ext
    funext K
    apply (sfIntegralConstructible l F Y).ι.map_injective
    exact eq_of_heq (he' K)

/-- The unique restriction of beta, retaining its ambient components.
Source: blueprint Proof (3) (blueprint: lem-pur-completed-line-tensor-coherence). -/
def integralBeta (L : integralTowerModules l E Y) [L.IsFiniteLocallyFreeOfRank 1]
    (hL : PreservesConstructible l E Y L)
    (N : integralTowerModules l F Y) [N.IsFiniteLocallyFreeOfRank 1]
    (hN : PreservesConstructible l F Y N)
    (b : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
      (completedCoefficientMap l E F ι Y) L ≅ N) (m : ℤ) :
    integralTwist l E Y L hL m ⋙
      sfConstructibleIntegralScalarExtension p l hl E F ι Y ≅
    sfConstructibleIntegralScalarExtension p l hl E F ι Y ⋙ integralTwist l F Y N hN m :=
  (integralBeta_existsUnique l E F ι Y p hl L hL N hN b m).exists.choose

/-- The rational beta on the recorded scalar extensions, fixed by integral localization.
Source: blueprint Proof (3) (blueprint: lem-pur-completed-line-tensor-coherence).
Proof: localize each restricted component and its inverse. On every pure tensor in
Hom, naturality is the integral naturality equation tensored with the image scalar;
additivity extends it to all morphisms. Localization preserves inverse equations.
Objects of the raw rationalization are precisely integral representatives. HEq only
transports the object equalities in the recorded scalar functor's specification. -/
theorem rationalBeta_existsUnique (L : integralTowerModules l E Y)
    [L.IsFiniteLocallyFreeOfRank 1] (hL : PreservesConstructible l E Y L)
    (N : integralTowerModules l F Y) [N.IsFiniteLocallyFreeOfRank 1]
    (hN : PreservesConstructible l F Y N)
    (b : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
      (completedCoefficientMap l E F ι Y) L ≅ N) (m : ℤ) :
    ∃! e : rationalTwist l E Y L hL m ⋙ sfRationalScalarExtension l E Y p hl F ι ≅
        sfRationalScalarExtension l E Y p hl F ι ⋙ rationalTwist l F Y N hN m,
      ∀ K : sfIntegralConstructibleCategory l E Y,
        HEq (e.hom.app ((sfRationalConstructibleLocalization l E Y).obj K))
          ((sfRationalConstructibleLocalization l F Y).map
            ((integralBeta l E F ι Y p hl L hL N hN b m).hom.app K)) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    let T := integralTwist l E Y L hL m
    let S := integralTwist l F Y N hN m
    let C := sfConstructibleIntegralScalarExtension p l hl E F ι Y
    let D := sfRationalScalarExtension l E Y p hl F ι
    let T' := rationalTwist l E Y L hL m
    let S' := rationalTwist l F Y N hN m
    have hD := (sfRationalScalarExtension_existsUnique l E Y p hl F ι).exists.choose_spec
    let ψ a := (sfRationalCoefficientEquiv l F).symm (ι (sfRationalCoefficientEquiv l E a))
    have hloc : ∃! e : T' ⋙ D ≅ D ⋙ S',
        ∀ K : sfRationalConstructibleCategory l E Y,
          HEq (e.hom.app K) ((sfRationalConstructibleLocalization l F Y).map
            ((integralBeta l E F ι Y p hl L hL N hN b m).hom.app K.obj)) := by
      apply line_localizedIso
        (Padic.coefficientExtensionUniformizer l E) (Padic.coefficientExtensionUniformizer l F)
        ψ (T ⋙ C) (C ⋙ S) (integralBeta l E F ι Y p hl L hL N hN b m)
        (T' ⋙ D) (D ⋙ S')
      · intro K
        exact hD.2.1 (T'.obj K)
      · intro K
        exact congrArg S'.obj (hD.2.1 K)
      · intro K K' f a
        have ht : T'.map (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f :
            ScalarLocalization.mk (R := Padic.coefficientExtensionIntegers l E)
              (p := Padic.coefficientExtensionUniformizer l E) K ⟶ ⟨K'⟩) =
            a ⊗ₜ[Padic.coefficientExtensionIntegers l E] T.map f :=
          LinearMap.baseChange_tmul _ _ _
        dsimp only [Functor.comp_map]
        rw [ht]
        exact hD.2.2 (T.obj K) (T.obj K') (T.map f) a
      · intro K K' f a
        have hm := line_map_heq S' (hD.2.1 ⟨K⟩) (hD.2.1 ⟨K'⟩) (hD.2.2 K K' f a)
        exact hm.trans (heq_of_eq (LinearMap.baseChange_tmul _ _ _))
    obtain ⟨e, he, hu⟩ := hloc
    refine ⟨e, fun K ↦ he ⟨K⟩, ?_⟩
    intro e' he'
    exact hu e' (fun K ↦ he' K.obj)

/-- The normalized rational scalar/line comparison.
Source: blueprint Proof (3) (blueprint: lem-pur-completed-line-tensor-coherence). -/
def rationalBeta (L : integralTowerModules l E Y) [L.IsFiniteLocallyFreeOfRank 1]
    (hL : PreservesConstructible l E Y L)
    (N : integralTowerModules l F Y) [N.IsFiniteLocallyFreeOfRank 1]
    (hN : PreservesConstructible l F Y N)
    (b : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
      (completedCoefficientMap l E F ι Y) L ≅ N) (m : ℤ) :
    rationalTwist l E Y L hL m ⋙ sfRationalScalarExtension l E Y p hl F ι ≅
      sfRationalScalarExtension l E Y p hl F ι ⋙ rationalTwist l F Y N hN m :=
  (rationalBeta_existsUnique l E F ι Y p hl L hL N hN b m).exists.choose

/-- Two conjugated associators agree when the ordinary associators correspond under
comparisons of the ordinary models compatible with the completion maps.
Source: blueprint Proof (3) (blueprint: lem-pur-completed-line-tensor-coherence). -/
private theorem conj_compare {A B C : Type*} [Category A] [Category B] [Category C]
    {D₁ C₁ : A ⥤ B} {D₂ C₂ C₂' : B ⥤ C} {D₁₂ C₁₂ C₁₂' : A ⥤ C}
    (e₁ : D₁ ≅ C₁) (e₂ : D₂ ≅ C₂) (e₁₂ : D₁₂ ≅ C₁₂)
    (od : D₁ ⋙ D₂ ≅ D₁₂) (ad : C₁ ⋙ C₂ ≅ C₁₂)
    (hA : Functor.isoWhiskerLeft D₁ e₂ ≪≫ Functor.isoWhiskerRight e₁ C₂ ≪≫ ad = od ≪≫ e₁₂)
    {K : A} {K₁ : B} (x₁ : C₁.obj K ≅ K₁) (x₂ : C₂.obj K₁ ≅ C₂'.obj K₁)
    (x₁₂ : C₁₂.obj K ≅ C₁₂'.obj K)
    (y₁ : D₁.obj K ≅ K₁) (y₂ : D₂.obj K₁ ≅ C₂'.obj K₁) (y₁₂ : D₁₂.obj K ≅ C₁₂'.obj K)
    (hy₁ : y₁.hom = e₁.hom.app K ≫ x₁.hom) (hy₂ : y₂.hom = e₂.hom.app K₁ ≫ x₂.hom)
    (hy₁₂ : y₁₂.hom = e₁₂.hom.app K ≫ x₁₂.hom) :
    y₂.inv ≫ D₂.map y₁.inv ≫ od.hom.app K ≫ y₁₂.hom =
      x₂.inv ≫ C₂.map x₁.inv ≫ ad.hom.app K ≫ x₁₂.hom := by
  obtain rfl : y₁ = e₁.app K ≪≫ x₁ := Iso.ext hy₁
  obtain rfl : y₂ = e₂.app K₁ ≪≫ x₂ := Iso.ext hy₂
  obtain rfl : y₁₂ = e₁₂.app K ≪≫ x₁₂ := Iso.ext hy₁₂
  have hK := congrArg (fun e ↦ e.hom.app K) hA
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hK
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.app_inv, Iso.app_hom, Functor.map_comp,
    Category.assoc]
  rw [reassoc_of% hK.symm]
  have hn := e₂.hom.naturality (x₁.inv ≫ e₁.inv.app K)
  simp only [Functor.map_comp, Category.assoc] at hn
  rw [reassoc_of% hn]
  simp only [Iso.inv_hom_id_app_assoc, ← C₂.map_comp_assoc, Iso.inv_hom_id_app,
    Category.comp_id]

/-- Two conjugated unitors agree when the ordinary unitors correspond under a comparison of
the ordinary models compatible with the completion maps.
Source: blueprint Proof (3) (blueprint: lem-pur-completed-line-tensor-coherence). -/
private theorem conj_compare_unit {A : Type*} [Category A]
    {D C C' : A ⥤ A} (e : D ≅ C) (ou : C ≅ 𝟭 A) (du : D ≅ 𝟭 A)
    (hu : e.hom ≫ ou.hom = du.hom) {K : A}
    (x : C.obj K ≅ C'.obj K) (y : D.obj K ≅ C'.obj K)
    (hy : y.hom = e.hom.app K ≫ x.hom) :
    y.inv ≫ du.hom.app K = x.inv ≫ ou.hom.app K := by
  obtain rfl : y = e.app K ≪≫ x := Iso.ext hy
  rw [← hu]
  simp

/-- The normalized ordinary-to-completed comparison is the scalar completion map.
Source: blueprint Proof (3) (blueprint: lem-pur-completed-line-tensor-coherence).
Proof: the isomorphism with components the scalar completion map satisfies the
normalization characterizing the comparison. -/
private theorem sfIntegralOrdinaryComparison_hom_app (K : sfIntegralConstructibleCategory l E Y) :
    (sfIntegralOrdinaryComparison l E F ι Y).hom.app K =
      (scalarCompletion l E F ι Y).app K.obj := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    have hχ := (scalarCompletion_existsUnique l E F ι Y).exists.choose_spec
    have (K : sfIntegralConstructibleCategory l E Y) :
        IsIso ((scalarCompletion l E F ι Y).app K.obj) := hχ.2 K.obj K.property.1
    let c : (sfIntegralConstructible l E Y).ι ⋙ integralOrdinaryDerivedScalar l E F ι Y ≅
        (sfIntegralConstructible l E Y).ι ⋙ integralScalarExtension l E F ι Y :=
      NatIso.ofComponents (fun K ↦ asIso ((scalarCompletion l E F ι Y).app K.obj))
        (fun f ↦ (scalarCompletion l E F ι Y).naturality f.hom)
    have h := (sfIntegralOrdinaryComparison_existsUnique l E F ι Y).unique
      (sfIntegralOrdinaryComparison_existsUnique l E F ι Y).exists.choose_spec
      (y₂ := c) (fun P _ ↦ hχ.1 P)
    exact congrArg (fun a ↦ a.hom.app K) h

/-- The associator and unit restrict to the recorded canonical integral comparisons;
the recorded rational comparisons are their localizations.
Source: blueprint Proof (3); scalar-extension composition construction
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: both ordinary constructions are fixed by balanced scalar multiplication on
K-flat representatives, so their unique counit-compatible comparisons identify them.
Their normalized chi maps are fixed by the same quotient-cone maps with zero shifted
component. The conjugated associator and unitor therefore agree on all complete inputs.
Full faithfulness gives the integral equalities. The specification of the recorded
rational associator and unit says exactly that they localize those integral components. -/
theorem canonical_restriction :
    (∀ K : sfIntegralConstructibleCategory l E Y,
      HEq ((sfIntegralScalarComp l E F ι Y p hl G j).hom.app K).hom
        (associator l E Y F ι G j K.obj (intrinsic_complete l E Y K)).hom) ∧
    (∀ K : sfIntegralConstructibleCategory l E Y,
      HEq ((sfIntegralScalarUnit l E Y p hl).hom.app K).hom
        (unit l E Y K.obj (intrinsic_complete l E Y K)).hom) ∧
    (∀ K : sfIntegralConstructibleCategory l E Y,
      HEq ((sfRationalScalarComp l E F ι Y p hl G j).hom.app
        ((sfRationalConstructibleLocalization l E Y).obj K))
        ((sfRationalConstructibleLocalization l G Y).map
          ((sfIntegralScalarComp l E F ι Y p hl G j).hom.app K))) ∧
    (∀ K : sfIntegralConstructibleCategory l E Y,
      HEq ((sfRationalScalarUnit l E Y p hl).hom.app
        ((sfRationalConstructibleLocalization l E Y).obj K))
        ((sfRationalConstructibleLocalization l E Y).map
          ((sfIntegralScalarUnit l E Y p hl).hom.app K))) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    refine ⟨fun K ↦ ?_, fun K ↦ ?_, fun K ↦ ?_, fun K ↦ ?_⟩
    · obtain ⟨eEF, eFG, eEG, hEF, hFG, hEG, hA⟩ :=
        (integralScalarOrdinaryModelCoherence l).2 E F G ι j Y
      apply heq_of_eq
      rw [show ((sfIntegralScalarComp l E F ι Y p hl G j).hom.app K).hom = _ from
        (sfIntegralScalarComp_existsUnique l E F ι Y p hl G j).exists.choose_spec K]
      unfold associator
      simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom]
      exact conj_compare eEF eFG eEG (integralOrdinaryDerivedScalarComp l E F ι Y G j)
        (associatorData l E Y F ι G j).derived hA
        (chi l E Y F ι K.obj (intrinsic_complete l E Y K))
        (chi l F Y G j _ (extension_complete l E Y F ι K.obj (intrinsic_complete l E Y K)))
        (chi l E Y G (j.comp ι) K.obj (intrinsic_complete l E Y K))
        ((sfIntegralOrdinaryComparison l E F ι Y).app K)
        ((sfIntegralOrdinaryComparison l F G j Y).app
          ((sfConstructibleIntegralScalarExtension p l hl E F ι Y).obj K))
        ((sfIntegralOrdinaryComparison l E G (j.comp ι) Y).app K)
        (by rw [Iso.app_hom, sfIntegralOrdinaryComparison_hom_app, ← hEF]; rfl)
        (by rw [Iso.app_hom, sfIntegralOrdinaryComparison_hom_app, ← hFG]; rfl)
        (by rw [Iso.app_hom, sfIntegralOrdinaryComparison_hom_app, ← hEG]; rfl)
    · obtain ⟨e, hχ, hu⟩ := (integralScalarOrdinaryModelCoherence l).1 E Y
      apply heq_of_eq
      rw [show ((sfIntegralScalarUnit l E Y p hl).hom.app K).hom = _ from
        (sfIntegralScalarUnit_existsUnique l E Y p hl).exists.choose_spec K]
      unfold unit
      simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom]
      exact conj_compare_unit e (ordinaryUnit l E Y) (integralOrdinaryDerivedScalarUnit l E Y)
        hu (chi l E Y E (AlgHom.id ℚ_[l] E) K.obj (intrinsic_complete l E Y K))
        ((sfIntegralOrdinaryComparison l E E (AlgHom.id ℚ_[l] E) Y).app K)
        (by rw [Iso.app_hom, sfIntegralOrdinaryComparison_hom_app, ← hχ]; rfl)
    · exact (sfRationalScalarComp_existsUnique l E F ι Y p hl G j).exists.choose_spec _
    · exact (sfRationalScalarUnit_existsUnique l E Y p hl).exists.choose_spec _

/-- Evaluation compatibility after rationalization, with exactly the integral components.
Source: blueprint Proof (3) (blueprint: lem-pur-completed-line-tensor-coherence).
Proof: restrict the ambient evaluation square by full faithfulness. Rationalization
sends both integral composites to the corresponding composites. The normalized
component equations for rationalBeta and rationalEpsilon identify these images
with the displayed square, including all morphisms tensored with arbitrary scalars. -/
theorem rational_evaluation (L : integralTowerModules l E Y) [L.IsFiniteLocallyFreeOfRank 1]
    (hL : PreservesConstructible l E Y L)
    (N : integralTowerModules l F Y) [N.IsFiniteLocallyFreeOfRank 1]
    (hN : PreservesConstructible l F Y N)
    (b : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
      (completedCoefficientMap l E F ι Y) L ≅ N)
    (m : ℤ) (K : sfRationalConstructibleCategory l E Y) :
    (rationalBeta l E F ι Y p hl L hL N hN b (-m)).hom.app
        ((rationalTwist l E Y L hL m).obj K) ≫
      (rationalTwist l F Y N hN (-m)).map
        ((rationalBeta l E F ι Y p hl L hL N hN b m).hom.app K) ≫
      (rationalEpsilon l F Y N hN m).hom.app
        ((sfRationalScalarExtension l E Y p hl F ι).obj K) =
    (sfRationalScalarExtension l E Y p hl F ι).map
      ((rationalEpsilon l E Y L hL m).hom.app K) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    let C := sfConstructibleIntegralScalarExtension p l hl E F ι Y
    let D := sfRationalScalarExtension l E Y p hl F ι
    let Q := sfRationalConstructibleLocalization l F Y
    let T := integralTwist l E Y L hL m
    let S := integralTwist l F Y N hN m
    let Sm := integralTwist l F Y N hN (-m)
    let Smq := rationalTwist l F Y N hN (-m)
    let bp := integralBeta l E F ι Y p hl L hL N hN b m
    let bm := integralBeta l E F ι Y p hl L hL N hN b (-m)
    let eE := integralEpsilon l E Y L hL m
    let eF := integralEpsilon l F Y N hN m
    have hi : bm.hom.app (T.obj K.obj) ≫ Sm.map (bp.hom.app K.obj) ≫
          eF.hom.app (C.obj K.obj) = C.map (eE.hom.app K.obj) := by
      apply (sfIntegralConstructible l F Y).ι.map_injective
      have hbp := eq_of_heq
        ((integralBeta_existsUnique l E F ι Y p hl L hL N hN b m).exists.choose_spec K.obj)
      have hbm := eq_of_heq
        ((integralBeta_existsUnique l E F ι Y p hl L hL N hN b (-m)).exists.choose_spec
          (T.obj K.obj))
      simp only [ObjectProperty.ι_map]
      change (bp.hom.app K.obj).hom = _ at hbp
      change (bm.hom.app (T.obj K.obj)).hom = _ at hbm
      have heE := (integralEpsilon_existsUnique l E Y L hL m).exists.choose_spec K.obj
      have heF := (integralEpsilon_existsUnique l F Y N hN m).exists.choose_spec (C.obj K.obj)
      change (bm.hom.app (T.obj K.obj)).hom ≫
          (tensor l F Y N (-m)).map (bp.hom.app K.obj).hom ≫
          (eF.hom.app (C.obj K.obj)).hom =
        (integralScalarExtensionOfUniverses l E F ι Y).map (eE.hom.app K.obj).hom
      change (eE.hom.app K.obj).hom = _ at heE
      change (eF.hom.app (C.obj K.obj)).hom = _ at heF
      erw [hbm, hbp, heE, heF]
      exact (beta_natural_evaluation l E Y F ι L N b).2 m K.obj.obj
        (intrinsic_complete l E Y K.obj)
    have hD := (sfRationalScalarExtension_existsUnique l E Y p hl F ι).exists.choose_spec
    have hobj := hD.2.1 K
    have hbp := (rationalBeta_existsUnique l E F ι Y p hl L hL N hN b m).exists.choose_spec
      K.obj
    have hbm := (rationalBeta_existsUnique l E F ι Y p hl L hL N hN b (-m)).exists.choose_spec
      (T.obj K.obj)
    have hm := line_map_heq Smq (hD.2.1 ((rationalTwist l E Y L hL m).obj K))
      (congrArg (rationalTwist l F Y N hN m).obj hobj) hbp
    have hm' : HEq
        (Smq.map ((rationalBeta l E F ι Y p hl L hL N hN b m).hom.app K))
        (Q.map (Sm.map (bp.hom.app K.obj))) :=
      hm.trans (heq_of_eq (LinearMap.baseChange_tmul _ _ _))
    have heF := (line_app_heq (rationalEpsilon l F Y N hN m).hom hobj).trans
      (heq_of_eq ((rationalEpsilon_existsUnique l F Y N hN m).exists.choose_spec
        (C.obj K.obj)))
    have hleft := line_comp_heq (hD.2.1
        ((rationalTwist l E Y L hL m ⋙ rationalTwist l E Y L hL (-m)).obj K))
      (congrArg Smq.obj (hD.2.1 ((rationalTwist l E Y L hL m).obj K))) hobj hbm
      (line_comp_heq (congrArg Smq.obj (hD.2.1
          ((rationalTwist l E Y L hL m).obj K)))
        (congrArg Smq.obj (congrArg (rationalTwist l F Y N hN m).obj hobj)) hobj hm' heF)
    have heE := (rationalEpsilon_existsUnique l E Y L hL m).exists.choose_spec K.obj
    have hright := line_map_heq D rfl rfl (heq_of_eq heE)
    have hmap : HEq (D.map
        ((sfRationalConstructibleLocalization l E Y).map (eE.hom.app K.obj)))
        (Q.map (C.map (eE.hom.app K.obj))) := by
      simpa only [D, C, Q, sfRationalScalarExtension, sfRationalConstructibleLocalization,
        ScalarLocalization.localization, map_one] using hD.2.2 _ _ (eE.hom.app K.obj) 1
    exact eq_of_heq (hleft.trans ((heq_of_eq (by
      simpa only [Functor.map_comp, Functor.mapIso_inv, Iso.app_inv,
        Functor.mapLinearMap] using congrArg Q.map hi)).trans
        (hright.trans hmap).symm))

end Rational
end CompletedLineTensor
end WeilConjectures
