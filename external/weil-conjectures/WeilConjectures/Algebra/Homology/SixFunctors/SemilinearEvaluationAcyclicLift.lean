/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SemilinearSystemModels
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
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
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.CoverPreserving
import WeilConjectures.Algebra.Homology.System.SystemRingedSequenceSite
import WeilConjectures.Algebra.Homology.System.SystemScalarCoherence
import WeilConjectures.Algebra.Homology.System.SystemGrothendieck
import WeilConjectures.Algebra.Homology.System.SystemEvaluationTopos
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Acyclic lifts of coefficient evaluation

Evaluation at one level admits acyclic lifts, obtained by restriction of scalars above
that level and zero below it. This tests K-flatness without requiring flat terms.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject
namespace SheafOfModules
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r}) (n : ℕ)

private def rightLevel (M : systemLevel B n) (k : ℕ) : systemLevel B k :=
  if h : n ≤ k then (systemRestriction B h).obj M else 0

private def rightAboveIso (M : systemLevel B n) {k : ℕ} (hk : n ≤ k) :
    rightLevel B n M k ≅ (systemRestriction B hk).obj M :=
  eqToIso (dite_eq_left hk)

private def rightTransition (M : systemLevel B n) {j k : ℕ} (h : j ≤ k) :
    rightLevel B n M k ⟶ (systemRestriction B h).obj (rightLevel B n M j) :=
  if hj : n ≤ j then
    let hk := hj.trans h
    let hc : B.map (homOfLE hk).op =
        B.map (homOfLE h).op ≫ B.map (homOfLE hj).op := by
      rw [← B.map_comp]
      rfl
    (rightAboveIso B n M hk).hom ≫
      (systemScalarRestrictionComposition _ _ _ hc).inv.app M ≫
        (systemRestriction B h).map (rightAboveIso B n M hj).inv
  else 0

private theorem rightTransition_above (M : systemLevel B n) {j k : ℕ}
    (h : j ≤ k) (hj : n ≤ j) :
    rightTransition B n M h =
      (rightAboveIso B n M (hj.trans h)).hom ≫
        (systemScalarRestrictionComposition (B.map (homOfLE h).op)
          (B.map (homOfLE hj).op) (B.map (homOfLE (hj.trans h)).op)
          (by rw [← B.map_comp]; rfl)).inv.app M ≫
        (systemRestriction B h).map (rightAboveIso B n M hj).inv := dite_eq_left hj

private def rightObj (M : systemLevel B n) : StrictRingSystem B where
  level := rightLevel B n M
  transition h := rightTransition B n M h
  identity k U x := by
    let η := systemScalarRestrictionUnit (B.map (homOfLE (Nat.le_refl k)).op)
      (B.map_id (op k))
    have he : rightTransition B n M (Nat.le_refl k) =
        η.inv.app (rightLevel B n M k) := by
      by_cases hk : n ≤ k
      · rw [rightTransition_above B n M _ hk]
        apply (cancel_epi (rightAboveIso B n M hk).inv).1
        apply (cancel_mono ((systemRestriction B (Nat.le_refl k)).map
          (rightAboveIso B n M hk).hom)).1
        simp only [Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp,
          Iso.inv_hom_id, CategoryTheory.Functor.map_id]
        rw [← η.inv.naturality]
        simp only [Functor.id_map, Iso.inv_hom_id_assoc]
        ext V y
        rfl
      · have hz : IsZero (rightLevel B n M k) := by
          dsimp only [rightLevel]
          rw [dite_eq_right hk]
          exact isZero_zero _
        exact hz.eq_of_src _ _
    exact congrArg (fun f ↦ f.val.app U x) he
  compose {j k m} h q U x := by
    have hc : B.map (homOfLE (h.trans q)).op =
        B.map (homOfLE q).op ≫ B.map (homOfLE h).op := by
      rw [← B.map_comp]
      rfl
    let η := systemScalarRestrictionComposition _ _ _ hc
    have he : rightTransition B n M (h.trans q) =
        rightTransition B n M q ≫
          (systemRestriction B q).map (rightTransition B n M h) ≫
          η.hom.app (rightLevel B n M j) := by
      by_cases hj : n ≤ j
      · have hk := hj.trans h
        have hm := hk.trans q
        rw [rightTransition_above B n M _ hj, rightTransition_above B n M _ hk,
          rightTransition_above B n M _ hj]
        apply (cancel_epi (rightAboveIso B n M hm).inv).1
        apply (cancel_mono ((systemRestriction B (h.trans q)).map
          (rightAboveIso B n M hj).hom)).1
        simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
        rw [← η.hom.naturality (rightAboveIso B n M hj).hom]
        simp only [Functor.comp_map, ← Functor.map_comp_assoc, ← Functor.map_comp,
          Iso.inv_hom_id, CategoryTheory.Functor.map_id, Iso.inv_hom_id_assoc]
        ext V y
        rfl
      · have hz : IsZero (rightLevel B n M j) := by
          dsimp only [rightLevel]
          rw [dite_eq_right hj]
          exact isZero_zero _
        exact ((systemRestriction B (h.trans q)).map_isZero hz).eq_of_tgt _ _
    exact congrArg (fun f ↦ f.val.app U x) he

private def rightLevelMap {M N : systemLevel B n} (f : M ⟶ N) (k : ℕ) :
    rightLevel B n M k ⟶ rightLevel B n N k :=
  if hk : n ≤ k then (rightAboveIso B n M hk).hom ≫
    (systemRestriction B hk).map f ≫ (rightAboveIso B n N hk).inv else 0

private theorem rightLevelMap_above {M N : systemLevel B n} (f : M ⟶ N)
    {k : ℕ} (hk : n ≤ k) :
    rightLevelMap B n f k = (rightAboveIso B n M hk).hom ≫
      (systemRestriction B hk).map f ≫ (rightAboveIso B n N hk).inv := dite_eq_left hk

private def rightMap {M N : systemLevel B n} (f : M ⟶ N) :
    rightObj B n M ⟶ rightObj B n N where
  app := rightLevelMap B n f
  comm {j k} h := by
    change rightLevelMap B n f k ≫ rightTransition B n N h =
      rightTransition B n M h ≫ (systemRestriction B h).map (rightLevelMap B n f j)
    by_cases hj : n ≤ j
    · have hk := hj.trans h
      rw [rightLevelMap_above B n f hk, rightTransition_above B n N h hj,
        rightTransition_above B n M h hj, rightLevelMap_above B n f hj]
      apply (cancel_epi (rightAboveIso B n M hk).inv).1
      apply (cancel_mono ((systemRestriction B h).map
        (rightAboveIso B n N hj).hom)).1
      simp only [Category.assoc, Iso.inv_hom_id_assoc,
        ← Functor.map_comp, Iso.inv_hom_id,
        CategoryTheory.Functor.map_id, Category.comp_id]
      exact (systemScalarRestrictionComposition (B.map (homOfLE h).op)
        (B.map (homOfLE hj).op) (B.map (homOfLE hk).op)
        (by rw [← B.map_comp]; rfl)).inv.naturality f
    · have hz : IsZero (rightLevel B n N j) := by
        dsimp only [rightLevel]
        rw [dite_eq_right hj]
        exact isZero_zero _
      exact ((systemRestriction B h).map_isZero hz).eq_of_tgt _ _

private def rightExtension : systemLevel B n ⥤ StrictRingSystem B where
  obj := rightObj B n
  map := rightMap B n
  map_id M := by
    apply strictRingSystem_hom_ext B
    intro k
    change rightLevelMap B n (𝟙 M) k = 𝟙 _
    by_cases hk : n ≤ k
    · rw [rightLevelMap_above B n _ hk, CategoryTheory.Functor.map_id, Category.id_comp,
        Iso.hom_inv_id]
    · have hz : IsZero (rightLevel B n M k) := by
        dsimp only [rightLevel]
        rw [dite_eq_right hk]
        exact isZero_zero _
      exact hz.eq_of_src _ _
  map_comp {M N P} f g := by
    apply strictRingSystem_hom_ext B
    intro k
    change rightLevelMap B n (f ≫ g) k =
      rightLevelMap B n f k ≫ rightLevelMap B n g k
    by_cases hk : n ≤ k
    · rw [rightLevelMap_above B n _ hk, rightLevelMap_above B n _ hk,
        rightLevelMap_above B n _ hk, Functor.map_comp]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    · have hz : IsZero (rightLevel B n M k) := by
        dsimp only [rightLevel]
        rw [dite_eq_right hk]
        exact isZero_zero _
      exact hz.eq_of_src _ _

private instance rightExtension_additive : (rightExtension B n).Additive where
  map_add {M N} f g := by
    apply strictRingSystem_hom_ext B
    intro k
    change (systemEvaluation B k).map ((rightExtension B n).map (f + g)) =
      (systemEvaluation B k).map ((rightExtension B n).map f + (rightExtension B n).map g)
    rw [(systemEvaluation B k).map_add]
    change rightLevelMap B n (f + g) k =
      rightLevelMap B n f k + rightLevelMap B n g k
    by_cases hk : n ≤ k
    · rw [rightLevelMap_above B n _ hk, rightLevelMap_above B n _ hk,
        rightLevelMap_above B n _ hk, Functor.map_add]
      simp only [Preadditive.comp_add, Preadditive.add_comp]
    · have hz : IsZero (rightLevel B n M k) := by
        dsimp only [rightLevel]
        rw [dite_eq_right hk]
        exact isZero_zero _
      exact hz.eq_of_src _ _

private def rightExtension_above {k : ℕ} (hk : n ≤ k) :
    rightExtension B n ⋙ systemEvaluation B k ≅ systemRestriction B hk :=
  NatIso.ofComponents (fun M ↦ rightAboveIso B n M hk) (fun f ↦ by
    change rightLevelMap B n f k ≫ (rightAboveIso B n _ hk).hom = _
    rw [rightLevelMap_above B n f hk]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl)

private theorem strict_acyclic_of_evaluation
    (K : CochainComplex (StrictRingSystem B) ℤ)
    (hK : ∀ k : ℕ, (((systemEvaluation B k).mapHomologicalComplex (.up ℤ)).obj K).Acyclic) :
    K.Acyclic := by
  intro i
  apply (HomologicalComplex.exactAt_iff_isZero_homology K i).2
  apply (strictRingSystem_isZero_iff B _).2
  intro k
  have he : ((K.sc i).map (systemEvaluation B k)).Exact := hK k i
  exact ((K.sc i).mapHomologyIso (systemEvaluation B k)).isZero_iff.mp
    ((ShortComplex.exact_iff_isZero_homology _).mp he)

private theorem rightExtension_acyclic
    (Z : CochainComplex (systemLevel B n) ℤ) (hZ : Z.Acyclic) :
    (((rightExtension B n).mapHomologicalComplex (.up ℤ)).obj Z).Acyclic := by
  apply strict_acyclic_of_evaluation B
  intro k
  by_cases hk : n ≤ k
  · let e := (NatIso.mapHomologicalComplex (rightExtension_above B n hk) (.up ℤ)).app Z
    have h : (((systemRestriction B hk).mapHomologicalComplex (.up ℤ)).obj Z).Acyclic := by
      intro i
      exact (hZ i).map (systemRestriction B hk)
    intro i
    exact (h i).of_iso e.symm
  · intro i
    apply HomologicalComplex.ExactAt.of_isZero
    change IsZero (rightLevel B n (Z.X i) k)
    dsimp only [rightLevel]
    rw [dite_eq_right hk]
    exact isZero_zero _

private def rightExtension_evaluation :
    rightExtension B n ⋙ systemEvaluation B n ≅ 𝟭 (systemLevel B n) :=
  rightExtension_above B n (Nat.le_refl n) ≪≫
    systemScalarRestrictionUnit (B.map (homOfLE (Nat.le_refl n)).op) (B.map_id (op n))

private theorem strictEvaluation_acyclicLift
    (Z : CochainComplex (systemLevel B n) ℤ) (hZ : Z.Acyclic) :
    ∃ (L : CochainComplex (StrictRingSystem B) ℤ), L.Acyclic ∧
      Nonempty ((((systemEvaluation B n).mapHomologicalComplex (.up ℤ)).obj L) ≅ Z) := by
  refine ⟨((rightExtension B n).mapHomologicalComplex (.up ℤ)).obj Z,
    rightExtension_acyclic B n Z hZ, ?_⟩
  exact ⟨(NatIso.mapHomologicalComplex (rightExtension_evaluation B n) (.up ℤ)).app Z ≪≫
    (Functor.mapHomologicalComplexIdIso (systemLevel B n) (.up ℤ)).app Z⟩

variable [EssentiallySmall.{r} C]

private theorem sequenceEvaluation_acyclicLift
    (Z : CochainComplex (systemLevel B n) ℤ) (hZ : Z.Acyclic) :
    ∃ (L : CochainComplex (systemSequenceModules B) ℤ), L.Acyclic ∧
      Nonempty ((((systemSequenceEvaluation B n).mapHomologicalComplex (.up ℤ)).obj L) ≅ Z) := by
  obtain ⟨L, hL, ⟨eL⟩⟩ := strictEvaluation_acyclicLift B n Z hZ
  let E := strictSystemSequenceEquivalence B
  let S := (E.functor.mapHomologicalComplex (.up ℤ)).obj L
  have hS : S.Acyclic := by
    intro i
    exact (hL i).map E.functor
  refine ⟨S, hS, ?_⟩
  let β := Functor.isoWhiskerRight E.unitIso (systemEvaluation B n)
  let βc := (NatIso.mapHomologicalComplex β (.up ℤ)).app L
  exact ⟨βc.symm ≪≫ eL⟩

section SemilinearLift

variable (A : ℕ → Sheaf J CommRingCat.{r}) (τ : ∀ i : ℕ, A (i + 1) ⟶ A i)

private def semilinearEvaluationIso :
    systemSequenceEvaluation (WeilConjectures.SemilinearSections.rings J A τ) n ≅
      WeilConjectures.SemilinearSections.evaluation J A τ n :=
  pushforwardCongr (by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    change 𝟙 _ = (eqToHom
      (WeilConjectures.SemilinearSections.evaluation_ring J A τ n).symm).hom.app U
    rw [ObjectProperty.eqToHom_hom, eqToHom_app]
    rfl)

/-- Every acyclic complex at one coefficient level lifts to an acyclic sequence complex.
Source: Zheng, Construction 4.1, with the elementary right extension at a vertex
(blueprint: lem-coef-semilinear-evaluation-acyclic-lift).
Proof: at level k at least n use restriction of scalars from B_n to B_k; below n use
zero. Above n the transitions are the identity on sections, and all other transitions
are zero. Restriction of scalars is exact, so each level complex is acyclic. Exactness
of strict systems is componentwise, hence the whole complex is acyclic. Transport it
through the equivalence with modules on the sequence site. Evaluation at n recovers
the original complex by restriction along the identity ring map. The unit of the
sequence equivalence and the sectionwise identity of the two evaluation functors give
the displayed isomorphism. This includes n = 0 and the zero complex. -/
theorem semilinearEvaluation_acyclicLift
    (Z : CochainComplex (WeilConjectures.SemilinearSections.Mod J (A n)) ℤ)
    (hZ : Z.Acyclic) :
    ∃ (L : CochainComplex (WeilConjectures.SemilinearSections.Systems J A τ) ℤ), L.Acyclic ∧
      Nonempty ((((WeilConjectures.SemilinearSections.evaluation J A τ n).mapHomologicalComplex
        (.up ℤ)).obj L) ≅ Z) := by
  obtain ⟨L, hL, ⟨eL⟩⟩ := sequenceEvaluation_acyclicLift
    (WeilConjectures.SemilinearSections.rings J A τ) n Z hZ
  refine ⟨L, hL, ⟨?_ ≪≫ eL⟩⟩
  refine HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ ((semilinearEvaluationIso n A τ).app (L.X i)).symm) ?_
  intro i j h
  exact (semilinearEvaluationIso n A τ).inv.naturality (L.d i j)

end SemilinearLift
end SheafOfModules
