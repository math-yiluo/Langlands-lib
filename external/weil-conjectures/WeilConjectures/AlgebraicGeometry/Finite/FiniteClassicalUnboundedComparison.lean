/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalDerivedDefinitions
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction

import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
import WeilConjectures.AlgebraicGeometry.Classical.ClassicalDerivedEquivalence
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.Bounded.BoundedBelowProEtaleComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalSheaves
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.AlgebraicGeometry.Etale.EtaleModuleAffineBound
import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
import WeilConjectures.CategoryTheory.DerivedCategory.LeftComplete
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-!
# Classical essential image of unbounded finite-coefficient comparison

Reference: Bhatt--Scholze, The pro-étale topology for schemes, Proposition 5.2.6(3),
Remark 5.2.8, Definition 5.3.1 and Proposition 5.3.2.

We use fixed-ring module sheaves, the ordinary constant-coefficient presentation.
The recorded `finiteCoefficientRealization` identifies these with modules over the
continuous-function coefficient sheaf. Classicality is the existing continuity-map
predicate `IsClassicalComplexFor`, degree by degree on cohomology sheaves.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated Opposite
open scoped ZeroObject

namespace AlgebraicGeometry.ProEtale

@[irreducible]
private noncomputable def standardHomologyIso (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] (q : ℤ) :
    DerivedCategory.homologyFunctor
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) q ≅
      (ShrinkHoms.equivalence.{u + 1}
        (@DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) _ _
          (HasDerivedCategory.standard _))).inverse ⋙
        (@DerivedCategory.homologyFunctor
          (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) _ _
          (HasDerivedCategory.standard _) q) := by
  let B := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)
  let H := @DerivedCategory.homologyFunctor B _ _ (HasDerivedCategory.standard B) q
  let Q := @DerivedCategory.Q B _ _ (HasDerivedCategory.standard B)
  let e := ShrinkHoms.equivalence.{u + 1} (@DerivedCategory B _ _ (HasDerivedCategory.standard B))
  let eQ : DerivedCategory.Q ⋙ e.inverse ≅ Q :=
    Functor.associator Q e.functor e.inverse ≪≫
      Functor.isoWhiskerLeft Q e.unitIso.symm ≪≫ Q.rightUnitor
  exact (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso B (.up ℤ)) B).preimageIso
      (DerivedCategory.homologyFunctorFactors B q ≪≫
        (@DerivedCategory.homologyFunctorFactors B _ _
          (HasDerivedCategory.standard B) q).symm ≪≫
        Functor.isoWhiskerRight eQ.symm H ≪≫ Functor.associator _ _ _)

private theorem moduleClassical_of_iso (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ]
    {F G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)}
    (e : F ≅ G) (hF : IsClassicalModuleFor X Λ F) : IsClassicalModuleFor X Λ G := by
  intro I _ _ P
  have hmap := continuityMap_natural P e.hom.hom
  have : IsIso (continuityMap P F.obj) := hF P
  have : IsIso (Functor.whiskerLeft P.diagram.op e.hom.hom) := by
    change IsIso (Functor.isoWhiskerLeft P.diagram.op
      ((sheafToPresheaf _ _).mapIso e)).hom
    infer_instance
  apply (isIso_comp_left_iff
    (CategoryTheory.Limits.colimMap (Functor.whiskerLeft P.diagram.op e.hom.hom)) _).mp
  rw [hmap]
  infer_instance

private theorem unboundedImage (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    (M : FiniteCoefficientEtaleDerivedCategory X Λ) :
    IsClassicalComplexFor X Λ
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj M) := by
  let : TopologicalSpace Λ := ⊥
  let : DiscreteTopology Λ := ⟨rfl⟩
  intro q
  obtain ⟨F, hF, _⟩ := (AlgebraicGeometry.proEtaleClassicalSheaves X).2.2 Λ
  let L := comparisonUpperStar (ModuleCat.{u + 1} Λ) X
  let H := (DerivedCategory.homologyFunctor _ q).obj M
  have hc : IsClassicalModuleFor X Λ (L.obj H) := by
    dsimp only [L]
    rw [← hF]
    exact (F.obj H).property
  apply moduleClassical_of_iso X Λ
    ((L.mapDerivedCategoryHomologyFunctorIso q).app M ≪≫
      (standardHomologyIso X Λ q).app _)
  exact hc

private theorem finite_range_upper_bound
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : DerivedCategory C ⥤ DerivedCategory D) [F.CommShift ℤ] [F.IsTriangulated]
    (P : C → Prop)
    (hPiso : ∀ {H H' : C}, (H ≅ H') → P H → P H')
    (e : ℤ) (hF : ∀ (H : C), P H → ∀ p : ℤ, e < p →
      IsZero ((DerivedCategory.homologyFunctor D p).obj
        (F.obj ((DerivedCategory.singleFunctor C 0).obj H))))
    (K : DerivedCategory C) (a b : ℤ) [K.IsGE a] [K.IsLE b]
    (hK : ∀ q : ℤ, a ≤ q → q ≤ b →
      P ((DerivedCategory.homologyFunctor C q).obj K))
    (r : ℤ) (hr : b + e < r) :
    IsZero ((DerivedCategory.homologyFunctor D r).obj (F.obj K)) := by
  have : F.PreservesZeroMorphisms := inferInstance
  have (q : ℤ) : (DerivedCategory.homologyFunctor D q).PreservesZeroMorphisms :=
    inferInstance
  suffices H : ∀ (n : ℕ) (K : DerivedCategory C) (a b : ℤ), b - a ≤ n →
      K.IsGE a → K.IsLE b →
      (∀ q : ℤ, a ≤ q → q ≤ b → P ((DerivedCategory.homologyFunctor C q).obj K)) →
      ∀ r : ℤ, b + e < r →
        IsZero ((DerivedCategory.homologyFunctor D r).obj (F.obj K)) from
    H (b - a).toNat K a b (by omega) inferInstance inferInstance hK r hr
  intro n
  induction n with
  | zero =>
    intro K a b hab _ _ hK r hr
    by_cases hlt : b < a
    · exact (DerivedCategory.homologyFunctor D r).map_isZero
        (F.map_isZero (DerivedCategory.TStructure.t.isZero K b a hlt))
    · have : K.IsGE b := DerivedCategory.TStructure.t.isGE_of_ge K b a (by omega)
      obtain ⟨Y, ⟨eY⟩⟩ :=
        DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K b
      have hY : P Y := hPiso
        ((DerivedCategory.homologyFunctor C b).mapIso eY ≪≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso C b).app Y)
        (hK b (by omega) le_rfl)
      apply (hF Y hY (r - b) (by omega)).of_iso
      exact (DerivedCategory.homologyFunctor D r).mapIso
        (F.mapIso eY ≪≫ F.mapIso
          (((DerivedCategory.singleFunctors C).shiftIso (-b) b 0 (by omega)).app Y).symm ≪≫
          (F.commShiftIso (-b)).app _) ≪≫
        ((DerivedCategory.homologyFunctor D 0).shiftIso (-b) r (r - b) (by omega)).app _
  | succ n ih =>
    intro K a b hab _ _ hK r hr
    by_cases hlt : b < a
    · exact (DerivedCategory.homologyFunctor D r).map_isZero
        (F.map_isZero (DerivedCategory.TStructure.t.isZero K b a hlt))
    have hab' : a ≤ b := by omega
    let t := DerivedCategory.TStructure.t (C := C)
    let T := (t.triangleLTGE b).obj K
    have hT := F.map_distinguished _ (t.triangleLTGE_distinguished b K)
    have h₁ : IsZero ((DerivedCategory.homologyFunctor D r).obj (F.obj T.obj₁)) := by
      refine ih T.obj₁ a (b - 1) (by omega) (inferInstanceAs
        (t.IsGE ((t.truncLT b).obj K) a))
        (t.isLE_truncLT_obj K b (b - 1) (by omega)) ?_ r (by omega)
      intro q hqa hqb
      have := DerivedCategory.isIso_homologyFunctor_map_truncLTι_app K b q (by omega)
      exact hPiso
        (asIso ((DerivedCategory.homologyFunctor C q).map ((t.truncLTι b).app K))).symm
        (hK q hqa (by omega))
    have h₃ : IsZero ((DerivedCategory.homologyFunctor D r).obj (F.obj T.obj₃)) := by
      refine ih T.obj₃ b b (by omega) (inferInstanceAs
        (t.IsGE ((t.truncGE b).obj K) b)) (inferInstanceAs
        (t.IsLE ((t.truncGE b).obj K) b)) ?_ r hr
      intro q hqb hbq
      have := DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app K b q hqb
      exact hPiso
        (asIso ((DerivedCategory.homologyFunctor C q).map ((t.truncGEπ b).app K)))
        (hK q (by omega) hbq)
    exact (DerivedCategory.HomologySequence.exact₂ _ hT r).isZero_of_both_zeros
      (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)

private theorem rightDerived_preserves_countable_products
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasCountableProducts C] [HasCountableProducts D] [CountableAB4Star D]
    [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] [PreservesLimitsOfShape (Discrete ℕ) F] :
    PreservesLimitsOfShape (Discrete ℕ) F.rightDerivedFunctor := by
  classical
  let G := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let a : G ⋙ DerivedCategory.Q ≅
      q ⋙ (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) :=
    Functor.isoWhiskerLeft G (DerivedCategory.quotientCompQhIso D).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors _).symm DerivedCategory.Qh ≪≫
      Functor.associator _ _ _
  let β : G ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
    a.hom ≫ Functor.whiskerLeft q F.rightDerivedFunctorUnit ≫
      (Functor.associator _ _ _).inv ≫
      (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso C)
        F.rightDerivedFunctor).hom
  have hβ (I : CochainComplex C ℤ) [I.IsKInjective] : IsIso (β.app I) := by
    dsimp [β, a]
    infer_instance
  obtain ⟨hP, hQ, _⟩ := derivedCategory_countableProducts_core D
  have : ∀ (I : ℕ → CochainComplex D ℤ),
      PreservesLimit (Discrete.functor I) DerivedCategory.Q := fun I ↦
    preservesLimit_of_preserves_limit_cone (limit.isLimit _) (hQ ℕ I).some
  have : PreservesLimitsOfShape (Discrete ℕ) (DerivedCategory.Q (C := D)) :=
    preservesLimitsOfShape_of_discrete _
  have hfamily (K : ℕ → DerivedCategory C) :
      PreservesLimit (Discrete.functor K) F.rightDerivedFunctor := by
    have hex (n : ℕ) := DerivedCategory.exists_iso_Q_obj_of_isKInjective (K n)
    choose I hI he using hex
    let e (n : ℕ) := (Classical.choice (he n)).symm
    have : ∀ n, (I n).IsKInjective := hI
    let P := HomologicalComplex.coneOfHasLimitEval (Discrete.functor I)
    obtain ⟨hPI, ⟨hPL⟩⟩ := CochainComplex.termwise_product_isKInjective_and_isLimit I
    have : CochainComplex.IsKInjective P.pt := hPI
    have hFPL := isLimitOfPreserves DerivedCategory.Q
      (isLimitOfPreserves G (HomologicalComplex.isLimitConeOfHasLimitEval (Discrete.functor I)))
    let α : Discrete.functor I ⋙ DerivedCategory.Q ≅ Discrete.functor K :=
      Discrete.natIso (fun (n : Discrete ℕ) ↦ e n.as)
    let c := (Cone.postcompose α.hom).obj (DerivedCategory.Q.mapCone P)
    have hc : IsLimit c := (IsLimit.postcomposeHomEquiv α _).symm hPL
    apply preservesLimit_of_preserves_limit_cone hc
    let αβ : (Discrete.functor I ⋙ G) ⋙ DerivedCategory.Q ≅
        (Discrete.functor I ⋙ DerivedCategory.Q) ⋙ F.rightDerivedFunctor :=
      Discrete.natIso (fun (n : Discrete ℕ) ↦ asIso (β.app (I n.as)))
    have hmap : IsLimit (F.rightDerivedFunctor.mapCone (DerivedCategory.Q.mapCone P)) :=
      (IsLimit.equivOfNatIsoOfIso αβ
        (DerivedCategory.Q.mapCone (G.mapCone P))
        (F.rightDerivedFunctor.mapCone (DerivedCategory.Q.mapCone P))
        (Cone.ext (asIso (β.app P.pt)) (fun n ↦ by
          simpa [αβ] using β.naturality (P.π.app n)))).1 hFPL
    exact (IsLimit.equivOfNatIsoOfIso (Functor.isoWhiskerRight α F.rightDerivedFunctor)
      (F.rightDerivedFunctor.mapCone (DerivedCategory.Q.mapCone P))
      (F.rightDerivedFunctor.mapCone c) (Cone.ext (Iso.refl _) (fun n ↦ by simp [c]))).1 hmap
  exact preservesLimitsOfShape_of_discrete _

private theorem etale_fixed_isZero_of_ringed
    (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (n : ℕ)
    (h : ∀ J : InjectiveResolution ((Scheme.etaleConstantModuleFunctor X Λ).obj F),
      IsZero ((((SheafOfModules.evaluation (Scheme.etaleConstantModuleRing X Λ)
        (op (Scheme.Etale.mk (𝟙 X)))).mapHomologicalComplex (.up ℕ)).obj
          J.cocomplex).homology n)) :
    IsZero (((Etale.sectionsFunctor (ModuleCat.{u + 1} Λ) X).rightDerived n).obj F) := by
  let E := Scheme.etaleConstantModuleFunctor X Λ
  have : E.IsEquivalence := Scheme.etaleConstantModuleFunctor_isEquivalence X Λ
  have : E.Additive := Functor.additive_of_preserves_binary_products E
  let I := injectiveResolution F
  let J : InjectiveResolution (E.obj F) :=
    { cocomplex := (E.mapHomologicalComplex _).obj I.cocomplex
      ι := E.mapResolution I.ι
      injective := fun n ↦ by
        change Injective (E.obj (I.cocomplex.X n))
        infer_instance }
  let V := Etale.sectionsFunctor (ModuleCat.{u + 1} Λ) X
  let K := (V.mapHomologicalComplex _).obj I.cocomplex
  let R := SheafOfModules.evaluation (Scheme.etaleConstantModuleRing X Λ)
    (op (Scheme.Etale.mk (𝟙 X)))
  let L := (R.mapHomologicalComplex _).obj J.cocomplex
  let U := forget₂ (ModuleCat.{u + 1}
    ((Scheme.etaleConstantModuleRing X Λ).obj.obj (op (Scheme.Etale.mk (𝟙 X)))))
      AddCommGrpCat.{u + 1}
  let U' := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  have hz : IsZero (((U.mapHomologicalComplex _).obj L).homology n) :=
    (U.map_isZero (h J)).of_iso ((L.sc n).mapHomologyIso U)
  have hz' : IsZero (((U'.mapHomologicalComplex _).obj K).homology n) := hz
  have hz'' : IsZero (U'.obj (K.homology n)) :=
    hz'.of_iso ((K.sc n).mapHomologyIso U').symm
  have : Subsingleton (K.homology n) := AddCommGrpCat.subsingleton_of_isZero hz''
  exact (ModuleCat.isZero_iff_subsingleton.mpr this).of_iso (I.isoRightDerivedObj V n)

private theorem fixed_section_bound
    (k : Type u) [Field k] (hk : Finite k ∨ IsAlgClosed k)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (algebraMap ℤ k (ℓ : ℤ)))
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ∃ a : ℕ, 1 ≤ a ∧ (ℓ : A) ^ a = 0)
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    (W : X.Etale) [IsAffine W.left]
    (H : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
    (hc : IsClassicalModuleFor X A H) (q : ℕ)
    (hq : 2 * ((topologicalKrullDim X).unbotD 0).toNat + 1 < q) :
    IsZero (((sectionsFunctor (ModuleCat.{u + 1} A)
      ((Scheme.toProEt X).obj W)).rightDerived q).obj H) := by
  obtain ⟨a, ha, hAa⟩ := hA
  obtain ⟨F, hF, hEq, _, _⟩ := (AlgebraicGeometry.proEtaleClassicalSheaves X).2.2 A
  let : F.IsEquivalence := hEq
  let G := F.asEquivalence.inverse.obj ⟨H, hc⟩
  let e : (comparisonUpperStar (ModuleCat.{u + 1} A) X).obj G ≅ H :=
    (eqToIso (congrArg (fun T ↦ T.obj G) hF)).symm ≪≫
      (ObjectProperty.ι (IsClassicalModuleFor X A)).mapIso
        (F.asEquivalence.counitIso.app ⟨H, hc⟩)
  let G' := (Scheme.etaleConstantModuleFunctor X A).obj G
  have het : IsZero (((Etale.sectionsFunctor (ModuleCat.{u + 1} A) W.left).rightDerived q).obj
      ((Etale.upperStar (ModuleCat.{u + 1} A) W.hom).obj G)) := by
    have hb := etaleModule_affine_cohomology_isZero hk ℓ (Fact.out : ℓ.Prime)
      (by simpa using hℓ) A a ha hAa X W G' (q : ℤ) (by exact_mod_cast hq)
    -- The unit identifies restriction of the constant-ring realization with G.
    have he : ((Scheme.etaleConstantModuleRestrictionFunctor X A).obj G') ≅ G :=
      ((Scheme.etaleConstantModuleUnitIso X A).app G).symm
    have hz : IsZero (((Etale.sectionsFunctor (ModuleCat.{u + 1} A) W.left).rightDerived q).obj
        ((Etale.upperStar (ModuleCat.{u + 1} A) W.hom).obj
          ((Scheme.etaleConstantModuleRestrictionFunctor X A).obj G'))) := by
      apply etale_fixed_isZero_of_ringed
      intro J
      exact hb J
    exact hz.of_iso (((Etale.sectionsFunctor (ModuleCat.{u + 1} A) W.left).rightDerived q).mapIso
      ((Etale.upperStar (ModuleCat.{u + 1} A) W.hom).mapIso he)).symm
  have hp := isZero_rightDerived_globalSectionsFunctor_comparisonUpperStar_obj
    (ModuleCat.{u + 1} A) W.left _ q het
  have hglobal : IsZero (((globalSectionsFunctor (ModuleCat.{u + 1} A) W.left).rightDerived q).obj
      ((ProEtale.upperStar (ModuleCat.{u + 1} A) W.hom).obj H)) := by
    apply hp.of_iso
    exact ((globalSectionsFunctor (ModuleCat.{u + 1} A) W.left).rightDerived q).mapIso
      ((ProEtale.upperStar (ModuleCat.{u + 1} A) W.hom).mapIso e.symm ≪≫
        (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) W.hom).app G)
  exact isZero_rightDerived_sectionsFunctor_of_upperStar
    (ModuleCat.{u + 1} A) ((Scheme.toProEt X).obj W) H q hglobal

/-- **Truncation and pro-étale sections.** Let `W` be an object of the small pro-étale site of
`X` and `e` a bound such that `H^q(W, F) = 0` for `q > e` and every classical sheaf `F` of
`A`-modules on `X_proét`. If `K` is a complex of pro-étale sheaves of `A`-modules with classical
cohomology sheaves and `H^q(K) = 0` for `q > b`, then `H^j RΓ(W, K) = 0` for `j > b + e + 1`.

The complex is the derived limit of its truncations `τ_{≥ -n} K`, which are bounded; on each
truncation the vanishing range follows from the hypothesis on classical sheaves, and the derived
limit costs at most one further degree. -/
theorem section_tail_bound
    (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (W : X.ProEt) (e : ℕ)
    (hb : ∀ H : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A),
      IsClassicalModuleFor X A H → ∀ q : ℕ, e < q →
        IsZero (((sectionsFunctor (ModuleCat.{u + 1} A) W).rightDerived q).obj H))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (b : ℤ) [K.IsLE b]
    (hc : ∀ q : ℤ, q ≤ b → IsClassicalModuleFor X A
      ((DerivedCategory.homologyFunctor
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) q).obj K)) :
    (((sectionsFunctor (ModuleCat.{u + 1} A) W).rightDerivedFunctor).obj K).IsLE (b + e + 1) := by
  let C := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)
  let : Abelian C := inferInstance
  have (q : ℤ) : (DerivedCategory.homologyFunctor C q).PreservesZeroMorphisms :=
    inferInstance
  let F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A) ⥤
      ModuleCat.{u + 1} A := sectionsFunctor (ModuleCat.{u + 1} A) W
  have : F.Additive := inferInstance
  have : PreservesLimitsOfShape (Discrete ℕ) F := by
    dsimp only [F, sectionsFunctor]
    infer_instance
  have : CountableAB4Star (ModuleCat.{u + 1} A) := by
    refine ⟨fun J ↦ ?_⟩
    exact HasExactLimitsOfShape.of_domain_equivalence (ModuleCat.{u + 1} A)
      (Discrete.equivalence Equiv.ulift : Discrete (ULift.{u + 1} J) ≌ Discrete J)
  have : PreservesLimitsOfShape (Discrete ℕ) F.rightDerivedFunctor :=
    rightDerived_preserves_countable_products.{u + 1, u + 2, u + 1, u + 2,
      u + 1, u + 1}
      (C := C) (D := ModuleCat.{u + 1} A) F
  have : HasExactLimitsOfShape (Discrete ℕ) C := CountableAB4Star.ofShape ℕ
  apply DerivedCategory.isLE_obj_of_forall_isLE_obj_truncGE.{u + 1, u + 2, u + 1,
      u + 2, u + 1, u + 1}
    (C := C) (D := ModuleCat.{u + 1} A) F.rightDerivedFunctor K (b + e)
  intro n
  rw [DerivedCategory.isLE_iff]
  intro r hr
  refine finite_range_upper_bound.{u + 1, u + 2, u + 1, u + 2, u + 1, u + 1}
    (C := C) (D := ModuleCat.{u + 1} A)
    F.rightDerivedFunctor (IsClassicalModuleFor X A)
    (fun i hi ↦ moduleClassical_of_iso X A i hi) e ?_
    _ (-(n : ℤ)) b ?_ r hr
  · intro H hH q hq
    have hnonneg : 0 ≤ q := by omega
    have heq : (q.toNat : ℤ) = q := Int.toNat_of_nonneg hnonneg
    have hz := (hb H hH q.toNat (by omega)).of_iso
      (Functor.homologyRightDerivedFunctorObjSingleFunctorIso
        (C := C) (D := ModuleCat.{u + 1} A) F H q.toNat)
    simpa only [heq] using hz
  · intro q hnq hqb
    have := DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app K (-(n : ℤ)) q hnq
    apply moduleClassical_of_iso X A
      (asIso ((DerivedCategory.homologyFunctor C q).map
        ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K)))
    exact hc q hqb

private theorem comparison_isLE_of_sections
    (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (b : ℤ)
    (hb : ∀ (W : X.Etale) [IsAffine W.left],
      (((sectionsFunctor (ModuleCat.{u + 1} A)
        ((Scheme.toProEt X).obj W)).rightDerivedFunctor).obj K).IsLE b) :
    ((comparisonLowerStar (ModuleCat.{u + 1} A) X).rightDerivedFunctor.obj K).IsLE b := by
  let C := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)
  let : Abelian C := inferInstance
  have (q : ℤ) : (DerivedCategory.homologyFunctor C q).PreservesZeroMorphisms :=
    inferInstance
  let D := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)
  let : Abelian D := inferInstance
  let R := comparisonLowerStar (ModuleCat.{u + 1} A) X
  have : R.rightDerivedFunctor.PreservesZeroMorphisms := inferInstance
  obtain ⟨I, hI, ⟨eI⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective K
  rw [DerivedCategory.isLE_iff]
  intro q hq
  have he : R.rightDerivedFunctor.obj K ≅
      DerivedCategory.Q.obj ((R.mapHomologicalComplex _).obj I) :=
    R.rightDerivedFunctor.mapIso eI ≪≫ R.rightDerivedFunctorObjQIso I
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor D q).mapIso he ≪≫
    (DerivedCategory.homologyFunctorFactors D q).app _)
  rw [HomologicalComplex.homologyFunctor_obj,
    ← HomologicalComplex.exactAt_iff_isZero_homology]
  have : HasLimitsOfSize.{u, u + 1} (ModuleCat.{u + 1} A) :=
    hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} _
  let Φ := (Scheme.AffineEtale.Spec X).sheafPushforwardContinuous (ModuleCat.{u + 1} A)
    (Scheme.AffineEtale.topology X) X.smallEtaleTopology
  have : LocallySmall.{u + 1} X.AffineEtale :=
    ⟨fun _ _ ↦ ⟨ULift.{u + 1} _, ⟨Equiv.ulift.symm⟩⟩⟩
  have : EssentiallySmall.{u + 1} X.AffineEtale := essentiallySmall_of_small_of_locallySmall _
  have : HasSheafify (Scheme.AffineEtale.topology X) (ModuleCat.{u + 1} A) :=
    GrothendieckTopology.hasSheafify_of_essentiallySmall _ _
  have : Abelian (Sheaf (Scheme.AffineEtale.topology X) (ModuleCat.{u + 1} A)) :=
    sheafIsAbelian
  have : Φ.Additive := ⟨rfl⟩
  have : Φ.PreservesHomology := {}
  let S := ((R.mapHomologicalComplex (.up ℤ)).obj I).sc q
  change S.Exact
  rw [← S.exact_map_iff_of_faithful Φ]
  have hS : ((S.map Φ).map
      (sheafToPresheaf (Scheme.AffineEtale.topology X) (ModuleCat.{u + 1} A))).Exact := by
    rw [ShortComplex.exact_iff_evaluation]
    intro W
    let V := (Scheme.AffineEtale.Spec X).obj W.unop
    have : IsAffine V.left := by
      dsimp only [V]
      rw [Scheme.AffineEtale.Spec_obj_left]
      infer_instance
    let F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A) ⥤
      ModuleCat.{u + 1} A := sectionsFunctor (ModuleCat.{u + 1} A) ((Scheme.toProEt X).obj V)
    have hz := DerivedCategory.isZero_of_isLE (F.rightDerivedFunctor.obj K) b q hq
      (hX := hb V)
    have hz' : IsZero (((F.mapHomologicalComplex (.up ℤ)).obj I).homology q) :=
      hz.of_iso ((DerivedCategory.homologyFunctor _ q).mapIso
        (F.rightDerivedFunctor.mapIso eI ≪≫ F.rightDerivedFunctorObjQIso I) ≪≫
          (DerivedCategory.homologyFunctorFactors _ q).app _).symm
    exact (HomologicalComplex.exactAt_iff_isZero_homology _ q).2 hz'
  have : (presheafToSheaf (Scheme.AffineEtale.topology X)
      (ModuleCat.{u + 1} A)).PreservesHomology := {}
  have hS' := hS.map (presheafToSheaf (Scheme.AffineEtale.topology X) (ModuleCat.{u + 1} A))
  exact (ShortComplex.exact_iff_of_iso
    (ShortComplex.mapNatIso (S.map Φ) (sheafificationNatIso _ _)).symm).1 hS'

private theorem moduleClassical_of_isZero (X : Scheme.{u}) (A : Type (u + 1))
    [CommRing A] (H : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
    (hH : IsZero H) : IsClassicalModuleFor X A H := by
  obtain ⟨F, hF, _⟩ := (AlgebraicGeometry.proEtaleClassicalSheaves X).2.2 A
  let L := comparisonUpperStar (ModuleCat.{u + 1} A) X
  have : L.PreservesZeroMorphisms := inferInstance
  have hc : IsClassicalModuleFor X A
      (L.obj (0 : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) := by
    dsimp only [L]
    rw [← hF]
    exact (F.obj (0 : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))).property
  have hz : IsZero (L.obj (0 : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
    L.map_isZero (isZero_zero _)
  let i : L.obj (0 : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ≅ H := hz.iso hH
  apply moduleClassical_of_iso X A i
  exact hc

private theorem classical_truncGE (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (hK : IsClassicalComplexFor X A K) (n : ℤ) :
    IsClassicalComplexFor X A ((DerivedCategory.TStructure.t.truncGE n).obj K) := by
  let C := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)
  let : Abelian C := inferInstance
  have (q : ℤ) : (DerivedCategory.homologyFunctor C q).PreservesZeroMorphisms :=
    inferInstance
  intro q
  apply moduleClassical_of_iso X A ((standardHomologyIso X A q).app _)
  by_cases hnq : n ≤ q
  · have := DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app K n q hnq
    apply moduleClassical_of_iso X A
      (asIso ((DerivedCategory.homologyFunctor C q).map
        ((DerivedCategory.TStructure.t.truncGEπ n).app K)))
    exact moduleClassical_of_iso X A ((standardHomologyIso X A q).app K).symm (hK q)
  · exact moduleClassical_of_isZero X A _
      (DerivedCategory.isZero_of_isGE _ n q (by omega))

private theorem boundedCounit (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (n : ℤ) [K.IsGE n] (hK : IsClassicalComplexFor X Λ K) :
    IsIso ((comparisonAdjunction (ModuleCat.{u + 1} Λ) X)
      |>.mapDerivedCategoryRightDerivedAdjunction.counit.app K) := by
  let : TopologicalSpace Λ := ⊥
  let : DiscreteTopology Λ := ⟨rfl⟩
  let L := comparisonUpperStar (ModuleCat.{u + 1} Λ) X
  let R := comparisonLowerStar (ModuleCat.{u + 1} Λ) X
  let a := (comparisonAdjunction (ModuleCat.{u + 1} Λ) X)
    |>.mapDerivedCategoryRightDerivedAdjunction
  let b := (comparisonAdjunction (ModuleCat.{u + 1} Λ) X).derivedPlus
  let Kp : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) := ⟨K, n, inferInstance⟩
  have hb : IsIso (b.counit.app Kp) :=
    (classicalDerivedEquivalence X Λ).2.1 Kp hK
  let c : L.mapDerivedCategoryPlus ⊣ R.rightDerivedFunctorPlus := a.restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    L.mapDerivedCategoryPlusCompatibility.symm R.rightDerivedFunctorPlusCompatibility.symm
  have hc : IsIso (c.counit.app Kp) := by
    rw [← Adjunction.rightAdjointUniq_hom_app_counit c b Kp]
    infer_instance
  have hm : IsIso (DerivedCategory.Plus.ι.map (c.counit.app Kp)) := inferInstance
  have hw := a.map_restrictFullyFaithful_counit_app
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    L.mapDerivedCategoryPlusCompatibility.symm R.rightDerivedFunctorPlusCompatibility.symm Kp
  rw [hw] at hm
  dsimp only [Iso.symm_inv, Functor.mapDerivedCategoryPlusCompatibility,
    Iso.refl_hom, NatTrans.id_app] at hm
  rw [Category.id_comp] at hm
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ _ hm

/-- Exact inverse image has classical cohomology, and the canonical unbounded derived
counit is invertible on every classical complex (so every such complex is isomorphic to an
inverse image), without any boundedness or constructibility condition.
Reference: Bhatt--Scholze, Proposition 5.2.6(3), Remark 5.2.8 and Proposition 5.3.2.

Proof:
1. Exact inverse image commutes with cohomology, and its image on sheaves is classical.
The standard and small derived-category homology functors are naturally isomorphic.
2. The affine étale module bound gives the uniform bound e = 2 dim(X) + 1.
Descend a classical sheaf to the étale site, realize it over the constant ring sheaf,
and transfer the bound back through the comparison of global sections.
3. On bounded-below objects the unbounded derived adjunction restricts to the usual
bounded-below adjunction. The compatibility isomorphisms and uniqueness of right
adjoints identify their counits. The existing bounded-below classical equivalence
therefore proves invertibility of the actual unbounded counit there.
4. Induction using truncation triangles gives amplitude b + e for derived affine
sections of a classical complex supported in a finite interval ending at b.
Derived sections preserve countable products: use termwise products of K-injectives
and exact products of modules. Exact countable products of pro-étale module sheaves
and the generic left-completeness theorem then give amplitude b + e + 1 for an
arbitrary classical complex supported in degrees at most b.
5. Compute derived sections and comparison direct image on a K-injective complex.
Restriction to the affine étale basis is faithful and exact. If the section complexes
are exact in degree q on that basis, exact sheafification proves exactness of the
direct-image complex in degree q as well.
6. For fixed m put n = m - e - 2. Apply Steps 4 and 5 to tau_{<n} K. Its derived
direct image vanishes in degrees m and m+1, so the truncation triangle makes
H^m(R nu_* K) -> H^m(R nu_* tau_{>=n} K) invertible. Exact inverse image preserves
this isomorphism. Counit naturality and Step 3 now make H^m of the counit at K
invertible. The cohomology criterion proves that the counit itself is invertible.
-/
theorem comparisonUpperStar_isClassicalComplexFor
    (k : Type u) [Field k] (hbase : Finite k ∨ IsAlgClosed k)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (algebraMap ℤ k (ℓ : ℤ)))
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ∃ r : ℕ, 1 ≤ r ∧ (ℓ : A) ^ r = 0)
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))] :
    (∀ M : FiniteCoefficientEtaleDerivedCategory X A,
      IsClassicalComplexFor X A
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj M)) ∧
    (∀ K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)),
      IsClassicalComplexFor X A K →
        IsIso
          ((comparisonAdjunction (ModuleCat.{u + 1} A) X).mapDerivedCategoryRightDerivedAdjunction
            |>.counit.app K)) := by
  have hi := unboundedImage X A
  have hc : ∀ K : DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)),
      IsClassicalComplexFor X A K → IsIso
        ((comparisonAdjunction (ModuleCat.{u + 1} A) X).mapDerivedCategoryRightDerivedAdjunction
          |>.counit.app K) := by
    intro K hK
    let C := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)
    let : Abelian C := inferInstance
    let D := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)
    let : Abelian D := inferInstance
    let L := comparisonUpperStar (ModuleCat.{u + 1} A) X
    have : L.PreservesZeroMorphisms := inferInstance
    let R := comparisonLowerStar (ModuleCat.{u + 1} A) X
    have : R.rightDerivedFunctor.PreservesZeroMorphisms := inferInstance
    let adj := (comparisonAdjunction (ModuleCat.{u + 1} A) X)
      |>.mapDerivedCategoryRightDerivedAdjunction
    let e : ℕ := 2 * ((topologicalKrullDim X).unbotD 0).toNat + 1
    rw [DerivedCategory.isIso_iff]
    intro m
    let n : ℤ := m - e - 2
    let t := DerivedCategory.TStructure.t (C := C)
    let T := (t.truncGE n).obj K
    let J := (t.truncLT n).obj K
    let f : K ⟶ T := (t.truncGEπ n).app K
    have hJ : J.IsLE (n - 1) := t.isLE_truncLT_obj K n (n - 1) (by omega)
    have hclassJ : ∀ q : ℤ, q ≤ n - 1 → IsClassicalModuleFor X A
        ((DerivedCategory.homologyFunctor C q).obj J) := by
      intro q hq
      have := DerivedCategory.isIso_homologyFunctor_map_truncLTι_app K n q (by omega)
      apply moduleClassical_of_iso X A
        (asIso ((DerivedCategory.homologyFunctor C q).map ((t.truncLTι n).app K))).symm
      apply moduleClassical_of_iso X A ((standardHomologyIso X A q).app K).symm
      exact hK q
    have hR : (R.rightDerivedFunctor.obj J).IsLE (n + e) := by
      apply comparison_isLE_of_sections X A J (n + e)
      intro W _
      have hh := section_tail_bound X A ((Scheme.toProEt X).obj W) e
        (fun H hH q hq ↦ fixed_section_bound k hbase ℓ hℓ A hA X W H hH q hq)
        J (n - 1) hclassJ
      convert hh using 1
      dsimp only [e]
      omega
    have hmap : IsIso ((DerivedCategory.homologyFunctor D m).map
        (R.rightDerivedFunctor.map f)) := by
      have htri := R.rightDerivedFunctor.map_distinguished _
        (t.triangleLTGE_distinguished n K)
      exact DerivedCategory.isIso_homologyMap_mor₂ _ htri m (m + 1) rfl
        (DerivedCategory.isZero_of_isLE _ (n + e) m (by dsimp [n]; omega) (hX := hR))
        (DerivedCategory.isZero_of_isLE _ (n + e) (m + 1)
          (by dsimp [n]; omega) (hX := hR))
    have hupper : IsIso ((DerivedCategory.homologyFunctor C m).map
        (L.mapDerivedCategory.map (R.rightDerivedFunctor.map f))) :=
      (NatIso.isIso_map_iff (L.mapDerivedCategoryHomologyFunctorIso m)
        (R.rightDerivedFunctor.map f)).1 (by rw [Functor.comp_map]; infer_instance)
    have hbc : IsIso (adj.counit.app T) :=
      boundedCounit X A T n (classical_truncGE X A K hK n)
    have hf : IsIso ((DerivedCategory.homologyFunctor C m).map f) :=
      DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app K n m (by dsimp [n]; omega)
    have hw := congrArg ((DerivedCategory.homologyFunctor C m).map)
      (adj.counit.naturality f)
    simp only [Functor.map_comp, Functor.id_map, Functor.comp_map] at hw
    have hh : IsIso ((DerivedCategory.homologyFunctor C m).map (adj.counit.app K) ≫
        (DerivedCategory.homologyFunctor C m).map f) := by
      rw [← hw]
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((DerivedCategory.homologyFunctor C m).map f)
  exact ⟨hi, hc⟩

end AlgebraicGeometry.ProEtale
