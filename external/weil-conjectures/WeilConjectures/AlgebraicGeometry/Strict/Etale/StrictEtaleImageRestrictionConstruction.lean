/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleSystemInterfaces
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemUnboundedComparison
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemDerivedComparison
import WeilConjectures.CategoryTheory.Exact.ExactDerivedAdjunctionBounds
import WeilConjectures.CategoryTheory.Scalar.ScalarAdjunctionDescent
import WeilConjectures.Algebra.Homology.System.SystemGrothendieck
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.ShrinkYoneda
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Derived geometric images with their restriction representative equations

Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks 09T5 and 0FND.
The assembly retains the representative equation already proved while constructing
its coefficient restriction square.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u d
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor SheafOfModules Opposite
namespace SheafOfModules

attribute [local instance] CoefficientEvaluationExtensionData.extensionAdditive

section Assembly

universe a av b bv c cv e ev
variable {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{d} A]
  {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{d} B]
  {MA : ℕ → Type c} [∀ n, Category.{cv} (MA n)] [∀ n, Abelian (MA n)]
  [∀ n, HasDerivedCategory.{d} (MA n)]
  {MB : ℕ → Type e} [∀ n, Category.{ev} (MB n)] [∀ n, Abelian (MB n)]
  [∀ n, HasDerivedCategory.{d} (MB n)]
  {eA : ∀ n, A ⥤ MA n} [∀ n, (eA n).Additive]
  {eB : ∀ n, B ⥤ MB n} [∀ n, (eB n).Additive]
  {RA : ∀ {m n : ℕ}, n ≤ m → MA n ⥤ MA m} [∀ m n (h : n ≤ m), (RA h).Additive]
  {RB : ∀ {m n : ℕ}, n ≤ m → MB n ⥤ MB m} [∀ m n (h : n ≤ m), (RB h).Additive]
  {TA : ∀ {m n : ℕ}, n ≤ m → MA m ⥤ MA n} [∀ m n (h : n ≤ m), (TA h).Additive]
  {TB : ∀ {m n : ℕ}, n ≤ m → MB m ⥤ MB n} [∀ m n (h : n ≤ m), (TB h).Additive]
  {atA : ∀ {m n : ℕ} (h : n ≤ m), TA h ⊣ RA h}
  {atB : ∀ {m n : ℕ} (h : n ≤ m), TB h ⊣ RB h}
  {KFA : ∀ n, CochainComplex (MA n) ℤ → Prop} {FlatA : ∀ n, MA n → Prop}
  {KFB : ∀ n, CochainComplex (MB n) ℤ → Prop} {FlatB : ∀ n, MB n → Prop}
  {TN₁ : (∀ {m n : ℕ} (h : n ≤ m), eA m ⟶ eA n ⋙ RA h) → Prop}
  {TN₂ : (∀ {m n : ℕ} (h : n ≤ m), eB m ⟶ eB n ⋙ RB h) → Prop}
  {UN₁ : (∀ n, TA (Nat.le_refl n) ≅ 𝟭 (MA n)) → Prop}
  {UN₂ : (∀ n, TB (Nat.le_refl n) ≅ 𝟭 (MB n)) → Prop}
  {AN₁ : (∀ {l m n : ℕ} (h₁ : m ≤ l) (h₂ : n ≤ m),
    TA h₁ ⋙ TA h₂ ≅ TA (h₂.trans h₁)) → Prop}
  {AN₂ : (∀ {l m n : ℕ} (h₁ : m ≤ l) (h₂ : n ≤ m),
    TB h₁ ⋙ TB h₂ ≅ TB (h₂.trans h₁)) → Prop}

variable (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive] (a : F ⊣ G)
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (Fl : ∀ n, MA n ⥤ MB n) (Gl : ∀ n, MB n ⥤ MA n)
  [∀ n, (Fl n).Additive] [∀ n, (Gl n).Additive] (al : ∀ n, Fl n ⊣ Gl n)
  (PY : CoefficientEvaluationExtensionData eA RA TA atA KFA FlatA TN₁ UN₁ AN₁)
  (PX : CoefficientEvaluationExtensionData eB RB TB atB KFB FlatB TN₂ UN₂ AN₂)
  (α : ∀ n, F ⋙ eB n ≅ eA n ⋙ Fl n)
  (β : ∀ {m n : ℕ} (h : n ≤ m), RA h ⋙ Fl m ≅ Fl n ⋙ RB h)
  (ds : CoefficientDerivedImage F G a)
  (dl : ∀ n, CoefficientDerivedImage (Fl n) (Gl n) (al n))
  (hr : ∀ n (K : CochainComplex (MA n) ℤ),
    ∃ (P : CochainComplex (MA n) ℤ) (q : P ⟶ K), QuasiIso q ∧ KFA n P ∧
      (∀ i : ℤ, FlatA n (P.X i)) ∧ KFB n (((Fl n).mapHomologicalComplex (.up ℤ)).obj P) ∧
        ∀ i : ℤ, FlatB n ((Fl n).obj (P.X i)))
  (hRestr : ∀ {m n : ℕ} (h : n ≤ m),
    IsIso (mateEquiv (al n) (al m) (TwoSquare.mk _ _ _ _ (β h).hom)))
  (hEval : ∀ n,
    IsIso (mateEquiv a (al n) (TwoSquare.mk _ _ _ _ (α n).inv)))
  (hTrans : ∀ {m n : ℕ} (h : n ≤ m) M,
    (PX.strictTransition h).app (F.obj M) ≫ (RB h).map ((α n).hom.app M) =
    (α m).hom.app M ≫ (Fl m).map ((PY.strictTransition h).app M) ≫
      (β h).hom.app ((eA n).obj M))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
include ds dl hr hRestr hEval hTrans in
omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
private theorem open_comparison_assembly :
    ∃ E : CoefficientEvaluationImageData F G a Fl Gl al eA eB
      PY.evaluation PX.evaluation PY.evaluationFactors PX.evaluationFactors α,
    ∃ T : CoefficientScalarImageData (F := F) (G := G) (adj := a)
      (Flevel := Fl) (Glevel := Gl) (adjLevel := al) (eA := eA) (eB := eB)
      (EA := PY.evaluation) (EB := PX.evaluation)
      (factorsA := PY.evaluationFactors) (factorsB := PX.evaluationFactors) (alpha := α)
      (fun {_ _} h ↦ TA h) (fun {_ _} h ↦ RA h) (fun {_ _} h ↦ atA h) KFA FlatA
      (fun {_ _} h ↦ PY.scalar h) (fun {_ _} h ↦ TB h) (fun {_ _} h ↦ RB h)
      (fun {_ _} h ↦ atB h) KFB (fun {_ _} h ↦ PX.scalar h)
      (fun {_ _} h ↦ PY.transition h) (fun {_ _} h ↦ PX.transition h) β E,
    ∀ {m n : ℕ} (h : n ≤ m) (P : CochainComplex (MA n) ℤ),
      (T.restrictedInverse h).hom.app (DerivedCategory.Q.obj P) ≫
        (PX.scalar h).restriction.map ((E.level n).inverseFactors.hom.app P) ≫
        (PX.scalar h).restrictionFactors.hom.app
          (((Fl n).mapHomologicalComplex (.up ℤ)).obj P) =
      (E.level m).inverse.map ((PY.scalar h).restrictionFactors.hom.app P) ≫
        (E.level m).inverseFactors.hom.app
          (((RA h).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (β h) (.up ℤ)).hom.app P) := by
  have he (n : ℕ) := derivedSquare_exists F
    (eA n)
    (eB n) (Fl n)
    ds.inverse (PY.evaluation n) (PX.evaluation n) (dl n).inverse
    ds.inverseFactors (PY.evaluationFactors n) (PX.evaluationFactors n)
    (dl n).inverseFactors (α n)
  have hb {m n : ℕ} (h : n ≤ m) := derivedSquare_exists
    (RA h)
    (Fl n) (Fl m) (RB h)
    (PY.scalar h).restriction (dl n).inverse (dl m).inverse (PX.scalar h).restriction
    (PY.scalar h).restrictionFactors (dl n).inverseFactors
    (dl m).inverseFactors (PX.scalar h).restrictionFactors (β h)
  have ht {m n : ℕ} (h : n ≤ m) : ∃ θ :
      TA h ⋙ (Fl n) ≅
        (Fl m) ⋙ TB h,
      ∀ M, (Fl m).map ((atA h).unit.app M) ≫
        (β h).hom.app ((TA h).obj M) ≫
        (RB h).map (θ.hom.app M) =
          (atB h).unit.app ((Fl m).obj M) := by
    have := hRestr h
    exact tensorSquare_exists (Fl m) (Gl m) (al m)
      (TA h) (RA h)
      (TB h) (RB h)
      (Fl n) (Gl n) (atA h)
      (atB h) (al n) (β h)
  choose δ hδ using @hb
  choose θ hθ using @ht
  have heo (n : ℕ) : ∃ χ : PY.extension n ⋙ F ≅
      (Fl n) ⋙ PX.extension n,
      ∀ M, (Fl n).map ((PY.adj n).unit.app M) ≫
        (α n).inv.app ((PY.extension n).obj M) ≫
        (eB n).map (χ.hom.app M) =
          (PX.adj n).unit.app ((Fl n).obj M) := by
    have : IsIso (mateEquiv a (al n)
        (TwoSquare.mk _ _ _ _ (α n).symm.hom)) := hEval n
    exact tensorSquare_exists (Fl n) (Gl n) (al n)
      (PY.extension n) (eA n)
      (PX.extension n) (eB n)
      F G (PY.adj n) (PX.adj n) a
      (α n).symm
  have hdT {m n : ℕ} (h : n ≤ m) : IsIso
      (derivedLeftSquare
        (TA h) (RA h)
        (TB h) (RB h)
        (atA h) (atB h)
        _ _ (PY.scalar h) (PX.scalar h) (dl m).inverse (dl n).inverse (δ h)) := by
    apply derivedLeftSquare_isIso (Fl m)
      (TA h) (RA h)
      (TB h) (RB h)
      (atA h) (atB h)
      _ _ (PY.scalar h) (PX.scalar h) (Fl n)
      (dl m).inverse (dl n).inverse (dl m).inverseFactors (dl n).inverseFactors
      (β h) (δ h) (hδ h) (θ h).symm
      (tensorSquare_transpose (Fl m)
        (TA h) (RA h)
        (TB h) (RB h)
        (Fl n) (atA h)
        (atB h) (β h) (θ h) (hθ h))
      (fun P ↦ KFA _ P ∧
        KFB m (((Fl m).mapHomologicalComplex (.up ℤ)).obj P))
    · intro K
      obtain ⟨P, q, hq, hp, hf, hfp, _⟩ := hr m K
      exact ⟨P, q, hq, hp, hfp⟩
    · intro P hP
      exact (PY.scalar h).computes P hP.1
    · intro P hP
      exact (PX.scalar h).computes _ hP.2
  choose ev hev using he
  choose χ hχ using heo
  have hdE (n : ℕ) : IsIso
      (derivedLeftSquare (PY.extension n) (eA n)
        (PX.extension n) (eB n) (PY.adj n) (PX.adj n)
        _ _ (extensionPairAbstract PY n) (extensionPairAbstract PX n)
        (dl n).inverse ds.inverse (ev n).symm) := by
    apply derivedLeftSquare_isIso (Fl n)
      (PY.extension n) (eA n)
      (PX.extension n) (eB n) (PY.adj n) (PX.adj n)
      _ _ (extensionPairAbstract PY n) (extensionPairAbstract PX n)
      F (dl n).inverse ds.inverse (dl n).inverseFactors ds.inverseFactors
      (α n).symm (ev n).symm
      (derivedSquare_symm_rep F
        (eA n) (eB n)
        (Fl n) ds.inverse (PY.evaluation n) (PX.evaluation n) (dl n).inverse
        ds.inverseFactors (PY.evaluationFactors n) (PX.evaluationFactors n)
        (dl n).inverseFactors (α n) (ev n) (hev n))
      (χ n).symm
      (tensorSquare_transpose (Fl n) (PY.extension n)
        (eA n) (PX.extension n)
        (eB n) F (PY.adj n) (PX.adj n)
        (α n).symm (χ n) (hχ n))
      (fun P ↦ (KFA _ P ∧
        ∀ i : ℤ, FlatA n (P.X i)) ∧
        (KFB n (((Fl n).mapHomologicalComplex (.up ℤ)).obj P) ∧
        ∀ i : ℤ, FlatB n ((Fl n).obj (P.X i))))
    · intro K
      obtain ⟨P, q, hq, hp, hf, hfp, hff⟩ := hr n K
      exact ⟨P, q, hq, ⟨hp, hf⟩, hfp, hff⟩
    · intro P hP
      exact PY.computes n P hP.1.1 hP.1.2
    · intro P hP
      exact PX.computes n _ hP.2.1 hP.2.2
  have hdEv (n : ℕ) : IsIso (mateEquiv ds.adjunction (dl n).adjunction
      (TwoSquare.mk _ _ _ _ (ev n).inv)) := by
    have := hdE n
    exact fourMate_isIso (dl n).inverse (dl n).direct (dl n).adjunction
      (PY.derivedExtension n) (PY.evaluation n) (PX.derivedExtension n) (PX.evaluation n)
      ds.inverse ds.direct (PY.derivedAdj n) (PX.derivedAdj n) ds.adjunction (ev n).symm (hdE n)
  let de := fun n ↦ (asIso
    (mateEquiv ds.adjunction (dl n).adjunction
      (TwoSquare.mk _ _ _ _ (ev n).inv)))
  let E : CoefficientEvaluationImageData F G a Fl Gl al eA eB
      PY.evaluation PX.evaluation PY.evaluationFactors PX.evaluationFactors α :=
    { system := ds
      level := dl
      inverseEvaluation := ev
      inverseEvaluation_rep := hev
      directEvaluation := de
      counit := fun n M ↦ evaluation_counit_of_mate ds.adjunction (dl n).adjunction
        (ev n) M }
  have hit {m n : ℕ} (h : n ≤ m) (H : DerivedCategory A) :
      (PX.transition h).app (E.system.inverse.obj H) ≫
        (PX.scalar h).restriction.map ((E.inverseEvaluation n).hom.app H) =
      (E.inverseEvaluation m).hom.app H ≫
        (E.level m).inverse.map ((PY.transition h).app H) ≫
        (δ h).hom.app ((PY.evaluation n).obj H) := by
    exact transition_localization F (eA n) (eA m) (eB n) (eB m) (Fl n) (Fl m)
      (RA h) (RB h) E.system.inverse (PY.evaluation n) (PY.evaluation m)
      (PX.evaluation n) (PX.evaluation m) (E.level n).inverse (E.level m).inverse
      (PY.scalar h).restriction (PX.scalar h).restriction E.system.inverseFactors
      (PY.evaluationFactors n) (PY.evaluationFactors m)
      (PX.evaluationFactors n) (PX.evaluationFactors m)
      (E.level n).inverseFactors (E.level m).inverseFactors
      (PY.scalar h).restrictionFactors (PX.scalar h).restrictionFactors
      (α n) (α m) (β h) (E.inverseEvaluation n) (E.inverseEvaluation m) (δ h)
      (PY.strictTransition h) (PX.strictTransition h) (PY.transition h) (PX.transition h)
      (E.inverseEvaluation_rep n) (E.inverseEvaluation_rep m) (hδ h)
      (PY.transition_rep h) (PX.transition_rep h) (hTrans h) H
  have hdR {m n : ℕ} (h : n ≤ m) : IsIso
      (mateEquiv (dl n).adjunction (dl m).adjunction
        (TwoSquare.mk _ _ _ _ (δ h).hom)) := by
    have := hdT h
    exact fourMate_isIso (dl m).inverse (dl m).direct (dl m).adjunction
      (PY.scalar h).derived (PY.scalar h).restriction
      (PX.scalar h).derived (PX.scalar h).restriction
      (dl n).inverse (dl n).direct (PY.scalar h).derivedAdj (PX.scalar h).derivedAdj
      (dl n).adjunction (δ h) (hdT h)
  let dt := fun {m n : ℕ} (h : n ≤ m) ↦ (asIso
    (derivedLeftSquare
      (TA h) (RA h)
      (TB h) (RB h)
      (atA h) (atB h)
      _ _ (PY.scalar h) (PX.scalar h) (dl m).inverse (dl n).inverse (δ h))).symm
  let rd := fun {m n : ℕ} (h : n ≤ m) ↦ (asIso
    (mateEquiv (dl n).adjunction (dl m).adjunction
      (TwoSquare.mk _ _ _ _ (δ h).hom))).symm
  refine ⟨E, {
    tensor := θ
    tensor_unit := hθ
    derivedTensor := dt
    derivedTensor_rep := ?_
    restrictedDirect := rd
    restrictedDirect_mate := ?_
    restrictedInverse := δ
    restrictedInverse_mate := ?_
    inverseTransition := ?_
    directTransition := ?_ }, ?_⟩
  · intro m n h P _ _
    apply (cancel_epi ((dt h).inv.app (DerivedCategory.Q.obj P))).1
    simp only [Iso.inv_hom_id_app_assoc]
    have hh := derivedLeftSquare_rep (Fl m)
      (TA h) (RA h)
      (TB h) (RB h)
      (atA h) (atB h)
      _ _ (PY.scalar h) (PX.scalar h) (Fl n)
      (dl m).inverse (dl n).inverse (dl m).inverseFactors (dl n).inverseFactors
      (β h) (δ h) (hδ h) (θ h).symm
      (tensorSquare_transpose (Fl m)
        (TA h) (RA h)
        (TB h) (RB h)
        (Fl n) (atA h)
        (atB h) (β h) (θ h) (hθ h)) P
    change _ = _ ≫ (_ ≫ _ ≫ _)
    slice_rhs 1 3 => exact hh
    simp only [Category.assoc, ← DerivedCategory.Q.map_comp]
    rw [show (NatIso.mapHomologicalComplex (θ h).symm (.up ℤ)).hom.app P ≫
      (NatIso.mapHomologicalComplex (θ h) (.up ℤ)).hom.app P = 𝟙 _ from
        (NatIso.mapHomologicalComplex (θ h) (.up ℤ)).inv_hom_id_app P]
    erw [DerivedCategory.Q.map_id, Category.comp_id]
  · intro m n h A B f
    apply (cancel_mono ((rd h).inv.app B)).1
    simp only [Category.assoc, Iso.hom_inv_id_app]
    erw [Category.comp_id]
    exact doubleMate_homEquiv (dl m).inverse (dl m).direct (dl m).adjunction
      (PY.scalar h).derived (PY.scalar h).restriction
      (PX.scalar h).derived (PX.scalar h).restriction
      (dl n).inverse (dl n).direct (PY.scalar h).derivedAdj (PX.scalar h).derivedAdj
      (dl n).adjunction (δ h) A B f
  · intro m n h A
    rw [Adjunction.homEquiv_unit]
    exact (unit_mateEquiv (dl n).adjunction (dl m).adjunction
      (TwoSquare.mk _ _ _ _ (δ h).hom) A).symm
  · intro m n h H
    exact hit h H
  · intro m n h M
    apply (cancel_mono ((rd h).inv.app ((PX.evaluation n).obj M))).1
    simp only [Category.assoc, Iso.hom_inv_id_app]
    erw [Category.comp_id]
    exact transition_mates ds.adjunction (dl m).adjunction (dl n).adjunction
      (PY.scalar h).restriction (PX.scalar h).restriction
      (PY.evaluation m) (PY.evaluation n) (PX.evaluation m) (PX.evaluation n)
      (ev m) (ev n) (δ h) (PY.transition h) (PX.transition h)
      (fun H ↦ hit h H) M
  · exact fun h P ↦ hδ h P

end Assembly

end SheafOfModules
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Construct the derived image while retaining its ordinary restriction square formula.
Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks 09T5 and 0FND
(blueprint: lem-pur-strict-etale-image-restriction-construction).
Proof: repeat coefficientSystemUnboundedComparison's assembly, retaining the
representative equation of the localized ordinary restriction square. The exact
inverse images and K-injective right images give normalized adjunctions. The derived
evaluation comparison is obtained from the ordinary one by localization; its mate
is invertible by the level extension/evaluation adjunction. Flat-term K-flat
resolutions give the tensor comparison and its mate restrictedDirect. The chosen
restrictedInverse is the localized ordinary square itself, so its factorization
formula is retained as the final conclusion. The existing exact-adjunction bound,
conservativity and scalar-transpose lemmas supply the descent fields. -/
public theorem strictEtaleImageWithRestriction_exists
    (O : Type (u + 1)) [CommRing O] (t : O)
    {X Z : Scheme.{u}} (j : X ⟶ Z)
    (I : StrictEtaleOrdinaryImage O t j)
    (PZ : StrictEtaleEvaluation Z O t) (PX : StrictEtaleEvaluation X O t)
    : ∃ D : CoefficientSystemDerivedImage (J := Z.smallEtaleTopology)
      (K := X.smallEtaleTopology) O t _ _ _ I PZ PX,
    ∀ {m n : ℕ} (h : n ≤ m) (P : CochainComplex (strictEtaleLevel Z O t n) ℤ),
    (D.restrictedInverse h).hom.app (DerivedCategory.Q.obj P) ≫
      (PX.scalar h).restriction.map ((D.level n).inverseFactors.hom.app P) ≫
      (PX.scalar h).restrictionFactors.hom.app
        ((((I.lift n).modules).mapHomologicalComplex (.up ℤ)).obj P) =
    (D.level m).inverse.map ((PZ.scalar h).restrictionFactors.hom.app P) ≫
      (D.level m).inverseFactors.hom.app
        (((coefficientRestriction (J := Z.smallEtaleTopology) O t h).mapHomologicalComplex
          (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (I.restrictInverse h) (.up ℤ)).hom.app P) := by
  have : HasWeakSheafify Z.smallEtaleTopology AddCommGrpCat.{u + 1} := inferInstance
  have : HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1} := inferInstance
  let := strictRingSystem_isGrothendieckAbelian
    (coefficientRings (J := X.smallEtaleTopology) (O := O) (ell := t))
  let : IsGrothendieckAbelian.{u + 1} (CoefficientSystem (J := X.smallEtaleTopology) O t) :=
    IsGrothendieckAbelian.of_equivalence
      (coefficientSystemEquivalence (J := X.smallEtaleTopology) (O := O) (ell := t)).symm
  let (n : ℕ) : IsGrothendieckAbelian.{u + 1}
      (coefficientLevelModules (J := X.smallEtaleTopology) O t n) :=
    isGrothendieckAbelian_coefficientUniverse _
  let : PreservesFiniteLimits I.inverse := I.systemExact.1
  let : PreservesFiniteColimits I.inverse := I.systemExact.2
  let (n : ℕ) : PreservesFiniteLimits (I.lift n).modules := (I.inverseExact n).1
  let (n : ℕ) : PreservesFiniteColimits (I.lift n).modules := (I.inverseExact n).2
  let : HasDerivedCategory.{u + 2} (strictEtaleCoefficientSystem Z O t) :=
    strictEtaleSystemDerived Z O t
  let : HasDerivedCategory.{u + 2} (strictEtaleCoefficientSystem X O t) :=
    strictEtaleSystemDerived X O t
  let (n : ℕ) : HasDerivedCategory.{u + 2} (strictEtaleLevel Z O t n) :=
    strictEtaleLevelDerived Z O t n
  let (n : ℕ) : HasDerivedCategory.{u + 2} (strictEtaleLevel X O t n) :=
    strictEtaleLevelDerived X O t n
  obtain ⟨ds⟩ := derivedImage_exists I.inverse I.rightSystem I.systemAdj
  have hl (n : ℕ) : Nonempty
      (CoefficientDerivedImage (I.lift n).modules (I.right n) (I.levelAdj n)) :=
    derivedImage_exists (I.lift n).modules (I.right n) (I.levelAdj n)
  have dl : ∀ n, CoefficientDerivedImage (I.lift n).modules (I.right n) (I.levelAdj n) :=
    fun n ↦ Classical.choice (hl n)
  obtain ⟨E, T, hT⟩ := open_comparison_assembly I.inverse I.rightSystem I.systemAdj
    (fun n ↦ (I.lift n).modules) I.right I.levelAdj PZ PX
    I.inverseEvaluation (fun {_ _} h ↦ I.restrictInverse h) ds dl
    (fun n ↦ exists_adapted_resolution
      (coefficientQuotientSheaf (J := Z.smallEtaleTopology) O t n)
      (coefficientQuotientSheaf (J := X.smallEtaleTopology) O t n)
      (Scheme.etaleSetPullback j) _ (strictEtaleSetAdjunction j)
      (I.lift n).modules (I.right n) (I.levelAdj n) (I.rightUnderlying n))
    (fun {_ _} h ↦ ordinaryRestrictionMate_isIso O t _ _ _ I h)
    (fun n ↦ show IsIso (mateEquiv I.systemAdj (I.levelAdj n)
      (TwoSquare.mk _ _ _ _ (I.inverseEvaluation n).inv)) by
        rw [ordinaryEvaluationMate_eq O t _ _ _ I n]
        infer_instance)
    (fun {_ _} h ↦ ordinaryInverseTransition O t _ _ _ I PZ PX h)
  let U : CoefficientSystemUnboundedImage (J := Z.smallEtaleTopology)
      (K := X.smallEtaleTopology) O t _ _ _ I PZ PX := {
        evaluation := E
        scalar := T }
  let image := U.evaluation
  let scalar := U.scalar
  refine ⟨{ construction := U
            detectsIso := coefficientEvaluation_detectsIso O t PX
            boundedBelow := ?_
            origin := ?_ }, hT⟩
  · rintro M ⟨a, ha⟩
    exact ⟨a, exactDerivedAdjunction_isGE I.inverse image.system.inverse
      image.system.inverseFactors image.system.adjunction M a⟩
  · intro hfull M hM horigin
    have hc (n : ℕ) :
        IsIso ((image.level n).adjunction.counit.app ((PX.evaluation n).obj M)) := by
      obtain ⟨H, hH, ⟨e⟩⟩ := horigin n
      exact exactDerivedAdjunction_counit_isIso_of_origin (I.lift n).modules
        (image.level n).inverse (image.level n).inverseFactors
        (image.level n).adjunction (hfull n) _ H hH e
    constructor
    · apply (coefficientEvaluation_detectsIso O t PX _).2
      intro n
      rw [← image.counit n M]
      infer_instance
    · intro hnorm m n h
      have hreflect : (image.level n).inverse.ReflectsIsomorphisms :=
        exactDerived_reflectsIso_of_boundedBelow_faithful (I.lift n).modules
          (image.level n).inverse (image.level n).inverseFactors
          (fun A B hA hB ↦ (hfull n A B hA hB).1)
      have hnorm' := hnorm h
      exact isIso_scalar_transpose_of_mate (PZ.scalar h).derivedAdj
        (PX.scalar h).derivedAdj (image.level m).adjunction (image.level n).adjunction
        (scalar.derivedTensor h) (scalar.restrictedDirect h) (scalar.restrictedDirect_mate h)
        ((image.directEvaluation m).app M) ((image.directEvaluation n).app M)
        ((PZ.transition h).app (image.system.direct.obj M)) ((PX.transition h).app M)
        (scalar.directTransition h M)

end AlgebraicGeometry
