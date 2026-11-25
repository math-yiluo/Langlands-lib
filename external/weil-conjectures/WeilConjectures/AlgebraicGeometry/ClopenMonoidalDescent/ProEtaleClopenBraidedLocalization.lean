/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClopenMonoidalDescent.ProEtaleClopenMonoidalNormalization
import WeilConjectures.CategoryTheory.Normalized.NormalizedBraidedLocalization
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
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
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex

/-! # Braided localization of degreewise clopen restriction

Source: Stacks Project, Tags 06YS, 0G7D, 06YU and 0FPT.
(blueprint: lem-pur-clopen-braided-localization).
-/

@[expose] public noncomputable section

attribute [-instance] CategoryTheory.Functor.mapCochainComplexMonoidal
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.modulesAbelian
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.hasDerived

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe t u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open WeilConjectures

attribute [local irreducible] DerivedCategory.Q Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors SheafOfModules.monoidalCategory
  SheafOfModules.symmetricCategory
  RingedDerivedNative.monoidal
  RingedDerivedNative.symmetric HasDerivedCategory.standard SheafOfModules.pushforward

attribute [local instance 20000] instMonoidalCategoryHomologicalComplexIntUp_weilConjectures
  RingedDerivedNative.moduleClosed SheafOfModules.cochainModulesMonoidal
  SheafOfModules.cochainModulesSymmetric SheafOfModules.cochainModulesPreadditive

namespace CategoryTheory

private theorem cochainKFlatCriterion {A : Type*} [Category* A] [Abelian A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
    [∀ (j : ℤ), HasColimitsOfShape
      (Discrete ((ComplexShape.up ℤ).π (.up ℤ) (.up ℤ) ⁻¹' {j})) A]
    [∀ (X Y : GradedObject ℤ A), X.HasTensor Y]
    [∀ X, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X)]
    [∀ X, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X)]
    [∀ (W X Y Z : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt W X Y Z]
    [∀ (X Y Z : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X Y Z]
    [∀ (X Y Z : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    (P : CochainComplex A ℤ) :
    (∀ Z : CochainComplex A ℤ, Z.Acyclic → (Z ⊗ P).Acyclic) ↔
      (HomologicalComplex.quasiIso A (.up ℤ)).kFlat P := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff P,
    HomotopyCategory.kFlat_iff_preserves_acyclic
      ((HomotopyCategory.quotient A (.up ℤ)).obj P)]
  constructor
  · intro hP Z hZ
    obtain ⟨Z, rfl⟩ := Z.quotient_obj_surjective
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hZ
    have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
      (CochainComplex.mapBifunctor Z P (curriedTensor _))).2 (hP Z hZ)
    exact ⟨(HomotopyCategory.subcategoryAcyclic _).prop_of_iso
      ((HomotopyCategory.quotient _ _).mapIso (β_ Z P)) hr, hr⟩
  · intro hP Z hZ
    exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1
      (hP _ ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic Z).2 hZ)).2

end CategoryTheory

namespace AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent

/-- Any braided structure on degreewise restriction descends to the specified exact
restriction, with monoidal canonical localization comparison.

Source: Stacks Project, Tags 06YS, 0G7D, 06YU and 0FPT.
(blueprint: lem-pur-clopen-braided-localization).

Proof: The acyclic-tensor criterion is equivalent to categorical K-flatness, using the
homotopy quotient and symmetry for the other tensor order. Functorial flat resolutions
supply the K-flat left derivability structure. Every derived object has a cochain preimage;
its independent-coefficient K-flat resolution gives an isomorphic localized K-flat model.
The hypothesis hk preserves these models. The native localization functors are lax braided,
with invertible units and tensorators on K-flat inputs. Apply normalizedBraidedLocalization
to these functors and the canonical exact-restriction factorization. This gives the claimed
braided structure and the monoidal factorization. No nonempty or nonzero assumption is used. -/
theorem clopen_braided_localization
    {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (c : (clopenTensorComplexRestriction.{t, u} j R).Braided)
    (hk : ∀ P : CochainComplex (clopenTensorModules.{t, u} R) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (J := topology X) (R := R) P →
      CochainComplex.IsKFlatIndependentCoefficients (J := topology Y)
        (R := (clopenTensorRings.{t, u} j).obj R)
        ((clopenTensorComplexRestriction.{t, u} j R).obj P)) :
    letI := c
    letI := RingedDerivedNative.laxBraided.{t + 1, t, u, max (u + 1) (t + 2)} (topology X) R
    letI := RingedDerivedNative.laxBraided.{t + 1, t, u, max (u + 1) (t + 2)}
      (topology Y) ((clopenTensorRings.{t, u} j).obj R)
    ∃ d : (derivedRestriction.{t, u} j R).Braided, letI := d
      NatTrans.IsMonoidal (factors.{t, u} j R).hom := by
  let RY := (clopenTensorRings.{t, u} j).obj R
  let Fc := clopenTensorComplexRestriction.{t, u} j R
  let G := derivedRestriction.{t, u} j R
  let QX : CochainComplex (clopenTensorModules.{t, u} R) ℤ ⥤
      DerivedCategory (clopenTensorModules.{t, u} R) := DerivedCategory.Q
  let QY : CochainComplex (clopenTensorModules.{t, u} RY) ℤ ⥤
      DerivedCategory (clopenTensorModules.{t, u} RY) := DerivedCategory.Q
  let W := HomologicalComplex.quasiIso (clopenTensorModules.{t, u} R) (.up ℤ)
  let := c
  let := RingedDerivedNative.laxBraided.{t + 1, t, u,
    max (u + 1) (t + 2)} (topology X) R
  let := RingedDerivedNative.laxBraided.{t + 1, t, u,
    max (u + 1) (t + 2)} (topology Y) RY
  let : IsGrothendieckAbelian.{max u (t + 1)} (clopenTensorModules.{t, u} R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses
      (topology X) R).1
  let : Abelian.HasFunctorialFlatResolution (clopenTensorModules.{t, u} R) :=
    SheafOfModules.hasFunctorialFlatResolution_kfi R
  have ktest (P : CochainComplex (clopenTensorModules.{t, u} R) ℤ) :
      CochainComplex.IsKFlatIndependentCoefficients (J := topology X) (R := R) P ↔
        W.kFlat P := CategoryTheory.cochainKFlatCriterion P
  have : W.localizerMorphismKFlat.IsLeftDerivabilityStructure := inferInstance
  have : IsIso (Functor.LaxMonoidal.ε QX) :=
    RingedDerivedNative.isIso_ε.{t + 1, t, u, max (u + 1) (t + 2)} (topology X) R
  have : IsIso (Functor.LaxMonoidal.ε QY) :=
    RingedDerivedNative.isIso_ε.{t + 1, t, u, max (u + 1) (t + 2)} (topology Y) RY
  exact normalizedBraidedLocalization QX QY Fc G (factors.{t, u} j R) W
    (fun Z ↦ by
      let K := QX.objPreimage Z
      obtain ⟨P, f, hP, _, hf, _⟩ :=
        CochainComplex.exists_isKFlatResolutionIndependentCoefficients K
      exact ⟨P, (ktest P).1 hP,
        ⟨Localization.isoOfHom QX W f hf ≪≫ QX.objObjPreimageIso Z⟩⟩)
    (fun P Q hQ ↦ RingedDerivedNative.isIso_mu.{t + 1, t, u, max (u + 1) (t + 2)} (topology X) R P Q
      (Or.inr ((ktest Q).2 hQ)))
    (fun P Q hQ ↦ RingedDerivedNative.isIso_mu.{t + 1, t, u, max (u + 1) (t + 2)}
      (topology Y) RY P (Fc.obj Q)
      (Or.inr (hk Q ((ktest Q).2 hQ))))

end AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent
