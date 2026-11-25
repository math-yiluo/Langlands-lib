/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackReductionData
import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantPresentationTransport
import WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackReductionArrowIsIso
import WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackReductionCoherence
import all WeilConjectures.AlgebraicGeometry.CompletedConstantAlgebraFlatQuotients
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Sites.CoverLifting
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement

/-! # Finite reduction of completed pullback

The canonical finite interface is in `CompletedPullbackReductionData`.
Source: Stacks Tag 099N (5).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry.Scheme
variable {X Y : Scheme.{u}} (g : X ⟶ Y) {A : Type (u + 1)} [CommRing A]
variable (d : AdicCoefficientDatum A)

open AlgebraicGeometry.ProEtale in
/-- Every finite coefficient projection is sectionwise surjective. Kept here, as in the
published module, for the modules that read it through `import all` of this module.
Source: Stacks Tag 099N (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: identify the projection with the limit projection of the constant quotient
system; constant sections lift through the completed constant comparison. -/
private theorem projection_surjective {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (T : Scheme.{u}) (n : ℕ) (U : T.ProEtᵒᵖ) :
    Function.Surjective ((completedReductionProjection T d n).hom.app U) := by
  let := d.noetherian
  let e := pbcCompletedComparison T d
  let c := CompletedConstantReduction.base T d.ideal ≫ e.hom
  have hc (m : ℕ) : c ≫ e.inv ≫
      limit.π (adicLisseRingSystem T d.ideal) (op m) =
      (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (m + 1)))) := by
    dsimp only [c]
    rw [Category.assoc, e.hom_inv_id_assoc]
    exact (CompletedConstantReduction.base_exists T d.ideal).choose_spec.1 m
  have hp : completedReductionProjection T d n =
      e.inv ≫ limit.π (adicLisseRingSystem T d.ideal) (op n) ≫
        (pbcLevelConstantComparison T d n).hom := by
    dsimp only [e, pbcCompletedComparison]
    rw [HasLimit.isoOfNatIso_inv_π_assoc]
    simp [pbcConstantSystemComparison, completedReductionProjection]
    rfl
  exact (CompletedConstantAlgebra.projection_surjective_and_kernel T d.ideal e c hc n
    (pbcLevelConstantComparison T d n) (completedReductionProjection T d n) hp U).1

/-- The unit-preserving coefficient presentation detects completeness of any
representative of an intrinsic completion. -/
private theorem complete_of_intrinsicCompletion_iso
    (r : ℕ) (f : Fin r → A) (hf : Ideal.span (Set.range f) = d.ideal)
    (N L : DerivedCategory (pbcModules X (pbcAdicCompletion X d)))
    (C : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ)
    (e : DerivedCategory.Q.obj C ≅ N)
    (α : L ≅ intrinsicCompletion X d r f hf N C e)
    (P : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ)
    (eP : DerivedCategory.Q.obj P ≅ L) :
    IsDerivedCompleteIntrinsic X d r f hf L P eP := by
  classical
  have : IsNoetherianRing A := d.noetherian
  obtain ⟨D⟩ := completed_constant_presentation_transport X d
  let F := D.equivalence.functor
  let G := ConstantCompletion.completion (completedCechTopology X) A d.ideal true
  let η := ConstantCompletion.completionUnit (completedCechTopology X) A d.ideal true
  obtain ⟨_, _, hcomplete, _, hcriterion⟩ := ConstantCompletion.koszul_quotient_reflector
    (completedCechTopology X) A d.ideal true r f hf
  obtain ⟨j, _⟩ := D.koszul r f hf C
  let k : F.obj (DerivedCategory.Q.obj P) ≅ G.obj (F.obj N) :=
    F.mapIso (eP ≪≫ α) ≪≫ j ≪≫ G.mapIso (F.mapIso e)
  have hη : IsIso (η.app (G.obj (F.obj N))) :=
    (hcriterion _).mpr (hcomplete _)
  have hηP : IsIso (η.app (F.obj (DerivedCategory.Q.obj P))) :=
    (η.isIso_app_iff_of_iso k).mpr hη
  obtain ⟨i, hi⟩ := D.koszul r f hf P
  have hm : IsIso (F.map (DerivedCategory.Q.map
      (intrinsicCompletionComplexUnit X d r f P)) ≫ i.hom) := by
    rw [hi]
    exact hηP
  have : IsIso (F.map (DerivedCategory.Q.map
      (intrinsicCompletionComplexUnit X d r f P))) :=
    IsIso.of_isIso_comp_right _ i.hom
  have : IsIso (DerivedCategory.Q.map (intrinsicCompletionComplexUnit X d r f P)) :=
    isIso_of_reflects_iso _ F
  unfold IsDerivedCompleteIntrinsic intrinsicCompletionUnit
  infer_instance

private theorem adjunct_composite_natural
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (L : D ⥤ E) (R : E ⥤ D) (adj : L ⊣ R)
    (T : C ⥤ F) (B V : F ⥤ D) (H : C ⥤ E)
    (p : B ⟶ V) (e : T ⋙ V ⟶ H ⋙ R)
    {K K' : C} (v : K ⟶ K') :
    L.map (B.map (T.map v)) ≫ (adj.homEquiv _ _).symm
        (p.app (T.obj K') ≫ e.app K') =
      (adj.homEquiv _ _).symm (p.app (T.obj K) ≫ e.app K) ≫ H.map v := by
  rw [← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_right_symm]
  apply congrArg (adj.homEquiv _ _).symm
  rw [← Category.assoc, p.naturality, Category.assoc]
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg (p.app (T.obj K) ≫ ·) (e.naturality v)

/-- Reduction of completed pullback, including the actual projection-induced arrows,
functoriality, transition maps, normalization, quotient cocycle and equal-index unit.
The parameter n denotes the positive level n+1; representatives are arbitrary.
No boundedness, nonempty scheme, nonzero ring, or nonempty generator tuple is required.

Source: blueprint order 1262; Stacks Tag 099N (5)
(blueprint: definition-completed-inverse-image).

Proof:
1. Restrict to constant A-coefficients using lem-weil-pbc-constant-completion-equivalence.
The defining pulled strict tower becomes the reduction tower of ordinary pullback N,
including its quotient units and finite projections; no infinite limit is pulled back.
2. Apply lem-weil-pbc-ringed-koszul-completion-reflector. Its completed value is complete.
The constant/completed comparison identifies its Koszul unit with the unit for L;
exact scalar restriction reflects invertibility, giving intrinsic completeness over A_X.
3. Use the strict-perfect coefficient package and projection-formula totalization to
commute reduction by P_a with the Koszul derived limit. On the tail m>=a the reduced
Koszul differential vanishes. The degree-zero summand is constant N_a; negative
summands have zero transition across a gap of a. The strict-tower homotopy-limit
lemma kills their derived limit, and also permits discarding the finite initial tail.
The product triangle computes the constant tower as N_a by finite partial sums.
Thus reduction of the completion unit is invertible.
4. The projection-induced arrow composed with that reduced unit is identity by the
normalized scalar adjunction: x tensor s maps to (x tensor 1)s. Hence alpha is the
inverse of the reduced unit. Natural finite comparisons give functoriality.
5. Naturality of tensoring the single completion unit with each quotient gives the
transition square. Apply scalar associativity to the same unit and invert its
reductions to obtain normalization compatibility. Associativity of scalar multiplication
in the ordinary balanced formulas gives the quotient cocycle; the identity quotient
gives the stated unitor. All maps here are the uniquely normalized maps above. -/
theorem completedPullback_reduction
    (r : ℕ) (f : Fin r → A) (hf : Ideal.span (Set.range f) = d.ideal)
    (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)))
    (C : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ)
    (e : DerivedCategory.Q.obj C ≅ K)
    (_hK : IsDerivedCompleteIntrinsic Y d r f hf K C e) :
    (∀ (P : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ)
      (eP : DerivedCategory.Q.obj P ≅ completedPullbackObject g d K),
      IsDerivedCompleteIntrinsic X d r f hf (completedPullbackObject g d K) P eP) ∧
    (∀ n : ℕ, IsIso (completedPullbackReductionArrow g d K n)) ∧
    (∀ (K' : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)))
      (C' : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ)
      (e' : DerivedCategory.Q.obj C' ≅ K')
      (_hK' : IsDerivedCompleteIntrinsic Y d r f hf K' C' e') (v : K ⟶ K') (n : ℕ),
      (reductionDerivedChange X (completedReductionProjection X d n)).map
          ((completedPullbackFunctor g d).map v) ≫ completedPullbackReductionArrow g d K' n =
        completedPullbackReductionArrow g d K n ≫
          (completedReductionFiniteTarget g d n).map v) ∧
    (∀ (a b : ℕ) (h : a ≤ b),
      IsIso (completedReductionTargetNormalization g d K a b h) ∧
      ((pbcDerivedScalarAdjunction (reductionCoefficientMap X d b a h)).homEquiv _ _
          ((completedPullbackSourceNormalization d X a b h (completedPullbackObject g d K)).hom)) ≫
            (pbcDerivedRestrict (reductionCoefficientMap X d b a h)).map
              (completedPullbackReductionArrow g d K a) =
        completedPullbackReductionArrow g d K b ≫
          (completedReductionTargetTransition g d a b h).app K) ∧
    (∀ (a b : ℕ) (h : a ≤ b),
      (reductionDerivedChange X (reductionCoefficientMap X d b a h)).map
          (completedPullbackReductionArrow g d K b) ≫
            completedReductionTargetNormalization g d K a b h =
        (completedPullbackSourceNormalization d X a b h (completedPullbackObject g d K)).hom ≫
          completedPullbackReductionArrow g d K a) ∧
    (∀ (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c),
      (reductionDerivedChange X (reductionCoefficientMap X d b a hab)).map
          (completedReductionTargetNormalization g d K b c hbc) ≫
            completedReductionTargetNormalization g d K a b hab =
        (completedReductionQuotientAssoc d X a b c hab hbc
            ((completedReductionFiniteTarget g d c).obj K)).hom ≫
          completedReductionTargetNormalization g d K a c (hab.trans hbc)) ∧
    ∀ a : ℕ, completedReductionTargetNormalization g d K a a (le_refl a) =
      completedReductionUnit d X a ((completedReductionFiniteTarget g d a).obj K) := by
  refine ⟨?_, ?_⟩
  · let N := (completedOrdinaryPullback g d).obj K
    let D := DerivedCategory.Q.objPreimage N
    let eD := DerivedCategory.Q.objObjPreimageIso N
    obtain ⟨α, _⟩ := completedPullback_isCompletion g d r f hf K C e _hK D eD
    intro P eP
    exact complete_of_intrinsicCompletion_iso d r f hf N _ D eD α P eP
  · refine ⟨?_, ?_, ?_⟩
    · exact completedPullbackReductionArrow_isIso g d r f hf K C e _hK
    · intro K' C' e' hK' v n
      exact adjunct_composite_natural _ _
        (pbcDerivedScalarAdjunction (completedReductionProjection X d n))
        (completedReductionTower Y d ⋙ completedTowerPullback g d)
        (completedTowerRlim d X) (pbcTowerEvaluation X (pbcAdicCompletion X d) n)
        (completedReductionFiniteTarget g d n)
        (completedReductionLimitProjection d (X := X) n)
        (completedReductionFiniteEvaluation g d n).hom v
    · exact completedPullbackReduction_coherence g d K
        (completedPullbackReductionArrow_isIso g d r f hf K C e _hK)

end AlgebraicGeometry.Scheme
