/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationDerivedLeftAdjoint
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonDerived
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Homology.CoefficientSystemDerivedImage.CoefficientSystemImageData
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemOrdinaryImages
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemUnboundedComparison
import WeilConjectures.CategoryTheory.Exact.ExactDerivedAdjunctionBounds
import WeilConjectures.CategoryTheory.Scalar.ScalarAdjunctionDescent
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Direct image and evaluation of strict coefficient systems

Source: Zheng, Six Operations and Lefschetz--Verdier, Construction 4.1, printed p. 21,
and Lemma 4.10, printed pp. 23--24
(blueprint: lem-pur-coefficient-system-derived-comparison).

The index `n` denotes the positive exponent `n+1`. All systems, evaluation functors,
scalar extensions and adjoint transitions are the recorded coefficient-evaluation
interface. The structures below specify the geometric lifts and the comparison,
including their normalizations; they are conclusions, not hypotheses of the theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v u' v' w d a b av bv
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}]
  [HasWeakSheafify J (Type w)]
  [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  (O : Type w) [CommRing O] (ell : O)

variable {D : Type u'} [Category.{v'} D] [EssentiallySmall.{w} C]
  [EssentiallySmall.{w} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [HasWeakSheafify K CommRingCat.{w}] [HasWeakSheafify K (Type w)]
  [K.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
  (V : Sheaf K (Type w) ⥤ Sheaf J (Type w)) (adj : L ⊣ V)

omit [EssentiallySmall.{w} D] [HasWeakSheafify K (Type w)]
  [K.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})] in
private theorem system_hom_ext {M N : CoefficientSystem (J := K) O ell}
    (f g : M ⟶ N) (h : f.app = g.app) : f = g := by
  cases f
  cases g
  cases h
  rfl

omit [EssentiallySmall.{w} D] [HasWeakSheafify K (Type w)]
  [K.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})] in
private theorem coefficientEvaluation_jointlyReflects :
    JointlyReflectIsomorphisms (coefficientEvaluation (J := K) (O := O) (ell := ell)) where
  isIso {M N} f hf := by
    have hi (n : ℕ) : IsIso (f.app n) := hf n
    let g : N ⟶ M := {
      app := fun n ↦ inv (f.app n)
      comm := by
        intro n
        apply (cancel_epi (f.app (n + 1))).mp
        simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
        rw [f.comm, Category.assoc]
        simp only [← Functor.map_comp, IsIso.hom_inv_id]
        rw [(coefficientRestriction (J := K) O ell (Nat.le_succ n)).map_id]
        exact (Category.comp_id _).symm }
    refine ⟨g, ?_, ?_⟩
    · apply system_hom_ext O ell
      funext n
      change f.app n ≫ inv (f.app n) = 𝟙 _
      exact IsIso.hom_inv_id _
    · apply system_hom_ext O ell
      funext n
      change inv (f.app n) ≫ f.app n = 𝟙 _
      exact IsIso.inv_hom_id _

omit [EssentiallySmall.{w} D] [HasWeakSheafify K (Type w)]
  [K.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})] in
private theorem coefficientEvaluation_limits (n : ℕ) :
    PreservesFiniteLimits (coefficientEvaluation (J := K) (O := O) (ell := ell) n) :=
  (coefficientEvaluation_exact n).1

omit [EssentiallySmall.{w} D] [HasWeakSheafify K (Type w)]
  [K.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})] in
private theorem coefficientEvaluation_colimits (n : ℕ) :
    PreservesFiniteColimits (coefficientEvaluation (J := K) (O := O) (ell := ell) n) :=
  (coefficientEvaluation_exact n).2

attribute [local instance] coefficientEvaluation_limits coefficientEvaluation_colimits

variable [∀ n : ℕ, HasDerivedCategory.{d} (coefficientLevelModules (J := J) O ell n)]
  [∀ n : ℕ, HasDerivedCategory.{d} (coefficientLevelModules (J := K) O ell n)]
  [HasDerivedCategory.{d} (CoefficientSystem (J := J) O ell)]
  [HasDerivedCategory.{d} (CoefficientSystem (J := K) O ell)]

private def coefficientEvaluation_derivedIso
    (P : CoefficientEvaluationDerivedPackage (J := K) (O := O) (ell := ell)) (n : ℕ) :
    P.evaluation n ≅
      (coefficientEvaluation (J := K) (O := O) (ell := ell) n).mapDerivedCategory := by
  have : PreservesFiniteLimits
      (coefficientEvaluation (J := K) (O := O) (ell := ell) n) :=
    (coefficientEvaluation_exact n).1
  have : PreservesFiniteColimits
      (coefficientEvaluation (J := K) (O := O) (ell := ell) n) :=
    (coefficientEvaluation_exact n).2
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (CoefficientSystem (J := K) O ell) (.up ℤ))
    (DerivedCategory.Q ⋙ P.evaluation n)
    (DerivedCategory.Q ⋙
      (coefficientEvaluation (J := K) (O := O) (ell := ell) n).mapDerivedCategory)
    (P.evaluation n)
    (coefficientEvaluation (J := K) (O := O) (ell := ell) n).mapDerivedCategory
    (P.evaluationFactors n ≪≫
      (coefficientEvaluation (J := K) (O := O) (ell := ell) n).mapDerivedCategoryFactors.symm)

omit [HasWeakSheafify K (Type w)]
  [K.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})] in
private theorem coefficientEvaluation_detectsIso
    (P : CoefficientEvaluationDerivedPackage (J := K) (O := O) (ell := ell))
    {M N : DerivedCategory (CoefficientSystem (J := K) O ell)} (f : M ⟶ N) :
    IsIso f ↔ ∀ n : ℕ, IsIso ((P.evaluation n).map f) := by
  have hlim (n : ℕ) : PreservesFiniteLimits
      (coefficientEvaluation (J := K) (O := O) (ell := ell) n) :=
    (coefficientEvaluation_exact n).1
  have hcolim (n : ℕ) : PreservesFiniteColimits
      (coefficientEvaluation (J := K) (O := O) (ell := ell) n) :=
    (coefficientEvaluation_exact n).2
  have hj := Functor.jointlyReflectIsomorphisms_mapDerivedCategory
    (coefficientEvaluation_jointlyReflects O ell (K := K))
  constructor
  · intro hf n
    infer_instance
  · intro hf
    apply (hj.isIso_iff f).2
    intro n
    exact (NatIso.isIso_map_iff (coefficientEvaluation_derivedIso O ell P n) f).1 (hf n)

-- Instantiate both sites and all ordinary/derived coherence structures.
/-- Derived direct image commutes canonically with every evaluation, with the specified
unit, counit and coefficient-change compatibility; bounded-below objects of levelwise
origin descend, and normalized ones stay normalized.
Source: Zheng, Construction 4.1 and Lemma 4.10, printed pp. 21, 23--24
(blueprint: lem-pur-coefficient-system-derived-comparison).

Proof plan:
1. Present strict systems as modules on the product sequence site. Kernels and cokernels
are levelwise. Apply prop-pur-kinjective-resolutions-exist on this small ringed site.
Transport algebraic operations through the geometric inverse image, which is exact;
its adjunction on modules gives the system adjunction level by level. Apply
situation-conventions and
lem-weil-pbc-kinjective-total-derived to construct the derived functors.
2. Use lem-weil-pbc-termwise-adjunction-homotopy and
lem-pc-pre-derived-adjoint-functors-general to normalize the derived adjunctions.
Their transpose on a strict complex map is the ordinary transpose followed by the
universal right-derived comparison, exactly the equation in CoefficientDerivedImage.
3. Resolve a coefficient-level complex by a flat-term K-flat complex, using
lem-pc-kflat-resolution. Its extension E_n has zero components above n and quotient
tensors below n. Exact inverse image preserves the cokernel of multiplication by
ell^(q+1), so commutes with these quotient tensors and their reduction maps.
Use lem-weil-pbc-ringed-topoi-derived-tensor-pullback for the canonical comparison.
4. The same flat-term K-flat computation gives the derived coefficient-change
comparison for every quotient, by lem-pur-derived-change-of-rings and
lem-weil-pbc-ringed-pullback-preserves-kflat. No quotient map is assumed flat.
5. Apply the LE_n/e_n adjunction of
lem-pur-coefficient-evaluation-derived-left-adjoint on both sides, the derived
system adjunction, and the comparison of step 3. The resulting natural chain of
Hom bijections identifies e_n Ru_* with Ru_* e_n by Yoneda. Inverse image commutes
with evaluation already on strict complexes.
6. The n-component of the extension comparison is the identity. The normalized
transposes therefore give the evaluated counit equation. Compose it with the
system unit and use the triangle identity; uniqueness of transpose gives the unit
equation. Thus these comparisons are adjunction mates, not unspecified isomorphisms.
7. Tensor extension is left adjoint to exact scalar restriction. Apply
lem-pc-derived-adjoint-functors and normalize as in step 2. Composition of ringed-topos
direct images gives the restricted-direct-image comparison
(lem-weil-pbc-ringed-topoi-derived-pushforward-composition). Its mate equation fixes it.
8. The extension comparison commutes with the sigma maps of the evaluation dependency:
on K-flat representatives their components below n are the same quotient tensor maps,
and above n have zero source. Its explicit sigma-mate formula gives the transition
squares. Naturality gives compatibility for every derived system morphism, including
identity quotients and compositions, with no independent choice of levelwise lifts.
9. For a uniformly bounded-below input choose a bounded-below injective resolution
(lem-sc-bounded-below-injective-resolution), which is K-injective and computes the
same total derived functor. Left exactness and
lem-weil-pbc-derived-functor-negative-vanishing give a uniform lower bound.
10. Full faithfulness on bounded-below level categories makes the level units
invertible by Yoneda. Triangle identities and naturality make the counit invertible
on the essential image. Step 6 identifies each evaluated system counit with it.
Evaluations jointly detect derived isomorphisms because cohomology is levelwise.
11. Apply naturality of the system counit to each adjoint transition. The tensor
comparison identifies this square with epsilon_n u^*(t_N) = t_M C(epsilon_m).
If M is normalized, all arrows but u^*(t_N) are invertible by step 10. Full
faithfulness on bounded-below derived objects implies full faithfulness on module
sheaves, using the fully faithful degree-zero single functors
(lem-weil-pbc-derived-single-fully-faithful). Hence exact inverse image reflects zero
module sheaves. It commutes with cohomology, so it reflects acyclicity of arbitrary
complexes, and therefore reflects isomorphisms even for the possibly unbounded
coefficient-change objects. Apply this to t_N to conclude normalization.
12. For the pro-etale/etale morphism use the recorded
Scheme.proEtaleSiteComparison and ProEtale.siteComparison_boundedBelow for finite
quotient coefficients. Its inverse image satisfies exactly the required full
faithfulness hypothesis. No constructibility of the individual sheaves is needed.
-/
theorem coefficientSystemDerivedComparison
    [PreservesFiniteLimits L]
    (hregular : ∀ x : O, ell * x = 0 → x = 0)
    [IsAdicComplete (Ideal.span ({ell} : Set O)) O] :
    ∃ (S : CoefficientSystemOrdinaryImage (J := J) (K := K) O ell L V adj)
      (PY : CoefficientEvaluationDerivedPackage (J := J) (O := O) (ell := ell))
      (PX : CoefficientEvaluationDerivedPackage (J := K) (O := O) (ell := ell)),
      Nonempty (CoefficientSystemDerivedImage O ell L V adj S PY PX) := by
  obtain ⟨S⟩ := coefficientSystemOrdinaryImage_exists O ell L V adj
  obtain ⟨PY⟩ := coefficientEvaluationDerivedLeftAdjoint (J := J) hregular
  obtain ⟨PX⟩ := coefficientEvaluationDerivedLeftAdjoint (J := K) hregular
  obtain ⟨T⟩ := coefficientSystemUnboundedComparison O ell L V adj S PY PX
  let image := T.evaluation
  let scalar := T.scalar
  have hlim : PreservesFiniteLimits S.inverse := S.systemExact.1
  have hcolim : PreservesFiniteColimits S.inverse := S.systemExact.2
  have hlevelLim (n : ℕ) : PreservesFiniteLimits (S.lift n).modules :=
    (S.inverseExact n).1
  have hlevelColim (n : ℕ) : PreservesFiniteColimits (S.lift n).modules :=
    (S.inverseExact n).2
  refine ⟨S, PY, PX, ⟨{
    construction := T
    detectsIso := coefficientEvaluation_detectsIso O ell PX
    boundedBelow := ?_
    origin := ?_ }⟩⟩
  · rintro M ⟨a, ha⟩
    exact ⟨a, exactDerivedAdjunction_isGE S.inverse image.system.inverse
      image.system.inverseFactors image.system.adjunction M a⟩
  · intro hfull M hM horigin
    have hc (n : ℕ) :
        IsIso ((image.level n).adjunction.counit.app ((PX.evaluation n).obj M)) := by
      obtain ⟨H, hH, ⟨e⟩⟩ := horigin n
      exact exactDerivedAdjunction_counit_isIso_of_origin (S.lift n).modules
        (image.level n).inverse (image.level n).inverseFactors
        (image.level n).adjunction
        (hfull n) _ H hH e
    constructor
    · apply (coefficientEvaluation_detectsIso O ell PX _).2
      intro n
      rw [← image.counit n M]
      infer_instance
    · intro hnorm m n h
      have hreflect : (image.level n).inverse.ReflectsIsomorphisms :=
        exactDerived_reflectsIso_of_boundedBelow_faithful (S.lift n).modules
          (image.level n).inverse (image.level n).inverseFactors
          (fun A B hA hB ↦ (hfull n A B hA hB).1)
      have hnorm' := hnorm h
      exact isIso_scalar_transpose_of_mate (PY.scalar h).derivedAdj
        (PX.scalar h).derivedAdj (image.level m).adjunction (image.level n).adjunction
        (scalar.derivedTensor h) (scalar.restrictedDirect h) (scalar.restrictedDirect_mate h)
        ((image.directEvaluation m).app M) ((image.directEvaluation n).app M)
        ((PY.transition h).app (image.system.direct.obj M)) ((PX.transition h).app M)
        (scalar.directTransition h M)

end SheafOfModules
