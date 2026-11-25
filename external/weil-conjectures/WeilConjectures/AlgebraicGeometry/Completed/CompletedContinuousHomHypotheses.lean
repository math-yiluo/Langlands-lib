/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Rational.RationalModuleRealizationFunctor
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousConstructibleModule
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarCoefficientEquivalence
import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformCompleteTriangulated
import all WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.Integral.IntegralConstructibleHomSums
import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectCharacterization

/-!
# Completed-to-continuous coefficient transport and shifted Hom sums

Source: Bhatt--Scholze, Lemma 6.8.2(1), Proposition 6.8.11(3), and Lemma 6.8.12
(blueprint: lem-per-completed-continuous-hom-hypotheses).

The transport is derived restriction along the inverse of the recorded normalized
coefficient isomorphism. The continuous scalar action uses actual constant functions.
The comparison field specifies its Hom identifications on arrows and checks the square
on every direct-sum generator. Coproduct objects are supplied by arbitrary colimit cofans.
Membership after transport uses the full recorded completion predicate, including the
compatible etale-origin witnesses, in the coordinates given by the coefficient isomorphism.

## Main definitions

* `continuousIntegralSections`: constant integral coefficients as compatible sections.
* `completedContinuousTransport`: derived restriction along the inverse coefficient map.
* `CompletedContinuousHomHypotheses`: all the coefficient and Hom-continuity conclusions.

## Main statements

* `completedContinuousHomHypotheses`: the specified transport has these properties.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Constant functions give the scalar action on continuous integral coefficients.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: lem-per-completed-continuous-hom-hypotheses). -/
def continuousIntegralSections (X : Scheme.{u}) :
    PbcIntegralRing l E →+* RingCat.sectionsSubring
      ((integralCoefficientSheaf l X E).obj ⋙ forget₂ CommRingCat RingCat) := by
  letI := coefficientExtensionNormedField l E
  exact
    { toFun := fun a ↦ ⟨fun _ ↦ ContinuousMap.const _ a, fun _ ↦ rfl⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }

/-- The ordinary module category is linear over constant integral coefficients.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: lem-per-completed-continuous-hom-hypotheses). -/
instance continuousIntegralLinear (X : Scheme.{u}) :
    Linear (PbcIntegralRing l E)
      (pbcModules X (integralCoefficientSheaf l X E)) :=
  letI : Linear (RingCat.sectionsSubring
      ((integralCoefficientSheaf l X E).obj ⋙ forget₂ CommRingCat RingCat))
      (pbcModules X (integralCoefficientSheaf l X E)) :=
    SheafOfModules.homLinear (integralCoefficientSheaf l X E).obj
      (X.adicLisseForget.obj (integralCoefficientSheaf l X E)).property
  { homModule := fun M N ↦ Module.compHom (M ⟶ N) (continuousIntegralSections l E X)
    smul_comp := fun M N P a f g ↦
      Linear.smul_comp M N P (continuousIntegralSections l E X a) f g
    comp_smul := fun M N P f a g ↦
      Linear.comp_smul M N P f (continuousIntegralSections l E X a) g }

/-- The induced constant action on the continuous-coefficient derived category.
Source: Bhatt--Scholze, Lemma 6.8.2(1); Stacks Project, Tag 015F
(blueprint: lem-per-completed-continuous-hom-hypotheses). -/
instance continuousIntegralDerivedLinear (X : Scheme.{u}) :
    Linear (PbcIntegralRing l E)
      (DerivedCategory (pbcModules X (integralCoefficientSheaf l X E))) := inferInstance

variable (X : Scheme.{u}) [IsNoetherian X]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]

/-- The fixed transport is restriction along the inverse normalized coefficient map,
derived by the exact-functor construction; it is not an arbitrarily chosen equivalence.
Source: Bhatt--Scholze, Lemma 6.8.2(1); Stacks Project, Tag 015F
(blueprint: lem-per-completed-continuous-hom-hypotheses). -/
abbrev completedContinuousTransport (R : RationalModuleRealization l E X) :=
  pbcDerivedRestrict R.integralIso.inv

/-- The canonical commutation with integer shifts for exact derived restriction.
Source: Stacks Project, Tag 015F
(blueprint: lem-per-completed-continuous-hom-hypotheses). -/
instance completedContinuousTransportShift (R : RationalModuleRealization l E X) :
    (completedContinuousTransport l E X R).CommShift ℤ :=
  inferInstanceAs ((pbcRestrict R.integralIso.inv).mapDerivedCategory.CommShift ℤ)

open Classical in
/-- The precise transport, boundedness, and shifted Hom comparison assertions.
The two bijective maps below are the direct-sum extensions of composition with the
shifted coprojections. The formulas for `φ` and `ψ` and the generator square identify
these actual maps, including their constant-coefficient module structures. The complete
predicate in `integral` retains every compatible etale-origin witness.
Source: Bhatt--Scholze, Lemma 6.8.2(1), Proposition 6.8.11(3), and Lemma 6.8.12
(blueprint: lem-per-completed-continuous-hom-hypotheses). -/
structure CompletedContinuousHomHypotheses (R : RationalModuleRealization l E X) where
  /-- Derived restriction is an equivalence. -/
  equivalence : (completedContinuousTransport l E X R).IsEquivalence
  /-- Its arrow maps are linear for the constant integral coefficient action. -/
  linear : (completedContinuousTransport l E X R).Linear (PbcIntegralRing l E)
  /-- The exact coefficient transport preserves and reflects both cohomological bounds. -/
  bounds : ∀ (N : PbcCompletedDerived X (pbcIntegralDatum l E)) (n : ℤ),
    (DerivedCategory.IsGE ((completedContinuousTransport l E X R).obj N) n ↔
      DerivedCategory.IsGE N n) ∧
    (DerivedCategory.IsLE ((completedContinuousTransport l E X R).obj N) n ↔
      DerivedCategory.IsLE N n)
  /-- All small coproduct cocones, including the empty one, remain coproducts. -/
  coproducts : ∀ (I : Type (u + 1)) (M : I → PbcCompletedDerived X (pbcIntegralDatum l E))
    (s : Cofan M), IsColimit s →
      Nonempty (IsColimit (Cofan.mk ((completedContinuousTransport l E X R).obj s.pt)
        (fun i : I ↦ (completedContinuousTransport l E X R).map (s.inj i))))
  /-- Membership in the same completed integral category in the continuous coordinates. -/
  integral : ∀ (K : PbcIntegralCategory l E X Fact.out Fact.out),
    PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)
      ((pbcDerivedRestrict R.integralIso.hom).obj
        ((completedContinuousTransport l E X R).obj K.obj))
  /-- Every integral object is bounded, in particular bounded below. -/
  bounded : ∀ (L : PbcIntegralCategory l E X Fact.out Fact.out),
    ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.IsGE L.obj a ∧ DerivedCategory.IsLE L.obj b
  /-- Every integer shift belongs to the full witness-sensitive integral category. -/
  shifts : ∀ (L : PbcIntegralCategory l E X Fact.out Fact.out) (q : ℤ),
    PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E) (L.obj⟦q⟧)
  /-- Normalized linear Hom identifications conjugate the two coprojection maps. -/
  comparison : ∀ (K : PbcIntegralCategory l E X Fact.out Fact.out)
    (I : Type (u + 1)) [Countable I]
    (M : I → PbcCompletedDerived X (pbcIntegralDatum l E)),
    (∃ n : ℤ, ∀ i : I, DerivedCategory.IsGE (M i) n) →
    ∀ (q : ℤ) (s : Cofan M), IsColimit s →
    ∀ (t : Cofan (fun i : I ↦ (completedContinuousTransport l E X R).obj (M i))),
    IsColimit t →
    ∃ c : (completedContinuousTransport l E X R).obj s.pt ≅ t.pt,
      (∀ i : I, (completedContinuousTransport l E X R).map (s.inj i) ≫ c.hom = t.inj i) ∧
      ∃ (φ : ∀ i : I, (K.obj ⟶ (M i)⟦q⟧) ≃ₗ[PbcIntegralRing l E]
          ((completedContinuousTransport l E X R).obj K.obj ⟶
            ((completedContinuousTransport l E X R).obj (M i))⟦q⟧))
        (ψ : (K.obj ⟶ s.pt⟦q⟧) ≃ₗ[PbcIntegralRing l E]
          ((completedContinuousTransport l E X R).obj K.obj ⟶ t.pt⟦q⟧)),
        (∀ (i : I) (f : K.obj ⟶ (M i)⟦q⟧),
          φ i f = (completedContinuousTransport l E X R).map f ≫
            ((completedContinuousTransport l E X R).commShiftIso q).hom.app (M i)) ∧
        (∀ f : K.obj ⟶ s.pt⟦q⟧,
          ψ f = (completedContinuousTransport l E X R).map f ≫
            ((completedContinuousTransport l E X R).commShiftIso q).hom.app s.pt ≫
            (shiftFunctor _ q).map c.hom) ∧
        (∀ (i : I) (f : K.obj ⟶ (M i)⟦q⟧),
          ψ (f ≫ (shiftFunctor _ q).map (s.inj i)) =
            φ i f ≫ (shiftFunctor _ q).map (t.inj i)) ∧
        Function.Bijective
          (DirectSum.toModule (PbcIntegralRing l E) I (K.obj ⟶ s.pt⟦q⟧)
            (fun i : I ↦ Linear.rightComp (PbcIntegralRing l E) K.obj
              ((shiftFunctor _ q).map (s.inj i)))) ∧
        Function.Bijective
          (DirectSum.toModule (PbcIntegralRing l E) I
            ((completedContinuousTransport l E X R).obj K.obj ⟶ t.pt⟦q⟧)
            (fun i : I ↦ Linear.rightComp (PbcIntegralRing l E)
              ((completedContinuousTransport l E X R).obj K.obj)
              ((shiftFunctor _ q).map (t.inj i))))

omit [IsNoetherian X] [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))] in
private theorem completedScalar_projection (n : ℕ) :
    pbcCompletedScalar X (pbcIntegralDatum l E) ≫ pbcAdicProjection X (pbcIntegralDatum l E) n =
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk ((pbcIntegralDatum l E).ideal ^ (n + 1)))) ≫
        (pbcLevelConstantComparison X (pbcIntegralDatum l E) n).hom := by
  dsimp only [pbcCompletedScalar, pbcAdicProjection, pbcCompletedComparison]
  rw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc]
  change (adicDatumScalar X
    { toCompleteCoefficientDatum := (pbcIntegralDatum l E).toCompleteCoefficientDatum
      quotientFinite := (pbcIntegralDatum l E).quotientFinite } ≫ _) ≫ _ = _
  congr 1
  exact (adicDatumScalar_exists X
    { toCompleteCoefficientDatum := (pbcIntegralDatum l E).toCompleteCoefficientDatum
      quotientFinite := (pbcIntegralDatum l E).quotientFinite }).exists.choose_spec n

omit [IsNoetherian X] [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))] in
private theorem completedSection_projection (n : ℕ) (U : X.ProEtᵒᵖ)
    (a : PbcIntegralRing l E) :
    (pbcAdicProjection X (pbcIntegralDatum l E) n).hom.app U
        (pbcCompletedSection X (pbcIntegralDatum l E) U a) =
      (pbcFunctionScalars X (pbcIntegralDatum l E) n).app U
        (Ideal.Quotient.mk ((pbcIntegralDatum l E).ideal ^ (n + 1)) a) := by
  have hp := congrArg (fun f ↦ f.hom.app U
    ((toSheafify (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (PbcIntegralRing l E)))).app U a))
    (completedScalar_projection l E X n)
  have hn := toSheafify_naturality (ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).map (CommRingCat.ofHom
      (Ideal.Quotient.mk ((pbcIntegralDatum l E).ideal ^ (n + 1)))))
  have hn' := congrArg (fun f ↦ f.app U a) hn
  change _ = (pbcLevelConstantComparison X (pbcIntegralDatum l E) n).hom.hom.app U _ at hp
  erw [← hn'] at hp
  rw [functionScalars_eq]
  exact hp.trans ((pbcLevelConstantComparison_exists X (pbcIntegralDatum l E) n).exists.choose_spec
    U (Ideal.Quotient.mk ((pbcIntegralDatum l E).ideal ^ (n + 1)) a))

private theorem completedContinuous_constants (R : RationalModuleRealization l E X)
    (U : X.ProEtᵒᵖ) (a : PbcIntegralRing l E) :
    R.integralIso.inv.hom.app U ((continuousIntegralSections l E X a).val U) =
      pbcCompletedSection X (pbcIntegralDatum l E) U a := by
  let G := sheafToPresheaf (ProEt.topology X) CommRingCat.{u + 1} ⋙
    (CategoryTheory.evaluation X.ProEtᵒᵖ CommRingCat.{u + 1}).obj U
  have hc := isLimitOfPreserves G (limit.isLimit (pbcAdicRings X (pbcIntegralDatum l E)))
  apply Concrete.isLimit_ext _ hc
  intro n
  change (pbcAdicProjection X (pbcIntegralDatum l E) n.unop).hom.app U _ =
    (pbcAdicProjection X (pbcIntegralDatum l E) n.unop).hom.app U _
  apply (ConcreteCategory.bijective_of_isIso ((R.finiteIso n.unop).hom.hom.app U)).1
  let := coefficientExtensionNormedField l E
  let : TopologicalSpace (finiteCoefficientRing l E n.unop) := ⊥
  let : DiscreteTopology (finiteCoefficientRing l E n.unop) := ⟨rfl⟩
  apply ContinuousMap.ext
  intro x
  apply ULift.ext
  have hn := R.integral_normalization n.unop U
    ((continuousIntegralSections l E X a).val U) x
  have hf := R.finite_normalization n.unop U
    (Ideal.Quotient.mk ((pbcIntegralDatum l E).ideal ^ (n.unop + 1)) a) x
  rw [completedSection_projection l E X]
  exact hn.trans (by
    change Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n.unop + 1)) a.down = _
    exact (congrArg ULift.down
      ((integralCoefficientULift_exists l E n.unop).exists.choose_spec a)).symm.trans
        (congrArg ULift.down hf).symm)

omit [IsNoetherian X] [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)] in
private theorem completedRestriction_faithful
    {S V : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (f : S ⟶ V) :
    (pbcRestrict f).Faithful where
  map_injective h := by
    ext U x
    exact congrArg (fun g ↦ g.val.app U x) h

private theorem completedTransport_bounds (R : RationalModuleRealization l E X)
    (N : PbcCompletedDerived X (pbcIntegralDatum l E)) (n : ℤ) :
    (DerivedCategory.IsGE ((completedContinuousTransport l E X R).obj N) n ↔
      DerivedCategory.IsGE N n) ∧
    (DerivedCategory.IsLE ((completedContinuousTransport l E X R).obj N) n ↔
      DerivedCategory.IsLE N n) := by
  let F := pbcRestrict R.integralIso.inv
  have : F.Faithful := completedRestriction_faithful X R.integralIso.inv
  constructor
  · constructor
    · intro h
      apply (DerivedCategory.isGE_iff N n).mpr
      intro i hi
      exact F.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
        ((DerivedCategory.isGE_iff _ n).mp h i hi)
    · intro h
      have := h
      exact F.isGE_mapDerivedCategory_obj N n
  · constructor
    · intro h
      apply (DerivedCategory.isLE_iff N n).mpr
      intro i hi
      exact F.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
        ((DerivedCategory.isLE_iff _ n).mp h i hi)
    · intro h
      have := h
      exact F.isLE_mapDerivedCategory_obj N n

/-- The normalized completed-to-continuous transport verifies all shifted Hom hypotheses.
Source: Bhatt--Scholze, Lemma 6.8.2(1), Proposition 6.8.11(3), and Lemma 6.8.12
(blueprint: lem-per-completed-continuous-hom-hypotheses).

Proof:
1. The quotient-normalized `R.integralIso` preserves constant sections and quotient
projections. Apply `lem-pur-ring-iso-derived-transport` to this coefficient isomorphism.
Restriction along its inverse is the exact ordinary module equivalence and induces the
specified derived equivalence. Its action on roofs preserves scalar multiplication,
because the coefficient isomorphism preserves every constant integral coefficient.
2. Termwise transport leaves kernels and images unchanged, so cohomological bounds are
preserved and reflected. The exact-derived shift isomorphism is the termwise one.
Transport a coproduct universal property through the inverse equivalence: a map from
its image is equivalent to one map from each transported summand. This identifies the
transported coprojections and works for the empty family too. The resulting unique
coproduct isomorphism is `c` in the comparison field.
3. Apply `lem-weil-pbc-integral-stratified-perfect-characterization`. Its third condition
provides bounded cohomology with finitely presented models on finitely many strata,
and its last clause gives all integer shifts. Quotient normalization and locally closed
restriction compatibility identify the same models in continuous coordinates. The
characterization retains intrinsic completeness, uniform bounds and compatible
etale-origin witnesses, so it gives `integral`, `bounded`, and `shifts`. The models may
have torsion; their cohomology modules need not be flat or projective.
4. The image family has the original common lower bound. Apply
`lem-weil-pbc-integral-constructible-hom-sums`, in the equivalent coefficient
presentation, to the transported integral object and the image family with the given
integer shift. This gives bijectivity of the continuous shifted-coprojection map.
5. On each summand put φ(f) = T(f) followed by the canonical shift isomorphism. On the
target put ψ(f) = T(f) followed by that shift isomorphism and c[q]. The equivalence and
constant normalization make these linear equivalences. Naturality of the shift
isomorphism and the coprojection normalization of c give the displayed generator
square. The direct-sum universal property extends it to the whole comparison square,
so bijectivity of the continuous comparison implies bijectivity of the completed one.
For an empty family both coproducts are zero, and both Hom comparison maps are between
zero modules. The continuity argument is used only with the supplied common lower bound. -/
theorem completedContinuousHomHypotheses (R : RationalModuleRealization l E X) :
    Nonempty (CompletedContinuousHomHypotheses l E X R) := by
  classical
  let T := completedContinuousTransport l E X R
  let : T.Additive := inferInstanceAs (pbcRestrict R.integralIso.inv).mapDerivedCategory.Additive
  have hT : T.IsEquivalence := derivedRestrictIso_isEquivalence R.integralIso.symm
  let : T.IsEquivalence := hT
  have hconstant (U : X.ProEtᵒᵖ) (a : PbcIntegralRing l E) :
      R.integralIso.inv.hom.app U ((continuousIntegralSections l E X a).val U) =
        pbcCompletedSection X (pbcIntegralDatum l E) U a := by
    exact completedContinuous_constants l E X R U a
  have hordinary : (pbcRestrict R.integralIso.inv).Linear (PbcIntegralRing l E) := by
    constructor
    intro M N f a
    ext U x
    change pbcCompletedSection X (pbcIntegralDatum l E) U a • f.val.app U x =
      R.integralIso.inv.hom.app U ((continuousIntegralSections l E X a).val U) • f.val.app U x
    rw [hconstant]
  let : (pbcRestrict R.integralIso.inv).Linear (PbcIntegralRing l E) := hordinary
  have hlin : T.Linear (PbcIntegralRing l E) :=
    inferInstanceAs ((pbcRestrict R.integralIso.inv).mapDerivedCategory.Linear
      (PbcIntegralRing l E))
  let : T.Linear (PbcIntegralRing l E) := hlin
  have hl : IsUnit (l : Γ(X, ⊤)) := by
    apply X.toRingedSpace.isUnit_of_isUnit_germ
    intro x hx
    simpa only [map_natCast] using
      (Fact.out : ∀ x : X, IsUnit (l : X.presheaf.stalk x)) x
  have hcop (I : Type (u + 1)) (M : I → PbcCompletedDerived X (pbcIntegralDatum l E))
      (s : Cofan M) (hs : IsColimit s) :
      IsColimit (Cofan.mk (T.obj s.pt) (fun i ↦ T.map (s.inj i))) :=
    (isColimitMapCoconeCofanMkEquiv T M s.inj).1 (isColimitOfPreserves T hs)
  refine ⟨{
    equivalence := hT
    linear := hlin
    bounds := completedTransport_bounds l E X R
    coproducts := fun I M s hs ↦ ⟨hcop I M s hs⟩
    integral := ?_
    bounded := ?_
    shifts := ?_
    comparison := ?_ }⟩
  · intro K
    let e := pbcDerivedRestrictComp R.integralIso.hom R.integralIso.inv _
      R.integralIso.hom_inv_id ≪≫ coefficientDerivedRestrictIdentity _
    have hP := pbcIntegralUniformComplete_isTriangulated l E X Fact.out Fact.out
    let : ObjectProperty.IsClosedUnderIsomorphisms
        (PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)) := hP.1
    exact ObjectProperty.prop_of_iso _ (e.app K.obj).symm K.property
  · intro L
    have h := integralStratifiedPerfectCharacterization X l E Fact.out hl L.obj
    exact (h.2.mp (h.1.mp L.property)).1
  · intro L q
    exact (integralStratifiedPerfectClosure X l E Fact.out hl).1 L.obj L.property q
  · intro K I hI M hM q s hs t ht
    let hsT := hcop I M s hs
    let c := hsT.coconePointUniqueUpToIso ht
    have hc (i : I) : T.map (s.inj i) ≫ c.hom = t.inj i :=
      hsT.comp_coconePointUniqueUpToIso_hom ht ⟨i⟩
    let e (N : PbcCompletedDerived X (pbcIntegralDatum l E)) :
        (K.obj ⟶ N⟦q⟧) ≃ₗ[PbcIntegralRing l E] (T.obj K.obj ⟶ (T.obj N)⟦q⟧) :=
      (LinearEquiv.ofBijective (T.mapLinearMap (PbcIntegralRing l E))
        ⟨T.map_injective, T.map_surjective⟩).trans
        (Linear.homCongr (PbcIntegralRing l E) (Iso.refl _) ((T.commShiftIso q).app N))
    let ψ := (e s.pt).trans
      (Linear.homCongr (PbcIntegralRing l E) (Iso.refl _) ((shiftFunctor _ q).mapIso c))
    have he (N) (f : K.obj ⟶ N⟦q⟧) :
        e N f = T.map f ≫ (T.commShiftIso q).hom.app N := by
      simp [e, Linear.homCongr_apply]
    have hψ (f : K.obj ⟶ s.pt⟦q⟧) :
        ψ f = T.map f ≫ (T.commShiftIso q).hom.app s.pt ≫
          (shiftFunctor _ q).map c.hom := by
      simp [ψ, he, Linear.homCongr_apply, Category.assoc]
    have hsq (i : I) (f : K.obj ⟶ (M i)⟦q⟧) :
        ψ (f ≫ (shiftFunctor _ q).map (s.inj i)) =
          e (M i) f ≫ (shiftFunctor _ q).map (t.inj i) := by
      rw [hψ, he, T.map_comp]
      have hn := (T.commShiftIso q).hom.naturality (s.inj i)
      dsimp only [Functor.comp_map] at hn
      simp only [Category.assoc]
      rw [← Category.assoc (T.map ((shiftFunctor _ q).map (s.inj i)))
        ((T.commShiftIso q).hom.app s.pt) ((shiftFunctor _ q).map c.hom), hn]
      simp only [Category.assoc]
      rw [← (shiftFunctor _ q).map_comp, hc i]
    have hb := integralConstructible_hom_sums X l E Fact.out Fact.out K I M hM q s hs
    refine ⟨c, hc, (fun i ↦ e (M i)), ψ, (fun i f ↦ he (M i) f), hψ, hsq, hb, ?_⟩
    let A := PbcIntegralRing l E
    let α := DirectSum.toModule A I (K.obj ⟶ s.pt⟦q⟧)
      (fun i ↦ Linear.rightComp A K.obj ((shiftFunctor _ q).map (s.inj i)))
    let β := DirectSum.toModule A I (T.obj K.obj ⟶ t.pt⟦q⟧)
      (fun i ↦ Linear.rightComp A (T.obj K.obj) ((shiftFunctor _ q).map (t.inj i)))
    let d := DirectSum.lmap (fun i ↦ (e (M i)).toLinearMap)
    have hd : Function.Bijective d :=
      ⟨(DirectSum.lmap_injective _).mpr (fun i ↦ (e (M i)).injective),
        (DirectSum.lmap_surjective _).mpr (fun i ↦ (e (M i)).surjective)⟩
    have hcomm : ψ.toLinearMap.comp α = β.comp d := by
      apply DirectSum.linearMap_ext
      intro i
      apply LinearMap.ext
      intro f
      simp only [LinearMap.comp_apply]
      dsimp only [α, β, d, A]
      erw [DirectSum.toModule_lof, DirectSum.lmap_lof, DirectSum.toModule_lof]
      exact hsq i f
    have hbcomp : Function.Bijective (β ∘ d) := by
      have heq : β ∘ d = ψ ∘ α := congrArg DFunLike.coe hcomm.symm
      rw [heq]
      exact ψ.bijective.comp hb
    exact ⟨fun x y h ↦ by
      obtain ⟨x', rfl⟩ := hd.2 x
      obtain ⟨y', rfl⟩ := hd.2 y
      exact congrArg d (hbcomp.1 h),
      fun y ↦ by
        obtain ⟨x, hx⟩ := hbcomp.2 y
        exact ⟨d x, hx⟩⟩

end AlgebraicGeometry.Scheme
