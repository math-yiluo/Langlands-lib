/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Tate.TateTwistFiniteLocallyFree
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnitySheafSupplement
public import WeilConjectures.SmoothPurity.Supporting.Coefficient.IntrinsicCoefficientTwists
public import WeilConjectures.AlgebraicGeometry.Pur.PurInverseImageTensorHom
import all WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionDualLocalIso
import all WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheafLocallyFree
import all WeilConjectures.AlgebraicGeometry.Pur.PurInverseImageScalarComparison
import all WeilConjectures.AlgebraicGeometry.Pur.PurTwistRootLocalModels
import all WeilConjectures.AlgebraicGeometry.Pur.PurTwistIntegralLocalModels
import all WeilConjectures.SmoothPurity.Supporting.SignedLineTensorEquivalence
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Algebra.Homology.LineUnbounded.LineUnboundedDerivedTensor
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import all WeilConjectures.SmoothPurity.IntegralLineReduction.IntegralLineReductionRestriction
import WeilConjectures.FourierTransform.CompletedLineTensor.CompletedLineTensorCoherence
import WeilConjectures.SmoothPurity.Integral.IntegralObjectPullbackLine
import WeilConjectures.SmoothPurity.Common.CommonStageTensorLineCoherence
import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorIso
import all WeilConjectures.SmoothPurity.Finite.FiniteLineTensorConditions
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
import WeilConjectures.SixFunctors.Completed.CompletedTensorScalarLinearity
import all WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization
import WeilConjectures.CategoryTheory.ScalarLocalization.SemilinearScalarLocalization
import all WeilConjectures.AlgebraicGeometry.Tate.TateTwistFiniteLocallyFree

/-! # Integral and rational Tate twists: definitions and local calculations

Source: `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/
sk-def-sp-tate-twist-locally-free.md`, clause (3), integral and rational cases
(blueprint: definition-tate-twists).

The integral, rational and algebraically closed twist functors and signed-line predicates,
with the integral and rational local calculations used by `tateTwist_locallyFree`
(`WeilConjectures.AlgebraicGeometry.Tate.TateTwistLocallyFree`). The finite clauses are in
`WeilConjectures.AlgebraicGeometry.Tate.TateTwistFiniteLocallyFree`.

## Main definitions

* `tateIntegralTwist` and `tateRationalTwist` are the integral and rational twist functors.
* `TateRationalSignedLine` and `TateQbarSignedLine` express the signed-line clauses in the
  recorded integral-representative categories, with the canonical restriction functors.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u v d c h

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

-- `flatConstantModulesAbelian` (universes `max u v`) leaves a universe metavariable that stalls
-- unification with the `WEqualsLocallyBijective` instance at universe `u + 1` on the slice sites.
attribute [-instance] CategoryTheory.flatConstantModulesAbelian

namespace AlgebraicGeometry.Scheme

/-- The canonical bounded integral twist uses the recorded intrinsic coefficient line.
Source: blueprint clause (3), integral case
(blueprint: definition-tate-twists). -/
def tateIntegralTwist (D : FiniteFieldDatum.{d}) (ℓ : ℕ) [Fact ℓ.Prime]
    (hD : ℓ ≠ D.p) (E : Type u) [Field E] [Algebra (Padic ℓ) E]
    [FiniteDimensional (Padic ℓ) E] (X : Scheme.{u})
    [∀ x : X, Invertible (ℓ : X.residueField x)] (m : ℤ) :=
  tateTensorRight (constructibleIntegralTensor ℓ E X)
    (intrinsicIntegralCoefficientTwist D ℓ hD E X m)

/-- The rational twist tensors with the localization of the same integral representative.
Source: blueprint clause (3), rational case
(blueprint: definition-tate-twists). -/
def tateRationalTwist (D : FiniteFieldDatum.{d}) (ℓ : ℕ) [Fact ℓ.Prime]
    (hD : ℓ ≠ D.p) (E : Type u) [Field E] [Algebra (Padic ℓ) E]
    [FiniteDimensional (Padic ℓ) E] (X : Scheme.{u})
    [∀ x : X, Invertible (ℓ : X.residueField x)] (m : ℤ) :=
  tateTensorRight (rationalDerivedTensor ℓ E X)
    ((sfRationalConstructibleLocalization ℓ E X).obj
      (intrinsicIntegralCoefficientTwist D ℓ hD E X m))

/-- Transport invertibility along the actual residue-field homomorphism.
Source: the cover in blueprint clause (3)
(blueprint: definition-tate-twists). -/
@[instance_reducible] def tatePullbackInvertible (ℓ : ℕ) {Y X : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (ℓ : X.residueField x)] :
    ∀ y : Y, Invertible (ℓ : Y.residueField y) :=
  fun y ↦ (map_natCast (f.residueFieldMap y).hom ℓ) ▸
    Invertible.map (f.residueFieldMap y).hom (ℓ : X.residueField (f y))

/-- The rational signed lines, interpreted in the recorded rational category:
every signed degree-zero line restricts to the coefficient unit on this cover,
and the positive/negative tensor product is the coefficient unit globally.
The integral representative of the coefficient unit is the published zero twist.
Source: blueprint clause (3), rational interpretation via definition-tate-twists
(blueprint: definition-tate-twists). -/
def TateRationalSignedLine (D : FiniteFieldDatum.{d}) (ℓ : ℕ) [Fact ℓ.Prime]
    (hD : ℓ ≠ D.p) (E : Type u) [Field E] [Algebra (Padic ℓ) E]
    [FiniteDimensional (Padic ℓ) E] (X : Scheme.{u})
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    {I : Type (u + 1)} (U : I → X.ProEt) : Prop :=
  (∀ (m : ℤ) (i : I),
    letI := tatePullbackInvertible ℓ (U i).hom
    Nonempty ((rationalDerivedPullback ℓ E (U i).hom).obj
      ((sfRationalConstructibleLocalization ℓ E X).obj
        (intrinsicIntegralCoefficientTwist D ℓ hD E X m)) ≅
      (sfRationalConstructibleLocalization ℓ E (U i).left).obj
        (intrinsicIntegralCoefficientTwist D ℓ hD E (U i).left 0))) ∧
  ∀ n : ℕ, Nonempty ((rationalDerivedTensor ℓ E X).obj
    ((sfRationalConstructibleLocalization ℓ E X).obj
      (intrinsicIntegralCoefficientTwist D ℓ hD E X n),
      (sfRationalConstructibleLocalization ℓ E X).obj
        (intrinsicIntegralCoefficientTwist D ℓ hD E X (-(n : ℤ)))) ≅
    (sfRationalConstructibleLocalization ℓ E X).obj
      (intrinsicIntegralCoefficientTwist D ℓ hD E X 0))

/-- The same signed local-line and tensor-inverse clauses in the recorded literal
common-stage category. Both restriction and tensor are the canonical published functors;
the coefficient unit is the least-stage zero twist, not an arbitrarily chosen object.
Source: blueprint clause (3), Qbar interpretation via definition-tate-twists
(blueprint: definition-tate-twists). -/
def TateQbarSignedLine (D : FiniteFieldDatum.{d}) (ℓ : ℕ) [Fact ℓ.Prime]
    (hD : ℓ ≠ D.p) (X : Scheme.{u})
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    (Ω : Type v) [Field Ω] [Algebra (Padic ℓ) Ω] [IsAlgClosure (Padic ℓ) Ω]
    {I : Type (u + 1)} (U : I → X.ProEt) : Prop :=
  (∀ (m : ℤ) (i : I),
    letI := tatePullbackInvertible ℓ (U i).hom
    Nonempty ((commonStageDerivedPullback ℓ Ω (U i).hom).obj
      (intrinsicQbarCoefficientTwist D ℓ hD X Ω m) ≅
      intrinsicQbarCoefficientTwist D ℓ hD (U i).left Ω 0)) ∧
  ∀ n : ℕ, Nonempty ((commonStageDerivedTensor ℓ Ω X).obj
    (intrinsicQbarCoefficientTwist D ℓ hD X Ω n,
      intrinsicQbarCoefficientTwist D ℓ hD X Ω (-(n : ℤ))) ≅
    intrinsicQbarCoefficientTwist D ℓ hD X Ω 0)

set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] HasDerivedCategory.standard

attribute [local instance 20000] tateAbSheafify tateAbBijective tateWeakSheafify tateSiteSmall
  tateDerived

private theorem tateIntegralTrivial (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type u) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (V : X.ProEt) (h : (purTwistZlModule X ℓ).over V ≅
      (SheafOfModules.unit (purTwistRing X (purTwistZlCompletion X ℓ))).over V) :
    Nonempty ((purTwistIntegralModule X ℓ E).over V ≅
      (SheafOfModules.unit (purTwistRing X
        (completedIntegralCommRingSheafUnrestricted ℓ E X))).over V) := by
  have := integralExtensionReverse_isIso X ℓ E
  exact ⟨(SheafOfModules.overFunctor _ V).mapIso
      (asIso (integralExtensionReverse X ℓ E)).symm ≪≫
    SheafOfModules.extendedBasisIso (purTwistCompletedScalarMap X ℓ E)
      (purTwistZlModule X ℓ) h⟩

private theorem tateIntegralTensorComparison (X : Scheme.{u}) (ℓ : ℕ)
    [Fact ℓ.Prime] (E : Type u) [Field E] [Algebra (Padic ℓ) E]
    [FiniteDimensional (Padic ℓ) E] :
    Nonempty (
      integralCompletedTensor ℓ E X ≅ IntegralOnSlice.completedTensor ℓ E X none
    ) :=
  ⟨((integralCompletedTensorDescent ℓ E X).universal _
    (IntegralOnSlice.completedTensor_global_comparison ℓ E X).some).exists.choose⟩

private theorem tateIntegralCompletedComparison
    (D : FiniteFieldDatum.{d}) (ℓ : ℕ) [Fact ℓ.Prime] (hD : ℓ ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) [∀ x : X, Invertible (ℓ : X.residueField x)] (m : ℤ) :
    Nonempty (
      tateIntegralTwist D ℓ hD E X m ⋙ (sfIntegralConstructible ℓ E X).ι ≅
        (sfIntegralConstructible ℓ E X).ι ⋙
          IntegralLineReduction.completed ℓ E X (purTwistIntegralModule X ℓ E) m
    ) := by
  refine ⟨?_⟩
  let F := tateIntegralTwist D ℓ hD E X m
  let T := tateTensorRight (integralCompletedTensor ℓ E X)
    (integralCoefficientTwist D ℓ hD E X m)
  have a : F ⋙ (sfIntegralConstructible ℓ E X).ι ≅
      (sfIntegralConstructible ℓ E X).ι ⋙ T := Iso.refl _
  have b : T ≅ IntegralLineReduction.completed ℓ E X
      (purTwistIntegralModule X ℓ E) m := by
    rw [IntegralLineReduction.completed, integralLineCompleted,
      IntegralLineReduction.power_eq_coefficient]
    let P := (𝟭 (DerivedCategory (integralTowerModules ℓ E X))).prod'
      ((Functor.const _).obj (integralCoefficientTwist D ℓ hD E X m))
    let Q := Prod.sectL (IntegralOnSlice.D ℓ E X none)
      (coefficientTwistLine X (R := completedIntegralCommRingSheafUnrestricted ℓ E X)
        (purTwistIntegralModule X ℓ E) m) ⋙
        (𝟭 _).prod (integralLineSingle ℓ E X ⋙ DerivedCategory.Q)
    have q : P ≅ Q := NatIso.ofComponents (fun K ↦ Iso.refl _) (by
      intro K K' f
      change Prod.mkHom f (𝟙 _) ≫ 𝟙 _ = 𝟙 _ ≫
        Prod.mkHom f ((integralLineSingle ℓ E X ⋙ DerivedCategory.Q).map (𝟙 _))
      exact (Category.comp_id _).trans
        ((congrArg (Prod.mkHom f) ((integralLineSingle ℓ E X ⋙
          DerivedCategory.Q).map_id _).symm).trans (Category.id_comp _).symm))
    exact Functor.isoWhiskerLeft P (tateIntegralTensorComparison X ℓ E).some ≪≫
      Functor.isoWhiskerRight q (IntegralOnSlice.completedTensor ℓ E X none)
  exact a ≪≫ Functor.isoWhiskerLeft (sfIntegralConstructible ℓ E X).ι b

private theorem tateIntegralFiniteReductions (X : Scheme.{u}) (ℓ : ℕ)
    [Fact ℓ.Prime] (E : Type u) [Field E] [Algebra (Padic ℓ) E]
    [FiniteDimensional (Padic ℓ) E]
    [∀ x : X, Invertible (ℓ : X.residueField x)] :
    IntegralLineReduction.FiniteReductions ℓ E X (purTwistIntegralModule X ℓ E) := by
  intro n
  let A := Padic.coefficientExtensionRing ℓ E (n + 1)
  let := Padic.finite_coefficientExtensionRing ℓ E (n + 1) (Nat.succ_pos n)
  let L := (IntegralLineReduction.line ℓ E X (purTwistIntegralModule X ℓ E) n)
  let e : L ≅ purTwistFiniteOne X ℓ E n :=
    eqToIso ((scalarReductionExistence.{u, u} ℓ E X n).choose_spec.choose
      (purTwistIntegralModule X ℓ E)) ≪≫
    SheafOfModules.ScalarHomOrdinary.extensionIso.{u + 1, u, u + 1}
      (completedIntegralCommRingProjectionUnrestricted ℓ E X n)
        (purTwistIntegralModule X ℓ E) ≪≫
    (((pur_twist_sheaf_locally_free.{u, 0} X ℓ E).2.2.1.2.2.2 n).1).some
  have : L.IsFiniteLocallyFreeOfRank 1 :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso e.symm
  obtain ⟨I, U, f, hc, he⟩ := line_constant_models X A L
  refine ⟨I, U, f, hc, fun i ↦ ?_⟩
  refine ⟨ModuleCat.of (ULift.{u + 1} A) (ULift.{u + 1} A), inferInstance, ?_⟩
  exact he i

private theorem tateIntegralInverse (D : FiniteFieldDatum.{d}) (ℓ : ℕ)
    [Fact ℓ.Prime] (hD : ℓ ≠ D.p) (E : Type u) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) [hX : ∀ x : X, Invertible (ℓ : X.residueField x)]
    (hf : IntegralLineReduction.FiniteReductions ℓ E X (purTwistIntegralModule X ℓ E))
    (m : ℤ) : TateInverseTwists (tateIntegralTwist D ℓ hD E X m)
      (tateIntegralTwist D ℓ hD E X (-m)) := by
  obtain ⟨b, d, e, hb, hd, he, hc, hs, hr⟩ :=
    IntegralLineReduction.integral_line_reduction_restriction ℓ E X hX
      (purTwistIntegralModule X ℓ E) hf
  obtain ⟨h, c, hc, hr⟩ := hr
  obtain ⟨v, w, hv, hw, ho, F, a, b, hF⟩ := hr m
  let inc := (sfIntegralConstructible ℓ E X).ι
  have a' : F.functor ≅ tateIntegralTwist D ℓ hD E X m :=
    Functor.fullyFaithfulCancelRight inc
      (a ≪≫ (tateIntegralCompletedComparison D ℓ hD E X m).some.symm)
  have b' : F.inverse ≅ tateIntegralTwist D ℓ hD E X (-m) :=
    Functor.fullyFaithfulCancelRight inc
      (b ≪≫ (tateIntegralCompletedComparison D ℓ hD E X (-m)).some.symm)
  exact ⟨(F.changeFunctor a').changeInverse b', rfl, rfl⟩

private theorem tateIntegralAdditive (D : FiniteFieldDatum.{d}) (ℓ : ℕ)
    [Fact ℓ.Prime] (hD : ℓ ≠ D.p) (E : Type u) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) [∀ x : X, Invertible (ℓ : X.residueField x)] (m : ℤ) :
    (tateIntegralTwist D ℓ hD E X m).Additive := by
  obtain ⟨e, he, hi⟩ := tateIntegralInverse D ℓ hD E X
    (tateIntegralFiniteReductions X ℓ E) m
  have : (tateIntegralTwist D ℓ hD E X m).IsEquivalence := he ▸ inferInstance
  exact Functor.additive_of_preserves_binary_products _

private theorem tateIntegralLinear (D : FiniteFieldDatum.{d}) (ℓ : ℕ)
    [Fact ℓ.Prime] (hD : ℓ ≠ D.p) (E : Type u) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) [∀ x : X, Invertible (ℓ : X.residueField x)] (m : ℤ) :
    (tateIntegralTwist D ℓ hD E X m).Linear
      (Padic.coefficientExtensionIntegers ℓ E) where
  map_smul := by
    intro K K' f c
    exact completedTensor_map_smul_left ℓ E X K K'
      (intrinsicIntegralCoefficientTwist D ℓ hD E X m)
      (intrinsicIntegralCoefficientTwist D ℓ hD E X m) f (𝟙 _) c

private noncomputable def tateLocalizedTensorIso
    {R : Type*} [CommRing R] {C : Type*} [Category C] [Preadditive C] [Linear R C]
    (p : R) (F : C ⥤ C) [F.Additive] [F.Linear R]
    (T : ScalarLocalization R C p ⥤ ScalarLocalization R C p)
    (ho : ∀ K, T.obj K = (ScalarLocalization.map R C p F).obj K)
    (hm : ∀ K K', ∃ q : (K ⟶ K') →ₗ[Localization.Away p]
      (T.obj K ⟶ T.obj K'), ∀ f, T.map f = q f)
    (ht : ∀ (K K' : ScalarLocalization R C p) (c : Localization.Away p)
      (f : K.obj ⟶ K'.obj), HEq (T.map (c ⊗ₜ[R] f)) (c ⊗ₜ[R] F.map f)) :
    T ≅ ScalarLocalization.map R C p F := by
  let G := ScalarLocalization.map R C p F
  let : G.Additive := ScalarLocalization.mapAdditive R C p F
  refine NatIso.ofComponents (fun K ↦ eqToIso (ho K)) ?_
  intro K K' f
  obtain ⟨q, hq⟩ := hm K K'
  change T.map f ≫ eqToHom (ho K') = eqToHom (ho K) ≫ G.map f
  rw [comp_eqToHom_iff, Category.assoc]
  apply (conj_eqToHom_iff_heq _ _ (ho K) (ho K')).mpr
  induction f using TensorProduct.inductionOn with
  | tmul c f =>
    exact (ht K K' c f).trans
      (heq_of_eq (LinearMap.baseChange_tmul (F.mapLinearMap R) c f).symm)
  | add f g hf hg =>
    rw [hq, map_add, ← hq, ← hq, Functor.map_add]
    exact (conj_eqToHom_iff_heq _ _ (ho K) (ho K')).mp (by
      rw [(conj_eqToHom_iff_heq _ _ (ho K) (ho K')).mpr hf,
        (conj_eqToHom_iff_heq _ _ (ho K) (ho K')).mpr hg]
      simp only [Preadditive.comp_add, Preadditive.add_comp])

private theorem tateRationalComparison
    (D : FiniteFieldDatum.{d}) (ℓ : ℕ) [Fact ℓ.Prime] (hD : ℓ ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) [∀ x : X, Invertible (ℓ : X.residueField x)] (m : ℤ) :
    Nonempty (
      letI := tateIntegralAdditive D ℓ hD E X m
      letI := tateIntegralLinear D ℓ hD E X m
      tateRationalTwist D ℓ hD E X m ≅
        ScalarLocalization.map (Padic.coefficientExtensionIntegers ℓ E)
          (sfIntegralConstructibleCategory ℓ E X)
          (Padic.coefficientExtensionUniformizer ℓ E) (tateIntegralTwist D ℓ hD E X m)
    ) := by
  refine ⟨?_⟩
  letI := tateIntegralAdditive D ℓ hD E X m
  letI := tateIntegralLinear D ℓ hD E X m
  let L := (sfRationalConstructibleLocalization ℓ E X).obj
    (intrinsicIntegralCoefficientTwist D ℓ hD E X m)
  apply tateLocalizedTensorIso (Padic.coefficientExtensionUniformizer ℓ E)
    (tateIntegralTwist D ℓ hD E X m) (tateRationalTwist D ℓ hD E X m)
    (fun K ↦ (rationalDerivedTensor_existsUnique ℓ E X).exists.choose_spec.1 (K, L))
  · intro K K'
    obtain ⟨b, hb, ht⟩ :=
      (rationalDerivedTensor_existsUnique ℓ E X).exists.choose_spec.2 K K' L L
    exact ⟨b.flip (𝟙 L), fun g ↦ hb g (𝟙 L)⟩
  · intro K K' c f
    obtain ⟨b, hb, ht⟩ :=
      (rationalDerivedTensor_existsUnique ℓ E X).exists.choose_spec.2 K K' L L
    have h := ht f (𝟙 L.obj) c 1
    have hh := heq_of_eq (hb (c ⊗ₜ[Padic.coefficientExtensionIntegers ℓ E] f) (𝟙 L))
    exact hh.trans h |>.trans (heq_of_eq (congrArg
      (fun a ↦ a ⊗ₜ[Padic.coefficientExtensionIntegers ℓ E]
        (constructibleIntegralTensor ℓ E X).map (Prod.mkHom f (𝟙 L.obj))) (mul_one c)))

private noncomputable def tateLocalizedPair
    {R : Type*} [CommRing R] {C : Type*} [Category C] [Preadditive C] [Linear R C]
    (p : R) (U V : C ⥤ C) [U.Additive] [V.Additive] [U.Linear R] [V.Linear R]
    (c : U ⋙ V ≅ 𝟭 C) :
    ScalarLocalization.map R C p U ⋙ ScalarLocalization.map R C p V ≅ 𝟭 _ := by
  let hp : IsUnit (algebraMap R (Localization.Away p) ((RingHom.id R) p)) :=
    IsLocalization.Away.algebraMap_isUnit p
  let q := ScalarLocalization.extensionNatIso p p (RingHom.id R) hp
    (ScalarLocalization.isSemilinear_of_linear (U ⋙ V))
    (ScalarLocalization.isSemilinear_of_linear (𝟭 C)) c
  have hh (W : C ⥤ C) [W.Additive] [W.Linear R] :=
    (ScalarLocalization.extension_id_and_linear (C := C) p).2 W
  rw [hh (U ⋙ V), hh (𝟭 C)] at q
  exact eqToIso (ScalarLocalization.map_comp R C p U V) ≪≫ q ≪≫
    eqToIso (ScalarLocalization.map_identity R C p)

private theorem tateRationalInverse (D : FiniteFieldDatum.{d}) (ℓ : ℕ)
    [Fact ℓ.Prime] (hD : ℓ ≠ D.p) (E : Type u) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) [∀ x : X, Invertible (ℓ : X.residueField x)] (m : ℤ) :
    TateInverseTwists (tateRationalTwist D ℓ hD E X m)
      (tateRationalTwist D ℓ hD E X (-m)) := by
  let R := Padic.coefficientExtensionIntegers ℓ E
  let C := sfIntegralConstructibleCategory ℓ E X
  let p : R := Padic.coefficientExtensionUniformizer ℓ E
  let F := tateIntegralTwist D ℓ hD E X m
  let G := tateIntegralTwist D ℓ hD E X (-m)
  let : F.Additive := tateIntegralAdditive D ℓ hD E X m
  let : G.Additive := tateIntegralAdditive D ℓ hD E X (-m)
  let : F.Linear R := tateIntegralLinear D ℓ hD E X m
  let : G.Linear R := tateIntegralLinear D ℓ hD E X (-m)
  obtain ⟨e, he, hi⟩ := tateIntegralInverse D ℓ hD E X
    (tateIntegralFiniteReductions X ℓ E) m
  have a : F ⋙ G ≅ 𝟭 C := by simpa only [he, hi] using e.unitIso.symm
  have b : G ⋙ F ≅ 𝟭 C := by simpa only [he, hi] using e.counitIso
  let q := CategoryTheory.Equivalence.mk
    (ScalarLocalization.map R C p F) (ScalarLocalization.map R C p G)
    (tateLocalizedPair p F G a).symm (tateLocalizedPair p G F b)
  exact ⟨(q.changeFunctor (tateRationalComparison D ℓ hD E X m).some.symm).changeInverse
    (tateRationalComparison D ℓ hD E X (-m)).some.symm, rfl, rfl⟩

private theorem tateLineGood (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type u) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (L : integralTowerModules ℓ E X) [L.IsFiniteLocallyFreeOfRank 1] :
    IntegralOnSlice.Good ℓ E X none ((integralLineSingle ℓ E X).obj L) := by
  obtain ⟨_, _, hL, _, hf, _, _⟩ :=
    SheafOfModules.LineUnbounded.line_unbounded_derived_tensor.{u, u} X
      (completedIntegralCommRingSheafUnrestricted ℓ E X) L
  exact ⟨hL, hf⟩

private theorem tateIntegralLineProduct
    (D : FiniteFieldDatum.{d}) (ℓ : ℕ) [Fact ℓ.Prime] (hD : ℓ ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) [hX : ∀ x : X, Invertible (ℓ : X.residueField x)] (m : ℤ) :
    Nonempty (
      (constructibleIntegralTensor ℓ E X).obj
        (intrinsicIntegralCoefficientTwist D ℓ hD E X m,
          intrinsicIntegralCoefficientTwist D ℓ hD E X (-m)) ≅
        intrinsicIntegralCoefficientTwist D ℓ hD E X 0
    ) := by
  refine ⟨?_⟩
  let L := purTwistIntegralModule X ℓ E
  let P := coefficientTwistLine X
    (R := completedIntegralCommRingSheafUnrestricted ℓ E X) L m
  let T := coefficientTwistLine X
    (R := completedIntegralCommRingSheafUnrestricted ℓ E X) L (-m)
  let K := intrinsicIntegralCoefficientTwist D ℓ hD E X m
  have : P.IsFiniteLocallyFreeOfRank 1 :=
    (signedLineTensor_equivalence X
      (completedIntegralCommRingSheafUnrestricted ℓ E X) L m).1
  have : T.IsFiniteLocallyFreeOfRank 1 :=
    (signedLineTensor_equivalence X
      (completedIntegralCommRingSheafUnrestricted ℓ E X) L (-m)).1
  let PG : (IntegralOnSlice.Good ℓ E X none).FullSubcategory :=
    ⟨(integralLineSingle ℓ E X).obj P, tateLineGood X ℓ E P⟩
  let hT := (tateLineGood X ℓ E T).1
  have ep :=
    ((DerivedCategory.singleFunctorIsoCompQ (integralTowerModules ℓ E X) 0).app P).symm
  have hc : IntegralOnSlice.IsComplete ℓ E X none K.obj :=
    CompletedLineTensor.intrinsic_complete ℓ E X K
  have hi := IntegralLineReduction.comparison_isIso ℓ E X hX L (-m) K.obj hc
  have a := (tateIntegralCompletedComparison D ℓ hD E X (-m)).some.app K
  have b := (asIso ((IntegralLineReduction.comparison ℓ E X L (-m)).app K.obj)).symm
  have c : (IntegralLineReduction.ordinary ℓ E X L (-m)).obj K.obj ≅
      DerivedCategory.Q.obj (integralLineComplex ℓ E X PG.obj T) := by
    change (integralLineOrdinary ℓ E X).obj
      (K.obj, IntegralLineReduction.power ℓ E X L (-m)) ≅ _
    rw [IntegralLineReduction.power_eq_coefficient]
    exact (integralLineRepresentativeIso ℓ E X PG T hT K.obj ep).symm
  let R := completedIntegralCommRingSheafUnrestricted ℓ E X
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} _
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  have collapse := CochainComplex.map₂HomologicalComplexFlipObjSingleIso
    (MonoidalCategory.curriedTensor (integralTowerModules ℓ E X)) T
  have single := HomologicalComplex.singleMapHomologicalComplex
    (SheafOfModules.siteSheafTensorRight
      (A := completedIntegralCommRingSheafUnrestricted ℓ E X) T) (.up ℤ) 0
  have evaluation : (SheafOfModules.siteSheafTensorRight
      (A := completedIntegralCommRingSheafUnrestricted ℓ E X) T).obj P ≅
      SheafOfModules.unit (purTwistRing X
        (completedIntegralCommRingSheafUnrestricted ℓ E X)) := by
    let U := SheafOfModules.unit (purTwistRing X
      (completedIntegralCommRingSheafUnrestricted ℓ E X))
    have ep : (SheafOfModules.siteSheafTensorRight (A := R) P).obj U ≅ P :=
      (SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1} R P).app U ≪≫
        MonoidalCategory.leftUnitor P
    exact ((SheafOfModules.siteSheafTensorRight (A := R) T).mapIso ep.symm) ≪≫
      (signedLineTensor_equivalence X R L m).2.some.app U
  have e : ((constructibleIntegralTensor ℓ E X).obj (K,
      intrinsicIntegralCoefficientTwist D ℓ hD E X (-m))).obj ≅
      (intrinsicIntegralCoefficientTwist D ℓ hD E X 0).obj :=
    a ≪≫ b ≪≫ c ≪≫ DerivedCategory.Q.mapIso
      (collapse.app PG.obj ≪≫
        ((NatIso.mapHomologicalComplex
          (SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1} R T).symm
          (.up ℤ)).app PG.obj) ≪≫ single.app P ≪≫
        (integralLineSingle ℓ E X).mapIso evaluation) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (integralTowerModules ℓ E X) 0).app
        (SheafOfModules.unit (purTwistRing X R))).symm
  exact (sfIntegralConstructible ℓ E X).ι.preimageIso e

private theorem tateRationalLineProduct
    (D : FiniteFieldDatum.{d}) (ℓ : ℕ) [Fact ℓ.Prime] (hD : ℓ ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) [∀ x : X, Invertible (ℓ : X.residueField x)] (m : ℤ) :
    Nonempty (
      (rationalDerivedTensor ℓ E X).obj
        ((sfRationalConstructibleLocalization ℓ E X).obj
          (intrinsicIntegralCoefficientTwist D ℓ hD E X m),
          (sfRationalConstructibleLocalization ℓ E X).obj
            (intrinsicIntegralCoefficientTwist D ℓ hD E X (-m))) ≅
        (sfRationalConstructibleLocalization ℓ E X).obj
          (intrinsicIntegralCoefficientTwist D ℓ hD E X 0)
    ) :=
  ⟨eqToIso ((rationalDerivedTensor_existsUnique ℓ E X).exists.choose_spec.1 _) ≪≫
    (sfRationalConstructibleLocalization ℓ E X).mapIso
      (tateIntegralLineProduct D ℓ hD E X m).some⟩

end AlgebraicGeometry.Scheme
