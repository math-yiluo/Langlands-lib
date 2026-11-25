/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Tate.TateTwistIntegralLines
public import WeilConjectures.AlgebraicGeometry.Tate.TateTwistFiniteLocallyFree
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnitySheafSupplement
public import WeilConjectures.SmoothPurity.Supporting.Coefficient.IntrinsicCoefficientTwists
public import WeilConjectures.AlgebraicGeometry.Pur.PurInverseImageTensorHom
import all WeilConjectures.AlgebraicGeometry.Tate.TateTwistFiniteLocallyFree
import all WeilConjectures.AlgebraicGeometry.Tate.TateTwistIntegralLines
import WeilConjectures.SmoothPurity.Supporting.SignedLineTensorEquivalence
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Algebra.Homology.LineUnbounded.LineUnboundedDerivedTensor
import WeilConjectures.SmoothPurity.Integral.IntegralObjectPullbackLine
import WeilConjectures.SmoothPurity.Common.CommonStageTensorLineCoherence
import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorIso
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
import WeilConjectures.SixFunctors.Completed.CompletedTensorScalarLinearity
import WeilConjectures.CategoryTheory.ScalarLocalization.SemilinearScalarLocalization

/-! # Tate twists are well defined and locally free of rank one

Source: `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/
sk-def-sp-tate-twist-locally-free.md`, clauses (1)--(3)
(blueprint: definition-tate-twists).

The helpers specialize the recorded constant sheaf, root module, scalar extension,
signed line and tensor functors. All positive root levels are indexed by `n + 1`.
The theorem includes one common cover, normalized generators, canonical Kummer
independence, signed invertible lines and equivalences with the negative twists.

The finite clauses and the definitions they use are in
`WeilConjectures.AlgebraicGeometry.Tate.TateTwistFiniteLocallyFree`
(`tateTwist_finite_locallyFree`), the integral and rational twist functors, signed-line
predicates and local calculations in
`WeilConjectures.AlgebraicGeometry.Tate.TateTwistIntegralLines`; both are imported publicly.

## Main statements

* `tateTwist_locallyFree` states all three source clauses for all four coefficients.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u v d c h

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] HasDerivedCategory.standard

attribute [local instance 20000] tateAbSheafify tateAbBijective tateWeakSheafify tateSiteSmall
  tateDerived

private theorem tateCommonTensorOnStage
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    (Ω : Type v) [Field Ω] [Algebra (Padic ℓ) Ω] [IsAlgClosure (Padic ℓ) Ω]
    (B : AlgebraicallyClosedCoefficients.Index ℓ Ω)
    (M N : sfRationalConstructibleCategory ℓ
      (AlgebraicallyClosedCoefficients.Coefficient.{u} ℓ Ω B) X) :
    Nonempty (
      (commonStageDerivedTensor ℓ Ω X).obj
        ((GeneralAlgebraicallyClosedCoefficients.stageSystem ℓ Ω X).ι B |>.obj M,
          (GeneralAlgebraicallyClosedCoefficients.stageSystem ℓ Ω X).ι B |>.obj N) ≅
        (GeneralAlgebraicallyClosedCoefficients.stageSystem ℓ Ω X).ι B |>.obj
          ((rationalDerivedTensor ℓ
            (AlgebraicallyClosedCoefficients.Coefficient.{u} ℓ Ω B) X).obj (M, N))
    ) := by
  refine ⟨?_⟩
  let S := GeneralAlgebraicallyClosedCoefficients.stageSystem ℓ Ω X
  let E := AlgebraicallyClosedCoefficients.Coefficient.{u} ℓ Ω B
  let P := (S.ι B).obj M
  let Q := (S.ι B).obj N
  have objIso : (commonStageDerivedTensor ℓ Ω X).obj (P, Q) ≅
      commonStageTensorObject ℓ Ω X P Q :=
    eqToIso ((commonStageDerivedTensor_existsUnique ℓ Ω X).exists.choose_spec.1 P Q)
  have hc : Padic.finiteCoefficientCompositum ℓ Ω B B = B := by
    apply Subtype.ext
    simp only [Padic.finiteCoefficientCompositum, sup_idem]
  have unit : S.T (le_refl B) ≅ 𝟭 _ :=
    eqToIso ((GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique
      ℓ Ω X).exists.choose_spec.1 B B (le_refl B)) ≪≫
      GeneralAlgebraicallyClosedCoefficients.unitor ℓ Ω X B
  let h : (commonStageTensorObject ℓ Ω X P Q).stage ≤ B := hc.le
  exact objIso ≪≫ S.isoToStage (commonStageTensorObject ℓ Ω X P Q) h ≪≫
    (S.ι B).mapIso (commonStageTensorComparison ℓ Ω X P Q B h ≪≫
      (rationalDerivedTensor ℓ E X).mapIso (Iso.prod (unit.app M) (unit.app N)))

private theorem tateQbarSigned_of_rational
    (D : FiniteFieldDatum.{d}) (ℓ : ℕ) [Fact ℓ.Prime] (hD : ℓ ≠ D.p)
    (X : Scheme.{u}) [∀ x : X, Invertible (ℓ : X.residueField x)]
    (Ω : Type v) [Field Ω] [Algebra (Padic ℓ) Ω] [IsAlgClosure (Padic ℓ) Ω]
    {I : Type (u + 1)} (U : I → X.ProEt)
    (h : TateRationalSignedLine D ℓ hD
      (AlgebraicallyClosedCoefficients.Coefficient.{u} ℓ Ω
        (Padic.finiteCoefficientBase ℓ Ω)) X U) :
    TateQbarSignedLine D ℓ hD X Ω U := by
  let B := Padic.finiteCoefficientBase ℓ Ω
  let E := AlgebraicallyClosedCoefficients.Coefficient.{u} ℓ Ω B
  constructor
  · intro m i
    let := tatePullbackInvertible ℓ (U i).hom
    have a := (h.1 m i).some
    refine ⟨eqToIso ((commonStageDerivedPullback_existsUnique ℓ Ω
      (U i).hom).exists.choose_spec.1 _) ≪≫ ?_⟩
    exact (GeneralAlgebraicallyClosedCoefficients.stageSystem ℓ Ω (U i).left).ι B |>.mapIso a
  · intro n
    exact ⟨(tateCommonTensorOnStage ℓ X Ω B _ _).some ≪≫
      ((GeneralAlgebraicallyClosedCoefficients.stageSystem ℓ Ω X).ι B).mapIso
        (h.2 n).some⟩

private theorem tateIntegralLocal
    (D : FiniteFieldDatum.{d}) (ℓ : ℕ) [Fact ℓ.Prime] (hD : ℓ ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) [∀ x : X, Invertible (ℓ : X.residueField x)]
    (W : X.ProEt) [∀ y : W.left, Invertible (ℓ : W.left.residueField y)]
    (e : (purTwistIntegralModule X ℓ E).over W ≅
      (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted ℓ E X)).over W)
    (m : ℤ) : Nonempty ((constructibleIntegralPullback ℓ E W.hom).obj
      (intrinsicIntegralCoefficientTwist D ℓ hD E X m) ≅
      intrinsicIntegralCoefficientTwist D ℓ hD E W.left 0) := by
  let R := completedIntegralCommRingSheafUnrestricted ℓ E X
  let L := purTwistIntegralModule X ℓ E
  let P := coefficientTwistLine X (R := R) L m
  have hP : P.IsFiniteLocallyFreeOfRank 1 :=
    (signedLineTensor_equivalence X R L m).1
  have eP := lineSignedOverUnit X R L W e m
  exact ⟨(sfIntegralConstructible ℓ E W.left).ι.preimageIso
    (integralObjectPullbackLine ℓ E X W P hP eP).some⟩

private theorem tateRationalSigned
    (D : FiniteFieldDatum.{d}) (ℓ : ℕ) [Fact ℓ.Prime] (hD : ℓ ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) [∀ x : X, Invertible (ℓ : X.residueField x)]
    {I : Type (u + 1)} (U : I → X.ProEt)
    (he : ∀ i, Nonempty ((purTwistIntegralModule X ℓ E).over (U i) ≅
      (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted ℓ E X)).over
        (U i))) : TateRationalSignedLine D ℓ hD E X U := by
  constructor
  · intro m i
    let := tatePullbackInvertible ℓ (U i).hom
    refine ⟨eqToIso ((rationalDerivedPullback_existsUnique ℓ E
      (U i).hom).exists.choose_spec.2.1 _) ≪≫ ?_⟩
    exact (sfRationalConstructibleLocalization ℓ E (U i).left).mapIso
      (tateIntegralLocal D ℓ hD E X (U i) (he i).some m).some
  · intro n
    exact tateRationalLineProduct D ℓ hD E X n

private noncomputable def tateTensorRightIso
    {C : Type c} [Category.{h} C] (T : C × C ⥤ C) {L M : C} (e : L ≅ M) :
    tateTensorRight T L ≅ tateTensorRight T M := by
  refine NatIso.ofComponents (fun K ↦ T.mapIso (Iso.prod (Iso.refl K) e)) ?_
  intro K K' f
  change T.map (Prod.mkHom f (𝟙 L)) ≫ T.map (Prod.mkHom (𝟙 K') e.hom) =
    T.map (Prod.mkHom (𝟙 K) e.hom) ≫ T.map (Prod.mkHom f (𝟙 M))
  rw [← T.map_comp, ← T.map_comp]
  congr 1
  ext <;> simp

private theorem tateTensorInverse
    {C : Type c} [Category.{h} C] (T : C × C ⥤ C) (U L M : C)
    (a : tateTensorRight T L ⋙ tateTensorRight T M ≅
      tateTensorRight T (T.obj (L, M)))
    (b : tateTensorRight T M ⋙ tateTensorRight T L ≅
      tateTensorRight T (T.obj (M, L)))
    (u : tateTensorRight T U ≅ 𝟭 C)
    (e : T.obj (L, M) ≅ U) (e' : T.obj (M, L) ≅ U) :
    TateInverseTwists (tateTensorRight T L) (tateTensorRight T M) := by
  have aa := a ≪≫ tateTensorRightIso T e ≪≫ u
  have bb := b ≪≫ tateTensorRightIso T e' ≪≫ u
  exact ⟨CategoryTheory.Equivalence.mk (tateTensorRight T L) (tateTensorRight T M)
    aa.symm bb, rfl, rfl⟩

private theorem tateQbarInverse
    (D : FiniteFieldDatum.{d}) (ℓ : ℕ) [Fact ℓ.Prime] (hD : ℓ ≠ D.p)
    (X : Scheme.{u}) [∀ x : X, Invertible (ℓ : X.residueField x)]
    (Ω : Type v) [Field Ω] [Algebra (Padic ℓ) Ω] [IsAlgClosure (Padic ℓ) Ω]
    (n : ℕ)
    (e : (commonStageDerivedTensor ℓ Ω X).obj
      (intrinsicQbarCoefficientTwist D ℓ hD X Ω n,
        intrinsicQbarCoefficientTwist D ℓ hD X Ω (-(n : ℤ))) ≅
      intrinsicQbarCoefficientTwist D ℓ hD X Ω 0) :
    TateInverseTwists (intrinsicQbarComplexTwistFunctor D ℓ hD X Ω n)
      (intrinsicQbarComplexTwistFunctor D ℓ hD X Ω (-(n : ℤ))) := by
  obtain ⟨ha, hu⟩ := commonStageTensorLineCoherence ℓ X Ω
  exact tateTensorInverse (commonStageDerivedTensor ℓ Ω X)
    (intrinsicQbarCoefficientTwist D ℓ hD X Ω 0)
    (intrinsicQbarCoefficientTwist D ℓ hD X Ω n)
    (intrinsicQbarCoefficientTwist D ℓ hD X Ω (-(n : ℤ)))
    (ha _ _).some (ha _ _).some hu.some e
    (pullbackTensorCommonBraiding ℓ Ω X _ _ ≪≫ e)

/-- One common covering trivializes the compatible root generators and all coefficient
lines; Kummer transitions induce the canonical A-linear isomorphisms; every signed twist
is a line, with positive and negative twist functors inverse on the specified categories.

Source: `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/
sk-def-sp-tate-twist-locally-free.md`, all three clauses
(blueprint: definition-tate-twists).

Proof:
1. The compatible root-tower local model supplies one pro-etale cover, compatible
   sections at every positive root level, and unit-to-root basis isomorphisms.
   Their naturality gives the displayed transition and slice formulas.
2. Annihilation supplies the quotient map from Z/ell^(r+1) to A. Form the
   scalar-extension adjunct of the specified root transition. Its value on a
   pure tensor is the prescribed Kummer formula. On the root cover it carries
   the chosen generator to the chosen generator, so it is locally and globally
   an isomorphism. Signed-line tensor equivalences give all finite signed powers
   and their two inverse functors on unbounded complexes.
3. Extend the same integral root basis to every finite coefficient field E.
   The completed integral local model identifies this extension with the actual
   integral Tate line. Signed powers and internal duals remain trivial on the
   same cover. The finite scalar reductions are the finite Tate lines already
   constructed, so coherent reduction and reconstruction give the two inverse
   intrinsic integral twist functors.
4. Identify the actual integral right-tensor functor with its completed line
   model. Prove its additivity and scalar linearity. Localize the two inverse
   natural isomorphisms; induction on pure Hom scalar tensors identifies these
   localized functors with the intrinsic rational twist functors.
5. For each signed integral line, the completed pullback calculation for a
   supplied slice basis identifies its actual derived inverse image with the
   regular line. Rational pullback then gives the required rational local
   trivializations. Transport these from the least finite coefficient stage
   to obtain the algebraically closed local trivializations.
6. Compute opposite integral Tate object products using a flat single-complex
   representative, completeness, the ordinary-to-completed comparison and the
   signed evaluation isomorphism. Localize this product to rational
   coefficients and identify the common-stage product on objects from one stage.
7. Natural fixed-right tensor associativity and the specified regular unit in
   the common-stage category combine with the opposite object products (and
   braiding for the reversed product) to give both inverse composites of the
   actual algebraically closed twist functors. Assemble all clauses using the
   original common root cover.
-/
theorem tateTwist_locallyFree
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    (E : Type u) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (Ω : Type v) [Field Ω] [Algebra (Padic ℓ) Ω] [IsAlgClosure (Padic ℓ) Ω]
    (ι : E →ₐ[Padic ℓ] Ω) :
    ∃ (I : Type (u + 1)) (U : I → X.ProEt)
      (f : ∀ i : I, U i ⟶ ProEt.mk (𝟙 X))
      (ζ : ∀ (n : ℕ) (i : I), (purTwistRootsModule X ℓ n).val.obj (op (U i)))
      (e : ∀ (n : ℕ) (i : I),
        (SheafOfModules.unit (purTwistRing X (purTwistFiniteRing X ℓ n))).over (U i) ≅
          (purTwistRootsModule X ℓ n).over (U i)),
      Presieve.ofArrows U f ∈ (ProEt.precoverage X).coverings _ ∧
      (∀ (n : ℕ) (i : I),
        (proEtaleRootsOfUnityTransition X (ℓ ^ (n + 1)) (ℓ ^ (n + 2))
          (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
          (pow_dvd_pow ℓ (Nat.le_succ (n + 1)))).hom.app (op (U i))
            (ζ (n + 1) i) = ζ n i) ∧
      (∀ (n : ℕ) (i : I) (V : (Over (U i))ᵒᵖ)
        (a : ((purTwistRing X (purTwistFiniteRing X ℓ n)).over (U i)).obj.obj V),
        (e n i).hom.val.app V a =
          a • (purTwistRootsModule X ℓ n).val.map V.unop.hom.op (ζ n i)) ∧
      (∀ (A : Type (u + 1)) [CommRing A] [Finite A] (r : ℕ),
        (∀ a : A, (ℓ ^ (r + 1)) • a = 0) →
        ∃ a : ZMod (ℓ ^ (r + 1)) →+* A,
          (∀ (n : ℕ) (hrn : r ≤ n),
            ∃ k : tateFiniteLine X ℓ A n
                (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))
                  (ZMod (ℓ ^ (r + 1))))) ⟶ tateFiniteLine X ℓ A r a,
              IsIso k ∧
              ∀ (V : X.ProEt) (b : (tateFiniteCoefficient X A).obj.obj (op V))
                (x : (proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1))).obj.obj (op V)),
                k.val.app (op V)
                  (tateFiniteTensor X ℓ A n
                    (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))
                      (ZMod (ℓ ^ (r + 1))))) V b x) =
                  tateFiniteTensor X ℓ A r a V b
                    ((proEtaleRootsOfUnityTransition X (ℓ ^ (r + 1)) (ℓ ^ (n + 1))
                      (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
                      (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))).hom.app (op V) x)) ∧
          (∃ hL : (tateFiniteLine X ℓ A r a).IsFiniteLocallyFreeOfRank 1,
            TateSignedLine X (tateFiniteCoefficient X A) (tateFiniteLine X ℓ A r a) U ∧
            ∀ n : ℕ, TateInverseTwists
              (tateComplexTwist X (tateFiniteCoefficient X A) (tateFiniteLine X ℓ A r a) hL n)
              (tateComplexTwist X (tateFiniteCoefficient X A) (tateFiniteLine X ℓ A r a) hL
                (-(n : ℤ))))) ∧
      TateSignedLine X (completedIntegralCommRingSheafUnrestricted ℓ E X)
        (purTwistIntegralModule X ℓ E) U ∧
      ∀ (D : FiniteFieldDatum.{d}) (hD : ℓ ≠ D.p),
        TateRationalSignedLine D ℓ hD E X U ∧
        TateQbarSignedLine D ℓ hD X Ω U ∧
        ∀ n : ℕ, TateInverseTwists (tateIntegralTwist D ℓ hD E X n)
          (tateIntegralTwist D ℓ hD E X (-(n : ℤ))) ∧
        TateInverseTwists (tateRationalTwist D ℓ hD E X n)
          (tateRationalTwist D ℓ hD E X (-(n : ℤ))) ∧
        TateInverseTwists (intrinsicQbarComplexTwistFunctor D ℓ hD X Ω n)
          (intrinsicQbarComplexTwistFunctor D ℓ hD X Ω (-(n : ℤ))) := by
  classical
  have _ := ι
  obtain ⟨I, U, f, ζ, e, hc, hζ, he, hr⟩ := tateRootCover X ℓ
  let hi (F : Type u) [Field F] [Algebra (Padic ℓ) F]
      [FiniteDimensional (Padic ℓ) F] (i : I) :
      Nonempty ((purTwistIntegralModule X ℓ F).over (U i) ≅
        (SheafOfModules.unit
          (completedIntegralCoefficientSheafUnrestricted ℓ F X)).over (U i)) :=
    tateIntegralTrivial X ℓ F (U i) (hr i).some
  refine ⟨I, U, f, ζ, e, hc, hζ, he,
    tateFiniteClause X ℓ U f hc ζ e hζ he,
    tateSignedLine_of_trivial X (completedIntegralCommRingSheafUnrestricted ℓ E X)
      (purTwistIntegralModule X ℓ E) U (hi E), ?_⟩
  intro D hD
  have hE := tateRationalSigned D ℓ hD E X U (hi E)
  let E₀ := AlgebraicallyClosedCoefficients.Coefficient.{u} ℓ Ω
    (Padic.finiteCoefficientBase ℓ Ω)
  have hΩ := tateQbarSigned_of_rational D ℓ hD X Ω U
    (tateRationalSigned D ℓ hD E₀ X U (hi E₀))
  refine ⟨hE, hΩ, fun n ↦ ⟨?_, ?_, ?_⟩⟩
  · exact tateIntegralInverse D ℓ hD E X (tateIntegralFiniteReductions X ℓ E) n
  · exact tateRationalInverse D ℓ hD E X n
  · exact tateQbarInverse D ℓ hD X Ω n (hΩ.2 n).some

end AlgebraicGeometry.Scheme
