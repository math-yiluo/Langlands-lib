import Langlands.Representation.Derivative.PartialDerivativeJacquetComparisonProof
import Langlands.Representation.CuspidalSupport.InducedJacquetEvaluation

/-! # Derivative quotients supplied by actual maps into induction -/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- The partial derivative retains surjectivity of every actual intertwiner. -/
theorem partialDerivative_map_surjective (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (k m : ℕ) :
    letI := T.topology
    ∀ {A B : SmoothRep.{0,uF,uV} ℂ (GeneralLinear k F.Carrier × GeneralLinear m F.Carrier)}
      (f : A ⟶ B), Function.Surjective (SmoothRep.hom f) →
        Function.Surjective (SmoothRep.hom ((partialDerivative T ψ k m).map f)) := by
  let := T.topology
  intro A B f hf y
  obtain ⟨v, rfl⟩ := partialDerivativeMk_surjective T ψ k m B y
  obtain ⟨w, rfl⟩ := hf v
  exact ⟨partialDerivativeMk T ψ k m A w, partialDerivative_map_mk T ψ k m f w⟩

/-- Restriction from the actual positive two-block Levi to the product of its
actual general linear factors. The carrier and every linear map are unchanged. -/
def positiveTwoBlockLeviPullback (T : F.TopologicalData) (k m : ℕ)
    (hk : 0 < k) (hm : 0 < m) :
    letI := T.topology
    SmoothRep.{0,uF,uV} ℂ ((Shahidi.twoBlocks k m hk hm).Levi F.Carrier) ⥤
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear k F.Carrier × GeneralLinear m F.Carrier) := by
  letI := T.topology
  exact Mirabolic.continuousPullbackFunctor
    (Shahidi.twoBlockLeviContinuousEquiv hk hm F.Carrier).symm.toMonoidHom
    (Shahidi.twoBlockLeviContinuousEquiv hk hm F.Carrier).symm.continuous

/-- A nonzero actual map into induction of an irreducible two-block Levi
representation supplies a surjection from the ordinary derivative onto the
partial derivative of that Levi representation. -/
def derivativeQuotientOfInducedMap (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    letI := T.topology
    ∀ (X : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + m) F.Carrier))
      (σ : SmoothRep.{0,uF,uV} ℂ ((Shahidi.twoBlocks k m hk hm).Levi F.Carrier))
      (_hσ : Representation.IsIrreducible σ.representation)
      (j : X.representation.IntertwiningMap
        (T.normalizedParabolicInduced (Shahidi.twoBlocks k m hk hm) σ.representation)),
      j ≠ 0 →
        {q : ((generalLinearDerivative T ψ (k + m) m (Nat.le_add_left m k) ⋙
                generalLinearRankCast T (Nat.add_sub_cancel k m)).obj X) ⟶
            (partialDerivative T ψ k m).obj
              ((positiveTwoBlockLeviPullback T k m hk hm).obj σ) //
          Function.Surjective (SmoothRep.hom q)} := by
  letI := T.topology
  intro X σ hσ j hj
  letI := hσ
  let f := CuspidalSupport.jacquetEvaluation T (Shahidi.twoBlocks k m hk hm) j
  have hf : f ≠ 0 :=
    CuspidalSupport.jacquetEvaluation_ne_zero T (Shahidi.twoBlocks k m hk hm) j hj
  have hfs : Function.Surjective f :=
    (Representation.IsIrreducible.surjective_or_eq_zero f).resolve_right hf
  let P := positiveTwoBlockLeviPullback.{uF,uV} T k m hk hm
  let fp : (positiveTwoBlockNormalizedJacquet T k m hk hm).obj X ⟶ P.obj σ :=
    P.map (SmoothRep.ofHom f)
  have hfp : Function.Surjective (SmoothRep.hom fp) := hfs
  let e := (Classical.choice (partialDerivativeJacquetComparison F T ψ k m hk hm)).app X
  refine ⟨e.hom ≫ (partialDerivative T ψ k m).map fp, ?_⟩
  exact (partialDerivative_map_surjective T ψ k m fp hfp).comp
    (SmoothRep.equivOfIso e).surjective

end Langlands.Derivative
