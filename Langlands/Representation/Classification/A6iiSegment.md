# Segment quotients under twists, and products of surjections

Author: Worker 4988. Module `Langlands.Representation.Classification.A6iiSegment`,
namespace `Langlands.Classification.A6ii`. Internal helper for the proof of Tadić's
Corollary A.6(ii) (`IrreducibleLanglandsHeadProductProof`).

- `twistSC F T s A`: the supercuspidal representation `ν^s A = A ⊗ |det|^s`
  (published `SupercuspidalRep.twist` by `determinantPowerCharacter`). Its object is
  literally `T.segmentFactor A.obj s`, so `i(ν^0 A', ν^1 A', …)` built from `twistSC` is
  definitionally the published `segmentInduced A'`.
- `segment_twisted_quotient`: if `π` is an irreducible quotient of
  `i(A, νA, …, ν^(m-1)A)`, then `ν^s π` is an irreducible quotient of the same induction
  built from `ν^s A`. Proof: published `twistedProductCharacterTwist` and
  `isIrreducibleQuotient_twist_iff`. The argument is the one of the private lemma
  `segmentQuotient_realPowerTwist` in `SegmentSpecialEssentialSquareIntegrabilityProof`.
- `productMap_surjective`: the normalized product functor maps blockwise surjections to
  a surjection (published `normalizedProductInducedMap_surjective`).
- `commonExponentIso`: for blocks `σ_i` and a real `s`,
  `Ind_B(σ) ≅ ν^s Ind_B(ν^{-s} σ_i)`. This copies the private `groupedCommonExponentIso`
  of `SquareIntegrableEqualExponentGroupingProof`: `twistedProductCharacterTwist` and
  `realPowerTwist_neg_cancel`.
- `induced_obj_eq`: the bundled induction `CuspidalJacquetMultiplicity.induced` of a
  block tensor is the object of the normalized product functor (`rfl`).
