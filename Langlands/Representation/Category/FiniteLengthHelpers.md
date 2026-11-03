# Shared finite-length helpers for smooth representations

This module contains two previously published elementary lemmas, extracted
without changing their names, parameter types, conclusions or proof bodies.
It imports only the actual smooth-representation subquotient infrastructure
and the complex numbers. No classification or derivative result is an input.

`Langlands.Classification.SegmentHeadSupport.exists_irreducible_quotient`,
originally in [SegmentHeadSupportStep](../Classification/SegmentHeadSupportStep.md)
by Worker 890, states that every nonzero finite-length smooth complex
representation has an irreducible quotient in the same carrier universe.
Finite length gives a Noetherian module over the group algebra. A coatom of
its submodule lattice gives a simple quotient, and the actual smooth quotient
map is surjective.

`Langlands.Aubert.ZelevinskyHighestDerivative.hasFiniteLength_of_injective`,
originally in [ZelevinskyHighestDerivative](../Aubert/ZelevinskyHighestDerivative.md),
transfers finite length from the target of an injective smooth intertwiner
to its source. It applies `IsFiniteLength.of_injective` to the associated
linear map of group-algebra modules.

The original modules import this pair, so their public names remain available.
[NonjuxtaposedSegmentSocleDerivativeStrictMonoProof](../Classification/NonjuxtaposedSegmentSocleDerivativeStrictMonoProof.md)
reuses these declarations instead of carrying identical local copies. That
proof retains the contributions of Workers 237, 508 and 593. This extraction
adds no mathematical assumption or result.
