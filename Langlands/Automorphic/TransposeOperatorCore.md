# Inverse-transpose pullback on the actual stable operator core

This internal helper for Task 7294 transports the existing concrete operator
algebra and its maximal stable automorphic core. It follows the algebraic
transport pattern of `CMOperatorConjugation` and
`StableAutomorphicCMTransport`, replacing their CM field automorphism by the
proved inverse-transpose pullback on actual adelic functions. The construction
works over an arbitrary-universe number field and every natural matrix size.

Conjugating ambient complex-linear endomorphisms by the pullback is an
involutive complex algebra automorphism. It sends finite translations to
inverse-transpose translations, compact translations to those indexed by
`compactTranspose`, and enveloping operators to those indexed by
`envelopingIota`. Induction over the generated concrete algebra proves that
this conjugation restricts to that same algebra. No freely presented algebra
or replacement representation is used.

An element belongs to the maximal operator core exactly when every concrete
operator applied to it is an actual automorphic form. Whole-algebra covariance
and preservation of actual forms prove preservation of this core. Involutivity
gives reflection and restriction supplies `StableAutomorphicFunctions.transpose`.
The remaining identities record whole-algebra, finite, compact and enveloping
covariance, compatibility with the actual automorphic inclusion, and the
inverse-transpose evaluation formula.

This helper does not establish preservation of cuspidality or the identification
with a contragredient; those remain open in Task 7294.
