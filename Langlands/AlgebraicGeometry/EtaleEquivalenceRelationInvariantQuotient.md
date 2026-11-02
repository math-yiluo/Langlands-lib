# The conditional invariant-ring quotient

This internal construction combines the conditional flatness and tensor-pushout
results with the geometric quotient certificate. For an étale equivalence
relation `E` in an arbitrary universe `u`, put
`B = Γ(E.U, ⊤)` and `C = Γ(E.R, ⊤)`, with source algebra structure
`E.s.appTop.hom.toAlgebra` and target `t = E.t.appTop.hom`.

Assume the ring relation `RingEtaleEquivalenceRelation t`, the unchanged
predicate `E.ComodulesAcyclic`, and zero detection: for every coaction
on a `B`-module in `Type u`, a subsingleton invariant module forces the
underlying module to be subsingleton.

`invariantRingQuotient` constructs an actual
`E.FaithfullyFlatRingQuotient`. Its base ring is the equalizer
`A = invariantRing t`, and its inclusion is the canonical map `A → B`.
The conditional flatness theorem proves this map faithfully flat.
`isPushout_invariantRing` supplies the pushout of two copies of this
inclusion, with last maps `E.t.appTop` and `E.s.appTop` in that order.

When `E.U` and `E.R` are affine,
`hasAffineQuotient_of_acyclic_of_detects_zero` applies the certificate's
geometric API. The witnesses are `Spec A` and the morphism from `E.U`
induced by `A → B`. Faithful flatness supplies flatness and surjectivity;
the ring pushout supplies the kernel-pair pullback, and fpqc descent
from the étale relation projection supplies local finite presentation.
Thus the conclusion is the unchanged published `E.HasAffineQuotient`.

The derivation translates no new literature theorem. It reuses the
actual coordinate rings, published coaction and acyclicity definitions,
and the internal helpers named above. It does not use Noetherianity or
closedness directly: deriving the ring-relation premise from affineness
and closedness and deriving zero detection from the Noetherian
hypotheses remain separate inputs to the full Serre criterion.
