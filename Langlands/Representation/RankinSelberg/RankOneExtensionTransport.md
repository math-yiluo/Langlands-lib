# Specialized rank-one lower-to-upper transport

Author: Worker 469.

This module supplies the concrete two-block specialization of the published
`Langlands.glOppositeProductReversal`. Its principal definition is
`Langlands.RankinSelberg.rankOneExtensionLowerInduced`; the comparison theorem is
`Langlands.RankinSelberg.rankOneExtensionLowerToUpperEquiv`.
This is a derived transport unit for the restricted JPSS Lemma 5.5 proof.
It does not prove the integral comparison or polynomial divisibility.

## Data and conventions

For an actual canonical p-adic field `F`, `t : Nat`, and a complex module `W`
in an independent universe, `rankOneExtensionUpperShape t` is exactly
`Shahidi.twoBlocks 1 (t+1)`, of total rank `1+(t+1)`.
`rankOneExtensionLowerShape t` is its reversal, with ordered sizes `(t+1,1)`
at the same total rank. The lower carrier family is the original Shahidi
pair carrier, precomposed with `Fin.rev`: its first member is `W` and its
second is `ULift Complex`. Only the rank-one carrier is lifted.

The inputs are an arbitrary representation `chi` of `GL_1(F)` on
`ULift.{uW} Complex` and an arbitrary representation `sigma` of `GL_(t+1)(F)`
on `W`. `rankOneExtensionLowerFamily` is `Shahidi.pairFamily chi sigma`
precomposed with reversal. The lower induced representation is the actual
`canonicalTopologicalData.normalizedOppositeParabolicInduced` of the block
tensor of this family. It uses the published opposite normalizing character;
there is no substituted abstract action or carrier. Explicit dependent
additive-group and module instances, and an explicit carrier-family argument
at `blockTensor`, fix the dictionaries used by this construction.

The theorem assumes smoothness of both factors for the canonical topology
and supplies a representation equivalence to exactly
`F.canonicalNormalizedProductInduced (rankOneExtensionUpperShape t)
  (Shahidi.pairFamily chi sigma)`.
The upper order is `(chi,sigma)`. No equivalence between the two upper
orders is asserted. The theorem applies in particular when `chi` is the
rank-one quasicharacter representation conjugated through
`ULift.moduleEquiv.symm` in `RankOneExtensionLDivisibilityStatement`.
The field and module universes remain independent. No irreducibility,
admissibility, or Whittaker hypothesis enters this transport unit.

## Implemented proof

`GeneralLinear.BlockShape.reverse_twice` proves equality of a shape with its
double reversal. After destructing the shape, function extensionality and
`Fin.rev_rev` identify its size function; the remaining fields are proofs.

The specialized theorem first proves smoothness of each lower block factor
by the two cases of `Fin 2`. It then invokes the published general reversal
with the actual lower shape, carrier family, and representation family.
The resulting upper endpoint has all three dependent families reindexed
twice. The final identification is performed together: the local proposition
`Q e` describes the entire target induction reindexed by a permutation `e`
of `Fin 2`. The supplied equivalence proves `Q (revPerm.trans revPerm)`.
Extensionality and `Fin.rev_rev` identify that permutation with `Equiv.refl`;
rewriting yields the exact requested upper induction. This avoids treating
dependent carrier equalities as definitional equalities.

The exported theorem asserts existence of an equivalence. Although the
reused general theorem includes evaluation formulas, this specialized
existence theorem does not export a prescribed evaluation formula for the
transported witness, nor does it assert any zeta-value or factor identity.
Those remain available as further transports to establish as needed.

## Provenance and remaining scope

This is an internal derived specialization of the current Library's actual
block-reversal and normalized-induction constructions, rather than a new
analytic result from the literature. The convention and application are
those of H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions* (1983): Section 3.1, printed 404–405 / PDF 39–40,
for lower induction, and Lemma 5.5, printed 423–427 / PDF 58–62, for its
rank-one application. The registered source is `jpss-1983-rankin-selberg`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
No corresponding erratum was located in the available project notes.

The parent proof still requires the compact-section construction, scalar
Fourier smoothing, comparison of actual zeta integrals, and certified factor
existence. The present module uses neither L-factor multiplicativity nor
the later Section 9.3 tail result. It imports the parent target unchanged.
