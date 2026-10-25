# Conditional assembly of two-block gamma multiplicativity

This internal module combines the implemented two-stage rank descent and
representation adapter into the exact published
`TwoBlockGammaMultiplicativityStatement` at the stable common carrier universe
`max uF u`. Its conclusion retains arbitrary dependent block carriers, the
supplied self-dual Haar measure, every positive rank order, and full
Whittaker-type representations, including reducible representations.

`twoBlockGammaAuxiliary` lifts the trivial scalar character representation
to `ULift.{max uF u} ℂ`. Conjugation through `ULift.moduleEquiv.symm` gives
its actual action, and that same linear equivalence intertwines the scalar
and lifted actions. Full Whittaker type transports through this equivalence
from the explicit `RankOneWhittakerTypeStatement` premise. The scalar action
and equivalence use the pattern shared by Worker 465 in his two-block L
draft; the gamma argument needs no high-ramification condition.

`twoBlockGammaMultiplicativity_of_inputs_commonUniverse` introduces the
published target's complete telescope and supplies this auxiliary object
to `TwoBlockGammaDescent.certified`. That theorem uses ordered canonical
normalized upper induction, certified unit uniqueness and cancellation,
two downward rank inductions, and the actual induced-representation
equivalence for the original dependent family.

Seven substantive inputs remain explicit premises: preservation of full
Whittaker type by normalized induction, gamma-construction input, equal-rank
pair exchange, the dominant, adjacent and rank-one analytic bases, and
scalar rank-one full type. This module proves none of these inputs. It does
not prove the requested closed theorem, nor does it yet transport the
conclusion to three independent universes. General carrier transport is
outside this module.

Provenance is internal assembly of the published predicates and transport
APIs, together with the implemented descent abstracted from JPSS (1983),
section 7, printed pages 438–442, registered source
`jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The actual lower-to-upper source reversal remains an obligation of the
separate upper-convention analytic base proofs. No analytic existence or
semantic acceptance is inferred from this conditional assembly.
