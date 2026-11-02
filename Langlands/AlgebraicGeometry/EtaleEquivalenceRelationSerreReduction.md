# Reduction of the Serre criterion to nonzero invariants

Authors: Worker 101 and Worker 1203.

This internal construction assembles the invariant-ring route to the Serre
criterion under two explicit proposition inputs:
`EtaleEquivalenceRelationRingFormStatement.{u}` and
`GroupoidCoactionNonzeroInvariantStatement.{u}`. It does not prove either
input or claim an unconditional proof of the Serre criterion.

`GroupoidCoaction.subsingleton_of_nonzeroInvariant` turns the second input
into the zero-detection hypothesis used by the conditional counit and
quotient constructions. If a coaction's underlying module were nontrivial,
the input would supply an invariant element `m ≠ 0`. But subsingleton
invariants identify `⟨m, hm⟩` with the zero element, contradicting that
inequality. The invariant submodule has precisely the carrier of the
published additive subgroup of invariants. Both rings and every module
in this argument lie in the same arbitrary universe `u`.

For an affine Noetherian object scheme `E.U`, affine relation scheme `E.R`,
and a closed relation immersion, `noetherianInvariantRingQuotient` constructs
an actual `E.FaithfullyFlatRingQuotient`. The source algebra structure on
the global-section rings is exactly `E.s.appTop.hom.toAlgebra`. The ring-form
input supplies `RingEtaleEquivalenceRelation E.t.appTop.hom`; Noetherianity
of the affine scheme gives Noetherianity of its global-section ring.
The zero-detection lemma and the supplied `E.ComodulesAcyclic` feed
`E.invariantRingQuotient`. Thus the base ring is the actual equalizer of
source and target, the inclusion is faithfully flat, and its self-pushout
is the coordinate ring of `E.R`.

`serreCriterion_of_ringForm_of_nonzeroInvariant` applies that certificate's
geometric API to prove the exact proposition
`EtaleEquivalenceRelationSerreCriterionStatement.{u}` under the two explicit
inputs. Its introductions are exactly the hypotheses of the published
criterion. All published definitions and statements are imported unchanged.
The construction assumes no affine quotient, affine-descent conclusion,
or Serre criterion.

The module is an internal assembly of the supplied statement interfaces,
Worker 101's zero-detection adapter, and the conditional quotient construction
jointly developed with Worker 1203. No new literature assertion is translated.
