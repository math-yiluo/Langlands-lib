# Local data for actual global Hecke characters

This internal assembly proves the complete local-data existence conjunct of
`Langlands.Global.HeckeGlobalFunctionalEquationStatement` for every number field
in arbitrary universe `u`, every actual Hecke character, and every existing
continuous nontrivial unitary additive character of the actual adeles that is
trivial on the diagonal field. No pairing equivalence is a premise of the
exported results. Nontriviality is already a field of the supplied
`UnitaryAdditiveCharacter`, so the additional nontriviality witness in the global
statement is unnecessary here.

The proved theorem `Langlands.Global.adelicDuality` supplies a group
homeomorphism from the additive adeles, retagged multiplicatively, onto their
full compact-open Pontryagin dual. Its evaluation is exactly `psi(a*x)`.
The wrappers `finiteAdditiveRestriction_ne_one` and
`infiniteAdditiveRestriction_ne_one` apply the existing local nontriviality
lemmas to this equivalence. Those lemmas use its injectivity and multiplication
by the actual one-place idempotent: a trivial local restriction would make that
nonzero idempotent annihilate the full adelic pairing.

`globalFiniteAdditiveComponent` and `globalInfiniteAdditiveComponent` bundle
these actual restrictions using the proved nontriviality, without requiring a
separate local proof from a caller. The finite constructor satisfies the exact
`IsFiniteAdditiveComponent` predicate and admits a self-dual Haar measure in
the original local topology, by the existing Haar-existence theorem.

`localData` applies the existing `localData_of_pairing` to this proved
equivalence. At every finite place it obtains the actual restricted additive
character and a nonempty type of its self-dual Haar measures, with precisely
the topology of `CompletionPadic.topologicalData`. At each real or complex
place it obtains a nonzero Fourier scale for the actual restricted additive
character and polar data for the actual infinite multiplicative component.
The completion ring equivalences, including Mathlib's chosen complex
embedding, are exactly those in the published predicates. The real scale uses
`exp(2*pi*i*a*x)` and the complex scale uses the positive trace character
`exp(2*pi*i*Tr(a*z))`. There is no restriction on the absolute value of the
Hecke character.

The provenance is direct composition of the actual adelic duality proof and
the previously constructed local-data adapter, without a new literature
assertion. The unchanged duality development is by Workers 1786 and 1843;
the local-data assembly is by Worker 1692. This unit proves local existence.
The convergence, meromorphic continuation and global functional-equation
conclusions of the host statement remain separate obligations.
