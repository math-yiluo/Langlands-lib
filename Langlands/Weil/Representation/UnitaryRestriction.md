# Restriction of actual invariant positive forms and unitary representations

Author: Worker 24.

This pair constructs restriction of the published positive Hermitian forms,
then restricts actual finite-dimensional unitary representations and their
genuine isomorphism classes. It retains the entire restricted action on the
original carrier, including when that action is reducible.

## The form construction

The generic declarations below are shared through
[Representation/Unitary/Restriction](../../Representation/Unitary/Restriction.md),
which contains their unchanged definitions, statements and proofs.

For monoids `G`, `H` and `J` in independent universes, a complex vector space
`V : Type uV`, an actual representation `ρ` of `G` on `V`, and a monoid
homomorphism `φ : H →* G`,
`Langlands.InvariantPositiveForm.comp b φ` is an invariant positive form for
`ρ.comp φ`. Its inner product core is exactly `b.toInnerProductCore`.
The invariance field at `h : H` is the old field at `φ h`.

Thus positivity, definiteness, Hermitian symmetry and both linearity laws are
inherited unchanged. `comp_inner` records the equality of values, and
`comp_id` and `comp_comp` establish identity and iterated precomposition laws.
`IsUnitarizable.comp` passes this constructor through the published existence
predicate. No topology, norm, completion, finite dimension, group inverse,
surjectivity or injectivity of the monoid map is needed here.

## Actual finite-dimensional representations

For groups `G : Type uG` and `H : Type uH`, with the carrier universe `uV`
independent of both, `FiniteRepresentation.restrictInvariantPositiveForm`
applies that same constructor to the published Mathlib-based
`FiniteRepresentation.restrict`. Its value formula is again definitional.
`isUnitary_restrict` uses the published equivalence
`isUnitary_iff_isUnitarizable` to preserve the finite-dimensional predicate.
That predicate asserts existence of a positive invariant Hermitian form.

`unitaryRestrict φ` maps the subtype of actual unitary finite representations
to the corresponding subtype for `H`. `unitaryRestrictClass φ` descends this
map to `IsomorphismClassesWith`. Well-definedness uses the existing
`restrictEquiv φ` on each actual invertible intertwiner. These quotients contain
all actual unitary representations, without an irreducibility condition.

With arbitrary topologies on the two groups, a proof of `Continuous φ`
additionally gives `continuousUnitaryRestrict` and
`continuousUnitaryRestrictClass`. The former combines the existing
`isContinuous_restrict` with the new form constructor; the latter again uses
`restrictEquiv` to descend through the genuine representation-isomorphism
relation. Continuity means the published usual complex module topology on
endomorphisms. No `IsTopologicalGroup` assumption is used.

The two rank lemmas are reflexive: the restricted representation has precisely
the original carrier and finite-dimensionality certificate. Rank zero is
allowed. There is no carrier resizing, irreducibility preservation, invariant
complement, irreducible decomposition, or map between irreducible lattices in
this pair.

## Provenance and dependencies

This is an internal derived transport construction from the published
`InvariantPositiveForm`, `IsUnitarizable`, `FiniteRepresentation.restrict`,
`restrictEquiv`, `isUnitary_iff_isUnitarizable`, and
`isContinuous_restrict`. Its form invariance proof is substitution of the
group argument; its quotient proof is restriction of the same intertwiner.
It adds no source theorem or existence assumption to those definitions.

The intended use in Henniart's construction is to retain unitarity of the full
local Weil restriction along a supplied actual local map. Henniart 2000,
sections 2.4–2.5, printed pages 445–446 (PDF pages 7–8), uses unitary global
Weil representations and their full local classes in the unitary integral
lattice. This elementary generic transport is a derived prerequisite, not a
transcription of a separately numbered result there.
Registered source: `henniart-2000-simple-proof`, SHA256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
Effective unitary irreducible expansion of this full class remains a separate
theorem obligation. No existence of local maps, global associated objects,
automorphic unitary support, absolute comparison or correspondence is asserted.

The imports are `Langlands.Representation.Unitary.Restriction`,
`Langlands.Weil.Representation.UnitaryProof` and
`Langlands.Weil.Representation.InductionContinuity`. They supply the existing
form, finite unitarity bridge, restriction functor and continuity result.
The prepared environment pins Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
