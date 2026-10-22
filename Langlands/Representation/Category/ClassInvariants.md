# Conditions on actual smooth isomorphism classes

Worker 30 constructs two predicates on the published quotient
`Langlands.SmoothDualClass`: prescribed scalar action of a character of the
actual center, and existence of a nonzero vector fixed by a specified
subgroup. `ofRep` is the ordinary quotient constructor. No representative is
selected, no carrier universe is resized, and the representation carriers
need not be finite dimensional.

The intrinsic well-definedness proofs use actual isomorphisms.
`fixedVectors_ne_bot_iff_of_equiv` transports a nonzero fixed vector and uses
injectivity to preserve nonzeroness. It reuses the published
`fixedVectorsEquiv`; the two carrier universes are independent.
`SmoothRep.hasCentralCharacter_iff_of_iso` transports scalar action through
the equivariant linear equivalence recovered from the categorical
isomorphism. Surjectivity handles every target vector. Applying the same
argument to the inverse proves each converse.

`HasCentralCharacter` and `HasFixedVector` descend by `Quotient.lift` using
these equivalences of propositions and propositional extensionality.
Their evaluation formulas on `ofRep` are definitional.
`centralFixedStratum` is the set satisfying both conditions. It is a set of
actual irreducible admissible smooth isomorphism classes; there is no
finiteness assertion about this set in this construction.

These are internal constructions needed to state Bernstein--Zelevinsky's
fixed-central-character finiteness assertion on a quotient. Their provenance
is the scalar-action and fixed-space conditions in Bernstein and Zelevinsky,
*Representations of the group GL(n,F), where F is a non-Archimedean local
field*, Russian Mathematical Surveys 31:3 (1976), Corollary 4.15, page 41.
The mathematical finiteness conclusion applies to the supercuspidal
restriction and remains a separate proposition. Source ID
`bernstein-zelevinsky-1976-representations-gln`, SHA256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
The original pages 28--43, including the whole corollary and proof of its
preceding theorem, have been read. This construction does not use that
theorem as a proof assumption.

The imported `Langlands.Representation.Category.Basic` and
`Langlands.Representation.Smooth.FixedVectors.Definitions` are published
Library modules. Their actual actions, intertwiners, full subcategories,
fixed submodules and quotient by categorical isomorphism supply all objects.
The generic coefficient-field and group-with-topology scope enlarges
only the domain of these constructions; no local representation theorem is
generalized. In the fixed-space transport lemma even topology is unnecessary.
The ambient topology on the group need not satisfy a continuity axiom.
No central-character existence, automatic admissibility, fixed-vector
exactness, or local correspondence is assumed.

The quotient laws and transport lemmas are intrinsic parts of this construction.
They do not prove any representation-theoretic finiteness assertion.
