# Actual standard induction at a prescribed normal compact open level

This internal specialization applies the normal-level normalized-induction
criterion to the published standard rational-point subgroups, at the level
specified in the fixed-vector category target. The field and representation
carrier universes are independent.

The published `neg_mem_simpleRelativeRoots` and `IsStandardCocharacter.neg`
from `Langlands.Representation.Aubert.General.RationalOppositeChamber`
reverse the chamber and simple-root face.
Negation stability of the actual relative roots implies that negating a
simple root and the chamber preserves simplicity: a decomposition of the
negated root into two opposite positive roots would negate to a forbidden
decomposition of the original simple root. Consequently, if `ζ` is standard
for `J` relative to `ν`, then `-ζ` is standard for `-J` relative to `-ν`.
These helpers assume only the stated relative-root negation property.

The choice-free standard subgroup definitions put the original parabolic
inside the dynamic parabolic of `ζ`, and the opposite standard radical inside
the dynamic unipotent of `-ζ`. The latter is the opposite cocharacter of
`ζ`. The published all-test opposite-intersection theorem therefore proves
that these actual subgroups intersect trivially on every test scheme.
This argument requires only one standard cocharacter and relative-root
negation; it does not require a comparison equality for the entire standard
subgroup functors.

For the actual standard family of a maximal split torus in a connected
reductive group, relative-root negation and existence of a standard
cocharacter are supplied by published unconditional proofs. The actual
Iwahori intersection decomposition and the preceding trivial intersection
therefore show that the actual Levi projection preserves `K ∩ P_I`.
The minimal-standard `M N K₀` factorization supplies `G = P_I K₀` by the
published standard factorization theorem.

`standardNormalLevelEvaluation` restricts actual normalized standard
induced `K`-fixed vectors to `K₀`, with values in the fixed vectors of the
coefficient representation under the literal inverse image of `K` in `M_I`.
The final nontriviality equivalence is the generic normalized criterion with
projection stability, parabolic closedness and factorization discharged by
the preceding actual standard results.

The standard family is the published geometric family, constructed
unconditionally by `Jacquet.standardBernsteinFamily` from connected
reductivity, a maximal split torus and a generic cocharacter.
The coefficient representation is any smooth complex action of the literal
standard Levi. No cuspidality, admissibility, irreducibility or finite length
is assumed. The group `K₀` need only normalize `K` and satisfy the stated
minimal-standard factorization; neither its compactness nor `K ≤ K₀` is
required.

The provenance is the published chamber-negation results and the internal
intersection argument above, followed by specialization of the published actual projection,
standard factorization, compact half-modulus and normalized induction
constructions. The result detects nontriviality of the whole induced fixed
space. It does not prove generation by the specified fixed vectors,
visibility of every irreducible constituent, or the host category theorem.
