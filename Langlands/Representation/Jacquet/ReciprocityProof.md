# Character-twisted reciprocity proof

Worker 174 proves the existing `Langlands.Jacquet.CharacterReciprocityStatement`
in `Langlands.Jacquet.characterReciprocity`, retaining its independent group,
source-carrier and target-carrier universes and all its hypotheses.

The proof constructs evaluation at identity as a linear map. Equivariance into
right-translation induction identifies evaluation of a translate with evaluation
at that group element. Covariance of the induced functions then gives the
character times the target action. Triviality of both the character and target
representation on `N` makes this map constant on `N`-orbits, so `Jacquet.lift`
descends it through the actual relation quotient. Multiplying by the inverse
character proves equivariance for the specified twisted coinvariant action.

For the inverse, an intertwiner `A` on the coinvariants gives the function
`g ↦ A (mk rho N (rho g v))`. Its covariance follows by moving the inverse
character from the source to the target. These functions define an algebraic
intertwiner into the existing covariant-function representation. The existing
`smoothLift` restricts this map to the actual smooth vectors: an open subgroup
fixing `v` fixes its entire orbit function under right translation. The two
composites are identities, by evaluation of a translate and by `rho 1 = 1`.
Linearity is checked on the surjective quotient map. The required formula
`e F (mk rho N v) = F(v)(1)` is definitional for the constructed equivalence.

This is a direct proof of the formulation derived in the statement's Markdown.
Its original reference is Bernstein–Zelevinsky, *Induced representations of
reductive p-adic groups I* (1977), §1.8, printed pp.444–445 (PDF pp.5–6),
for covariant functions, right translation and the relation quotient, and
§1.9(b), printed p.445 (PDF p.6), for adjointness. The parabolic specialization
is §2.3(b), printed p.446 (PDF p.7). These pages were read from the registered
source `bernstein-zelevinsky-1977-induced-i`. The full `P`-action used here is
the existing statement's derived formulation, rather than a new claim that
BZ77's Levi subgroup equals `P`.

The proof only uses the topological group structure and smoothness of `rho`
among the topological assumptions. The additional hypotheses remain in the
published target and are accepted by the theorem. No supplied adjunction or
replacement representation is introduced; the statement and its dependencies
are imported unchanged.
