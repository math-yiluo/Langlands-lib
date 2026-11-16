# Descent of inner local isomorphisms through Borel stabilizers

This internal module constructs an actual group-scheme isomorphism from
an inner local family between reductive groups with chosen relative Borels,
a supplied actual representative of the source Borel stabilizer, and the
sectioned quotient geometry used by `SectionedWeilInnerDescent`.

The base is `Spec R` for a commutative ring object R. The source Borel is
an actual inclusion iG : B to G; the target is an actual inclusion
jH : B' to H. Both ambient groups are reductive. A supplied fppf quotient
qG : G to Gad has full kernel the scheme-theoretic center, and an action c
of Gad on G restricts along qG to conjugation. The original local family e
lives on any single flat, surjective, locally finitely presented cover V
of the base, and has all-refinement inner discrepancy for c. No cocycle,
subgroup-valued discrepancy or Borel-preserving property of e is supplied.

The sectioned geometry consists of maps i : K to B, p : B to T and
t : T to B, with t followed by p the identity; z : Z to T; and fppf
quotients qB : B to P and qT : T to D. Their full kernel ranges are
respectively range i, range (z followed by t), and range z. The inclusion i
is monic, K is affine over the base and has a supplied actual finite
vector-bundle series, and P has affine total space. An actual isomorphism
D to `WeilGm.groupScheme R C` is supplied for a module-finite projective
commutative R-algebra C. Finally a supplied monic k : P to Gad represents
exactly `c.subgroupStabilizer (range iG)` on all relative tests. In particular
P is the same actual group in the sectioned quotient and the stabilizer
presentation; it is not a surrogate group with unrelated coefficients.

`SectionedQuotientExtension.borelInnerIsoOfPicTrivial` gives the actual
isomorphism G to H when Pic C is trivial. Its proof first constructs the
affine fppf Borel-preserving refinement and its actual conjugating cochain.
The quotient-action twist of the refined family preserves the two full
Borel ranges and retains inner discrepancy. Faithfulness of c follows
from its full-center quotient description. The existing
`subgroupInnerCocycle` then constructs a natural P-valued cocycle from that
inner discrepancy and the represented stabilizer, including its cocycle
law and discrepancy equation. The already proved sectioned-quotient
vanishing theorem makes this cocycle trivial. The published fppf descent
of local group isomorphisms yields the required actual G-isomorphic-to-H
object.

`borelInnerIsoOfFiniteAlgebrasHaveTrivialPicard` uses finite-algebra Picard
triviality of R to discharge Pic C. `borelInnerIsoOfSemilocal` obtains that
property from finiteness of the maximal spectrum of R. Both retain all the
stated geometric data. The total space of the original cover V need not
be affine or quasi-compact; the construction chooses its own affine fppf
refinement covering the base.

The provenance is internal composition of actual Borel correction,
full-center quotient faithfulness, stabilizer-valued natural cocycles,
sectioned-quotient vanishing and actual fppf descent. This construction
removes the earlier requirement to supply subgroup-valued inner discrepancy.
It does not construct a special quasi-split form, the sectioned Borel
geometry, a radical filtration or a WeilGm presentation, and does not prove
the unconditional semi-local inner-form statement.
