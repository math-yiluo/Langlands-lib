# Affine quotients by central subgroups of multiplicative type

`RelativeCentralMultiplicativeTypeQuotientStatement.{u}` asks for the
following construction over every scheme `S` in universe `u`. Let `G` be
smooth and affine over `S`, with connected geometric fibres. Let
`z : Z → G` be a closed central subgroup whose source is of relative
multiplicative type. There exist a group scheme `Q` over `S` and a
homomorphism `q : G → Q` such that `Q → S` is affine and `q` is an fppf
quotient by the range of `z`.

The last condition is the Library's `RelativeRoot.IsFppfQuotient`: the
underlying scheme map is flat, surjective and locally of finite
presentation, and the range of its actual kernel inclusion equals the
range of `z` on every relative scheme test. Centrality uses `IsCentral`,
which tests commutation after every further test morphism. Multiplicative
type means fppf-local isomorphism with a diagonalizable group whose
character group is finitely generated. It allows torsion characters,
including finite non-smooth and non-reduced subgroups.

There is no affineness, quasi-compactness, Noetherian, connectedness or
reducedness hypothesis on `S`. Neither a quotient nor an action is an
input. Smoothness is imposed on `G`, not on `Z`. This module defines the
quotient proposition; it does not prove it.

## Conditional reduction to the full-centre target

The helper theorem
`relativeAdjointQuotientExistence_of_center_and_centralMultiplicativeTypeQuotients`
retains two explicit assumptions: `ReductiveRelativeCenterStatement`
and the new quotient proposition. From the first it obtains the closed
full-centre inclusion `z`, its multiplicative type, and its centrality.
Reductivity supplies smoothness, affineness and connectedness of the
geometric fibres of `G`. The second assumption then constructs `Q` and
`q`. Rewriting the range of `z` as `center G` gives exactly the unchanged
`RelativeAdjointQuotientExistenceStatement`.

The base-change clause in the centre theorem is not needed for this
reduction. The conclusion asserts neither reductivity nor trivial centre
of `Q`. Both input propositions remain explicit; the helper is not an
unconditional proof of the full-centre quotient target.

## Source and derived scope

Brian Conrad, *Reductive group schemes* (2014), registered source
`conrad-2014-reductive-group-schemes`, original PDF
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`,
proof of Lemma 3.3.2, printed/PDF p.98.

The paragraph beginning with the fppf quotient sheaf constructs the
quotient of a smooth affine group by a central subgroup of multiplicative
type as an affine scheme of finite presentation over the base, citing
SGA3 VIII, 5.1 and IX, 2.3. The preceding fibrewise maximality assumption
in that lemma is used to establish centrality and the later
maximality conclusion; the quotient step itself uses the stated
central multiplicative-type subgroup. This proposition isolates that
step, retains geometric connectedness, and asks only for affineness and
the quotient projection with its full kernel. It omits the stronger
finite-presentation assertion for `Q → S`. The full-kernel condition
records the meaning of the represented fppf sheaf quotient.

The original page has been read. No source-specific errata note is
present in the Library. The registered author-homepage snapshot
`conrad-author-reductive-errata-check-2026-11-13` reports no separate
correction link attached to these notes, within that bounded check.
The conditional reduction is an internal consequence of the two
explicit Library propositions and the definitions of reductivity,
centre representation and fppf quotient.
