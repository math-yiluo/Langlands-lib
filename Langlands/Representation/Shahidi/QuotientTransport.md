# The inverse-transpose transport of quotient measures

This module implements the quotient transport in Shahidi, *Fourier transforms
of intertwining operators and Plancherel measures for GL(n)* (1984), printed
page 75, measure item 1, continuing on page 76. It is a derived measure
prerequisite. The group map, quotient map and pushforward are actual
constructions; their well-definedness and transport laws are proved.

## Source and coordinates

Write `r = n + 1`. The source begins with a measure `d'a` on the primed
quotient associated with the lower-right `GL_n` subgroup of `GL_r`.
It prescribes a measure `dã` on `N_n \ GL_n` by the displayed formula
`dã = d'(w · (a⁻¹)ᵀ · w⁻¹)`, where `a` is embedded in the upper-left
block and `w` is the long Weyl representative of the larger group.
The transpose and inverse in this formula are both retained.

In the lower-right coordinates `b ↦ diag(1,b)`, the map in that formula is

`φ(a) = w_n · (a⁻¹)ᵀ · w_n⁻¹`.

Here `w_n` is the antidiagonal matrix with entries one. The theorem
`quotientReflection_insert` verifies the full larger-group matrix equality:

`diag(1, φ(a)) = w_(n+1) · (diag(a,1)⁻¹)ᵀ · w_(n+1)⁻¹`.

The actual insertion maps in this theorem are `Bruhat.insert 0` and
`Bruhat.insert (Fin.last n)`. As the long Weyl matrix is its own inverse,
the Lean formulas write the final factor as `w`.

For the primed quotient we use the upper-unipotent subgroup of that
lower-right block, as in `KirillovMeasure`: the source's literal
`N' = w_r N_n w_r⁻¹` on page 74 instead gives the lower unipotents.
This is the explicitly documented source interpretation supported by
Whittaker descent and the restriction convention on page 71, not a
published erratum. The current transport gives further concrete support:
transpose-inverse takes upper unipotents to lower ones, and long-Weyl
conjugation takes them back to upper ones. Thus the displayed page 75 map
has a well-defined map between the quotients with this interpretation.
The module does not assert that it descends to the literal primed lower
quotient. Worker 11 contributed the underlying primed-subgroup analysis.

## Definitions and hypotheses

`quotientReflection n F` is the multiplicative equivalence `φ`, formed by
composing the published inverse-transpose equivalence with conjugation by
`weylLong n F`. Its algebraic results hold for every commutative ring and
every natural rank, including zero.

With a topology making `F` a topological ring,
`quotientReflectionContinuous` is the corresponding continuous group
equivalence. `quotientReflectionHomeomorph` is its actual descent to
`QuotientIntegration.LeftQuotient (upperUnipotent n F)`, the space of left
upper-unipotent cosets. Its evaluation lemma maps the class of `a` to the
class of `φ(a)`. Both the group map and quotient map are involutive.

For any Borel measurable structure on that quotient,
`reflectedQuotientMeasure n F ν'` is the pushforward of `ν'` along this
homeomorphism. Since `φ` is involutive, this is also the pullback described
by the source's differential notation. More concretely, for measurable
`E` its value is `ν'(φ⁻¹(E)) = ν'(φ(E))`.
`IsQuotientReflectionRelated n F ν ν'` is the Prop-valued equation
`ν = reflectedQuotientMeasure n F ν'`; the commutation theorem proves its
equivalence to the reverse equation.

## Implemented proofs

The reflection formula unfolds the composite equivalence. Applying it twice
uses multiplicativity of inverse transpose, its involutivity, and the fact
that it fixes the long Weyl matrix, which squares to one. The insertion
identity is proved entry by entry, separating the isolated coordinate and
the remaining coordinates. Reversing indices exchanges the first and last
isolated positions, while transposing the inverse exchanges the two entry
indices.

For membership in the upper-unipotent subgroup, the reflected entry at
`(i,j)` is the inverse matrix entry at `(j.rev,i.rev)`. When `j < i`, this
is a strictly lower entry of the upper-unipotent inverse and hence zero;
diagonal entries remain one. Involutivity gives the converse membership
implication. Multiplicativity then preserves and reflects the left-coset
relation, supplying the hypotheses of `Homeomorph.Quotient.congr`.

`quotientReflectionHomeomorph_rightTranslate` follows on representatives
from `φ(xg) = φ(x)φ(g)`. The pushforward involution follows by composing
the two measurable maps; applying it to a measure equality proves
injectivity. Standard measurable-equivalence change of variables gives the
complex integral equality and the integrability equivalence. Pushforward
preserves nonzeroness in both directions and preserves regularity when the
input measure is regular.

`reflectedQuotientMeasure_right_invariant` proves that right invariance
is also preserved when supplied for the input measure. Indeed, right
translation by `g` after reflection equals reflection after translation by
`φ(g)`. Composing measure pushforwards and using invariance of the input
measure yields the asserted measure-preserving right translation.

## Scope

No measure is chosen from an existence assertion. The bare reflection
relation does not require Haar or regularity hypotheses and permits the zero
measure; the separate lemmas preserve such supplied properties precisely
as stated. These constructions do not supply the Proposition 1.2 pairing,
the `dn₁ dn₂` decomposition, compatibility of the quotient with group and
subgroup Haar measures through a Weil formula, or the remaining normalized
measure system. Those are separate obligations. No representation-theoretic
existence, continuation or comparison theorem is proved here.
