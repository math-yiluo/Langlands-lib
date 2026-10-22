# Finite-filtration vanishing criteria

Author: Worker 185.

This module states two internal algebraic consequences of a finite filtration.
Both declarations are definitions returning `Prop`; this module proves neither
proposition and supplies no theorem-valued data fields.

## Source and derived scope

The motivation is Bernstein and Zelevinsky, *Induced representations of
reductive p-adic groups. I*, Ann. Sci. ENS (4) 10 (1977), 441–472,
Corollary 2.13(a),(b), printed p.449 / PDF p.10. Their §1.10 explains
objectwise subfunctors, and §1.11 defines finite gluing by actual successive
quotients, both on printed p.445 / PDF p.6. Section 2.4, printed p.446 /
PDF p.7, observes that all subquotients of a quasicuspidal representation
are quasicuspidal, using exactness from §2.3(a).

The registered source is `bernstein-zelevinsky-1977-induced-i`, retained at
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`,
SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The source locations above were read directly. These two criteria are internal
derived statements, not transcriptions of new assertions in that article.
In particular, the article's geometric lemma and its specific induction and
Jacquet objects are not hypotheses of either statement.

## Actual filtration semantics

The imported `Langlands.ObjectRepFiltration A r` is a finite filtration of the
actual representation `A`, implemented as a filtration of its constant
one-object functor. Its invariant subspaces `S_i`, indexed by `Fin (r + 1)`,
are increasing, with `S_0 = ⊥` and `S_r = ⊤`. For `i : Fin r`,
`s.gradedRepresentation i` is the actual representation on the quotient of
`S_(i+1)` by the inverse image of `S_i` under the inclusion of `S_(i+1)` in
`A`. Monotonicity makes this the usual successive quotient `S_(i+1)/S_i`.
No abstract list of constituents replaces these quotients.

Repeated steps and zero quotients are permitted. The length `r` can be zero;
then the endpoint requirements already identify the zero and full subspaces.
Neither statement asks for a composition series or simple factors.

## Zero criterion

`Langlands.ObjectRepFiltrationSubsingletonStatement` quantifies over:

- any commutative ring `R : Type uR` and monoid `G : Type uG`;
- any actual representation `A : Rep.{uV} R G`;
- any natural number `r` and actual `ObjectRepFiltration A r`.

Its sole additional hypothesis is `Subsingleton (s.gradedRepresentation i)`
for every `i : Fin r`. Its conclusion is `Subsingleton A`. Here a
subsingleton module carrier is exactly a zero module, because it contains
zero. The three universes are independent. No field, group, topology,
smoothness, finite-dimensionality or finite-length assumption is needed.

The intended elementary argument is that a zero successive quotient forces
two consecutive subspaces to agree. Finite induction, together with the
zero and full endpoints, then makes every ambient vector zero. This describes
the provenance of the target, not an implemented proof.

## No quasicuspidal subquotients criterion

`Langlands.CuspidalSupport.PadicLeviFiltrationNoQuasicuspidalSubquotientsStatement`
quantifies over every natural prime `p` with `Fact p.Prime`, every
`F : PadicField.{uF} p`, and every compatible `T : F.TopologicalData`.
The local instance `T.topology` supplies the topology used by the smooth
representations. It then quantifies over every natural rank `n`, block shape
`B : BlockShape n`, smooth complex representation
`A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)`, length `r`, and actual
`s : ObjectRepFiltration (Rep.of A.representation) r`.

For each `i : Fin r`, the hypothesis supplies a smooth representation `Q`
of that same Levi and an actual `Representation.Equiv` from
`(s.gradedRepresentation i).ρ` to `Q.representation`. This is a bijective
complex-linear intertwiner. It also requires that every smooth `D` with
`SmoothRep.IsSubquotient D Q` and `IsLeviQuasicuspidal B D.representation`
has `Subsingleton D`. The representatives and equivalences are mathematical
hypotheses, not chosen identifications or consequences assumed from the
geometric lemma.

The conclusion makes the same assertion for every smooth subquotient `D`
of `A`: quasicuspidality implies `Subsingleton D`. Thus it expresses absence
of nonzero quasicuspidal smooth subquotients without restricting to
irreducible constituents. The carriers of `A`, the representatives `Q`, and
the tested `D` are arbitrary types in `uV`; the existing
`SmoothRep.IsSubquotient` relates objects in one carrier universe. The local
field universe `uF` and this carrier universe `uV` are independent. In
particular, the statement can be instantiated with carrier universe
`max uF uV` for geometric-lemma consumers.

Concretely, `SmoothRep.IsSubquotient D A` means that there exist an actual
invariant submodule `S` of `A` and an actual invariant submodule `U` of its
smooth restriction to `S`, together with a smooth-category isomorphism
from `D` to the actual quotient `S/U`. The predicate
`IsLeviQuasicuspidal B` means that every proper standard block refinement of
`B` has zero actual unipotent coinvariant module. Smoothness comes from the
quantified `SmoothRep` objects; admissibility is not part of this predicate.

There are no admissibility, irreducibility, finite-dimensionality, finite-length
or positive-rank assumptions, and length zero is included. Quasicuspidality
of `A` or of the graded representatives is not required.

For provenance, a smooth subquotient of `A` inherits a finite filtration by
intersecting its representing submodule with the steps of `s` and taking
images in its quotient. Each induced graded piece is a subquotient of an
original graded piece and, after transport, of `Q`. If the tested subquotient
is quasicuspidal, hereditary quasicuspidality makes these induced pieces
quasicuspidal. The hypotheses therefore make them zero; the first criterion
then makes the tested subquotient zero. Hereditary quasicuspidality and these
filtration/subquotient constructions remain proof obligations, not extra
assumptions hidden in either proposition.
