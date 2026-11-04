# Anisotropy of the actual finite-separable norm-one torus

Author: Worker 1107.

This module declares a proposition about the actual group scheme of norm-one
units of a finite separable field extension. It supplies a statement definition;
its Lean proof is a separate obligation.

Let `k` and `K` be fields in the same arbitrary universe, with a specified
`k`-algebra structure and `[FiniteDimensional k K]`. The declaration

`Langlands.GroupScheme.WeilGm.normOneAnisotropyStatement k K`

has the explicit premise `Algebra.IsSeparable k K` and concludes

`IsAnisotropic (WeilGm.normOne (CommRingCat.of k) K)`.

Here `normOne` is the published group-scheme kernel of the determinant norm
from `WeilGm.groupScheme (CommRingCat.of k) K` to the multiplicative group.
It is an object of `Grp (Over (Spec k))`. Its points on every test scheme are
the tensor units whose determinant norm is one, by the published
`WeilGm.normOnePointsEquiv`. The existing
`WeilGm.normOne_isTorus_of_finite_separable` proves that this actual group is
a torus under the same finite-separable hypotheses; torus status is therefore
not an additional input to the new proposition.

## Exact meaning and hypotheses

`IsAnisotropic N` is the published equality `splitRank N = 0` in
`Rational.SplitTorus`. That rank is the supremum in `ℕ∞` of `Nat.card I`
over finite types `I` admitting a closed-subgroup homomorphism
`splitTorus (Spec k) I → N`. Equivalently, by the published
`isAnisotropic_iff`, every such index type is empty. Thus the conclusion
concerns actual closed split subtori and their scheme morphisms. It is not
merely a statement about field-valued points or fixed vectors of an abstract
lattice.

The target includes all characteristics and extension degrees, including
degree one. It requires no perfectness of `k`, normality or Galois hypothesis
on `K/k`, chosen splitting field or embedding, or assumed descent
surjectivity. The extension algebra `K` is a field; a finite separable product
algebra is outside this statement. Neither the absence of split subtori nor
cocharacter vanishing is a premise.

## Provenance and intended derivation

This is a derived internal target built from the published norm-one
construction, lattice comparisons and split-rank predicate. The following is
a mathematical derivation explaining its provenance, not an implemented Lean
proof of this module's proposition.

The published norm-one Galois fixed-lattice result
`WeilGm.normOneGaloisFixedLattices` identifies the fixed cocharacter lattice
as zero over a normal splitting field. The published canonical fixed-lattice
map and its field-base-change injectivity in `Torus.LatticeBaseInvariants`
then give the intended ground-field cocharacter vanishing. That conclusion
has its own existing proposition,
`WeilGm.normOneRationalCocharacterVanishingStatement`, within
`WeilRestrictionNormOneRationalStatements`. This module uses the actual
norm-one object and does not assume that separate proposition.

For the remaining comparison, let `i : Gm^I → N` be any closed split-torus
inclusion. For an index `j : I`, compose the coordinate cocharacter
`splitTorus.single (Spec k) I j` with `i`. This is an actual cocharacter of
the commutative norm-one group, so ground-field cocharacter vanishing makes
it zero. A closed immersion is a monomorphism; cancellation makes the
coordinate cocharacter itself zero. Composing with the matching coordinate
projection and using `splitTorus.single_comp_proj` gives `id_Gm = 0`.
The published `gmEndEquiv k` sends these morphisms to `1` and `0` in `ℤ`,
which is impossible. Therefore `I` is empty, and `isAnisotropic_iff` gives
the required rank-zero conclusion. This route uses whole group-scheme
morphisms, retaining arbitrary relative tests, including nonreduced tests.
It requires neither a positive-rank witness supplied as a hypothesis nor a
general invariant-descent surjectivity theorem.

## Source conventions

The rank-zero convention is that of Borel and Tits, *Groupes réductifs*
(1965), Definition 4.23, printed p.93 / PDF p.40, source ID
`borel-tits-1965-groupes-reductifs`, SHA-256
`ec6674ba292deaadd77a449f4bad3750db79c0b87b117a892ef6b09bb16357ad`.
The adjacent Theorem 4.21 explains the common rank of maximal split tori.
This source passage supplies the convention, not the specialized norm-one
result or its proposed Lean proof.

Milne, *Algebraic Groups* (2017), Definition 25.3 and footnote 1, printed
p.545 / PDF p.561, source ID `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`,
uses absence of a noncentral split torus instead. For a commutative group
that convention alone would not give the present no-nontrivial-split-subtorus
assertion. The complete registered Milne errata snapshot of 2 November 2026
contains no correction to Definition 25.3 or its footnote. The new target
uses exactly the existing Borel–Tits predicate.

This statement does not supply the proof of cocharacter vanishing, the
actual-subtorus comparison, general descent surjectivity, an isomorphism of
rational-point quotients, or any integral-model assertion. The proof of the
new proposition remains to be independently submitted and checked.
