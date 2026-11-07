# Actual Frobenius orbits of supplied highest-weight vectors

This derived unit proves injectivity and the dimension of the actual
opposite-unipotent Frobenius orbit of a supplied highest-weight vector. It
combines the linked full-root word coordinates and original endpoint from
`HighestWeightWordCoordinates` with `OrderedFrobeniusCyclicity`. No external
existence or dimension theorem is used.

Work over a field `k : Type u` with an affine group scheme `G`, a supplied split
pinning `p`, a finite root index, and full integral coroot span. Put
`ν₀ = p.rootDatum.Polarization (IntegralWeylVector.rho ...)`. Throughout the
construction the opposite unipotent group is the existing actual closed
representative
`Dynamic.Affine.unipotentScheme (CommGroupScheme.groupHom (-ν₀) ≫ p.inclusion)`.
Its inclusion into `G` is the existing `unipotentHom`.

For actual simple-reflection representatives and a word whose successive roots
enumerate all positive roots, `linkedWordRoot` records those original root
indices and `linkedWordWeight` their negative characters. Each character has
positive pairing with `-ν₀`. The previously proved full-root representation of
each linked word factor therefore puts its entire image in the opposite dynamic
unipotent functor. `linkedWordUnipotentMap` lifts that same factor through the
representing inclusion. Its composite with the inclusion is proved equal to the
original factor as a group-scheme morphism.

Conjugation by the original torus preserves the dynamic subgroup, so the
represented-subgroup action constructs `oppositeRhoUnipotentAction`. Cancelling
the monic inclusion transfers the original factor's all-algebra torus scaling
law to its lift. This preserves the factor order and requires no commutation
between different factors.

The lifted ordered point, followed by the inclusion, is exactly the original
ordered root product. The parameter comparison is the actual
spectrum/global-section isomorphism on each coefficient algebra. The full
opposite-root factorization on arbitrary relative test schemes then gives
bijectivity of this lifted chart on every commutative coefficient algebra.
Testing the two universal points, as in `OrderedFrobeniusCyclicity`, gives
bijectivity of its actual coordinate-algebra pullback.

The representation conclusions additionally assume `Infinite k` and a supplied
finite matrix representation `ρ` satisfying `p.IsHighestWeight` at `m rho`.
This existing predicate includes irreducibility, complete weight decomposition,
a one-dimensional highest space and lower-weight support. Restricting `ρ` to the
actual unipotent group does not change any ordered coefficient, because each
lift composed with its inclusion is the original factor. For a tuple constantly
equal to `m`, the original linked-word endpoint is consequently nonzero on every
nonzero vector of that highest-weight space.

Now let `[ExpChar k q]`, let `r` be any natural number, and take `m = q^r - 1`.
The chart and its positive-height torus scaling meet the hypotheses of
`OrderedFrobeniusCyclicity`. Its intrinsic top distribution is the original
constant-degree coefficient just proved nonzero. Thus the full intrinsic
distribution orbit map for `ρ` restricted to the actual opposite unipotent group
is injective. Its intrinsic origin orbit span has dimension `(q^r)^l.length`.
This span uses all commutative coefficient algebras, including nonreduced ones.

The final theorems choose the word and representatives from the supplied
pinning. A bijection from word positions to the positive-root subtype proves
that its length is
`N = Fintype.card {j : p.rootIndex // p.base.IsPos j}`. Hence the final orbit
dimension is `(q^r)^N`, with no word or representative hypothesis left in that
conclusion. A separate upper bound by this number on the entire supplied
representation makes the origin orbit span equal to the whole representation,
by equality of finite dimensions.

The split pinning, full coroot span, infinitude and highest-weight representation
remain explicit inputs. This unit does not construct the pinning or the
highest-weight representation, and it does not prove the upper bound for an
entire covariant induced space. In particular it supplies neither the remaining
whole-induced-space irreducibility law nor `SteinbergBigCellStatement`.
