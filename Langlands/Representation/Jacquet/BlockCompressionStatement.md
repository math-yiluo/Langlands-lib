# Normalized block compression and the upper Jacquet quotient

Author: Worker 126.

`Langlands.Jacquet.BlockCompressionStatement.{uF, uV}` is one Prop-valued
definition stating two laws of the actual normalized compact compressed
operator. This module states these laws; it does not prove them.

## Inputs and conventions

The proposition universally quantifies over every prime `p`, every
`F : PadicField.{uF} p`, every supplied `T : F.TopologicalData`, every natural
rank `n`, and every `B : GeneralLinear.BlockShape n`. It installs exactly
`T.topology` and `T.generalLinearTopologicalGroup n`. The representation carrier
`V : Type uV` has an additive commutative group and a complex module structure;
its universe is independent of the field universe. The remaining inputs are
an actual representation `ρ` of `GeneralLinear n F.Carrier`, its smoothness
witness `hρ`, an actual open subgroup `K`, its compactness witness `hK`, and
`B.HasBlockIwahoriFactorization T K`.

The last predicate is imported unchanged from `BlockIwahoriDefinitions`. It
requires bijectivity of the lower-Levi-upper multiplication map and the two
conjugation containments for every weakly contracting block-scalar tuple.
Weak contraction means all forward absolute ratios `|a_i/a_j|` for `i < j`
are at most one, using `T.normalizedAbsUnits`.

Write `A(a) = B.blockScalar F.Carrier a`, `N = B.unipotentSubgroup F.Carrier`,
and `M = B.leviSubgroup F.Carrier`. The notation

`C(a) = Jacquet.compressedAction ρ hρ K hK (A(a))`

denotes the published endomorphism of `fixedVectors ρ K.toSubgroup`.
On an actual fixed vector it is `e_K (ρ (A(a)) v)`, where `e_K` is
`Compact.averageMap ρ hρ K hK`, the normalized compact average. No alternative
family of operators is quantified over or introduced.

## The two clauses

1. For all weakly contracting tuples `a` and `b`,
   `C(a * b) = C(a) * C(b)`. The tuple product is pointwise. The endomorphism
   product is composition, so the right side applies `C(b)` first.
2. For every weakly contracting `a` and every actual `K`-fixed vector `v`,
   `Jacquet.mk ρ N (C(a) v) =
   Jacquet.action ρ N M hMN (B.blockScalarInLevi F.Carrier a)
     (Jacquet.mk ρ N v)`,
   with fixed vectors coerced into `V` and
   `hMN = B.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier`.
   Both sides lie in the actual carrier `Jacquet.Coinvariants ρ N`.
   The descended action is unnormalized, so the equality contains no modulus,
   half-modulus, subgroup index, or other scalar.

The published `compressedAction_one`, `B.blockScalar_one`,
`B.isWeaklyContracting_one`, and `B.IsWeaklyContracting.mul` provide the
identity and chamber closure needed to interpret the first clause as the
multiplication law of a weak-chamber monoid action. That interpretation
requires a proof of the new proposition; this statement module supplies none.

There is no finite-dimensionality, admissibility, stabilization, quotient
surjectivity, canonical lift, pairing, or Jacquet admissibility hypothesis.
There is no nonzero condition on `V`, no positivity condition on `n`, and no
restriction on the number of blocks beyond `BlockShape` itself. In particular,
zero representations, rank zero and empty or one-block shapes are retained.
Constant scalar tuples are weakly contracting without any size bound.

## Source and derived normalization

The motivating original is Bill Casselman, *Introduction to admissible
representations of p-adic groups*, Chapter III, *Induced representations and
the Jacquet module*, revision April 29, 2019. The registered source is
`casselman-2019-jacquet-module`, SHA256
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.
Its retained PDF is
`/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter III - Induced representations and the Jacquet module--2019.pdf`.
The relevant locations are section 3, pages 3–4 (coinvariants and normalization),
section 4, page 5 (Iwahori factorization), and III.5.1–III.5.3, pages 5–6
(coset-sum formula, quotient compatibility, and multiplicativity). No project
errata file for this source was present when this module was written.

Casselman's `τ_a` is an unnormalized finite sum over `K a K / K`.
III.5.1 expresses it through upper-radical cosets. III.5.2 gives the image
`δ_P(a)^(-1/2) π_N(a) [v]`, where section 3 defines `π_N` with the inverse
half-modulus twist of the ordinary descended action. III.5.3 states
`τ_(ab) = τ_a τ_b` in the strict chamber. These are the source formulas,
not formulas asserted here for `C`.

The present proposition is a **derived translation** to normalized averaging
and the unnormalized quotient action. An upper-radical normalized average,
once justified as the expression for `C(a)v`, has quotient equal to
`[ρ(A(a))v]`: all its summands have that quotient and its coefficients sum to
one. The published `action_mk` identifies this with the second clause's right
side. Thus this formulation has no coset-count scalar and needs no
half-modulus conversion in its Lean equality. Multiplicativity is the
corresponding normalized averaging law for successive contractions. The
weak-chamber extension uses the stronger published containment predicate,
not an attribution of weak-chamber factorization to Casselman's definition.

This explanation does not assume or assert an equality between the actual
average and a rescaled `τ_a`, nor a Haar-measure/subgroup-index identity.
A subsequent proof must derive the two laws from the actual average and
factorization. One possible route is to invert the ordered product bijection,
use the lower containment and centrality in the Levi to see that
`ρ(A(a))v` is fixed by those factors, and justify reduction of the compact
average to the upper factor. Conjugation and averaging must then establish
the first clause. These are proof obligations, not facts established in this
module. Radical intersections need not be open in the ambient group; any
averaging over them must use their subgroup topology and a justified
restriction of the representation.
