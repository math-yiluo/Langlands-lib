# Cofinal compact open block Iwahori factorization: proof

Author: Worker 70.

The theorem `Langlands.GeneralLinear.BlockShape.blockIwahoriBasis.{uF}`
proves the published `BlockIwahoriBasisStatement B T` from
`Langlands.Group.GL.BlockIwahoriBasisStatement`. Its complete parameters are
`{p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {n : ℕ}`,
`B : GeneralLinear.BlockShape n`, and `T : F.TopologicalData`. There are no
additional hypotheses. The field universe is arbitrary, and the statement
and every imported Library pair are unchanged.

The public theorem
`exists_compactOpenSubgroup_hasBlockIwahoriFactorization B T hU` exposes the
existence conclusion directly. After installing `T.topology`, its implicit
set `U : Set (GeneralLinear n F.Carrier)` and argument `hU : U ∈ 𝓝 1`
give an actual `K : OpenSubgroup (GeneralLinear n F.Carrier)` with compact
underlying set, contained in `U`, and satisfying
`B.HasBlockIwahoriFactorization T K`. This is a direct application of
`blockIwahoriBasis`, so it also covers every natural rank.

## Congruence preservation in the weak chamber

The private predicate `EntryIdeal O I g` means that each entry of `g - 1`
is the image of an element of the ideal `I : Ideal O`, where `O` is a
subring of the field. It is a Prop-valued definition.

For the upper radical, `entryIdeal_upper_conj` proves preservation under
`blockScalar(a) * g * blockScalar(a)⁻¹`, assuming that every forward ratio
`a_i/a_j`, for `i < j`, belongs to `O`. The proof rewrites the entries in
block coordinates using `B.indexEquiv` and `blockScalar_conj_apply`, then
splits into three cases:

- When `i < j`, the identity entry is zero, and multiplying the original
  ideal witness by the integral ratio gives a new witness in the same ideal.
- When `i = j`, the ratio is one, so the original witness works.
- When `j < i`, the upper parabolic condition makes the matrix entry zero,
  and the identity entry is also zero.

For the opposite radical, `entryIdeal_lower_inv_conj` treats
`blockScalar(a)⁻¹ * g * blockScalar(a)` with
`blockScalar_inv_conj_apply`. The upper blocks vanish. In a lower block
`(i,j)` with `j < i`, its multiplier is `a_i⁻¹ * a_j`, equal by
commutativity to the forward ratio `a_j/a_i`. The same ideal multiplication
argument applies. The diagonal multiplier is again one.

`principal_upper_conj` and `principal_lower_inv_conj` upgrade this entry
calculation to membership in the existing
`Conductor.principalCongruenceSubgroup O n I`. They use the published theorem
`Conductor.mem_principalCongruenceSubgroup_iff` from
`Langlands.Representation.Conductor.PrincipalCongruenceBasisProof`, which
requires the entry condition for both the matrix and its group inverse.
The inverse belongs to the same radical, and the inverse of either
conjugate is the corresponding conjugate of the inverse. Applying the same
entry calculation twice therefore supplies both conditions. No inverse
integrality is inferred from the forward condition alone.

For the supplied p-adic data, `weak_ratio_mem_integers` applies
`T.normalizedAbs_le_one_iff_mem_integers`. Every ratio in a weakly
contracting tuple belongs to exactly `T.Integers`. Ideal closure under
multiplication works for all these ratios, including those with normalized
absolute value equal to one. Thus the argument proves both containments
for every weakly contracting tuple.

## Construction inside an arbitrary neighborhood

The closing theorem splits the rank into zero and successor cases.

In positive rank `n + 1`, it installs the supplied `T.topology`,
`T.valuativeRel`, and `T.localField`. The published
`Conductor.exists_pos_principalLevelOpenSubgroup_subset F.Carrier n hU`
chooses a level `a > 0` whose existing principal open subgroup is contained
in `U`. Compactness is the existing
`Conductor.isCompact_principalLevelOpenSubgroup F.Carrier n a`.
The imported cofinality proof establishes trivial intersection of the
positive principal levels using Krull intersection in the valuation integer
ring and then uses compactness to obtain a level inside the neighborhood.

For this same level, the published
`principalLevelSubgroup_iwahoriProduct_bijective F.Carrier n B a ha` from
`Langlands.Group.GL.PrincipalBlockFactorizationProof` gives the actual
lower-Levi-upper multiplication bijection. Its factors are the intersections
with the opposite radical, the embedded common Levi, and the upper radical,
and all three lie in the same principal subgroup. The imported theorem is
proved by block elimination over the valuation integer ring and uniqueness
from the relevant subgroup intersections. No factorization witness is an
assumption of the present theorem.

The principal level is defined by the ideal
`IsLocalRing.maximalIdeal T.Integers ^ a`. The two private conjugation
lemmas, applied with this ideal and the integral ratios above, preserve
principal-subgroup membership. The existing
`blockScalar_conj_mem_unipotentSubgroup` and
`blockScalar_inv_conj_mem_oppositeUnipotentSubgroup` preserve the respective
radicals. Combining the two memberships proves the two intersection
containments in the published factorization predicate. Every topology,
valuation, integer ring, and normalized absolute value is the one supplied
by `T`.

At rank zero, `blockIwahoriBasis_zero` proves by matrix extensionality that
every group element equals the identity: there is no index in `Fin 0`.
The full open subgroup has underlying set `{1}`, hence is compact and lies
in every identity neighborhood. Its ordered multiplication map is
injective because its domain is a subsingleton, and is surjective using
`(1,1,1)`. Both conjugation containments reduce to the identity. This covers
the empty shape. Positive-rank one-block shapes are already included in
the imported factorization theorem; the weak inequalities impose no extra
condition when there are no pairs `i < j`.

## Provenance and scope

This proof derives the concrete GL result from the Library's actual block
subgroups and principal congruence subgroups. Its motivating original is
Bill Casselman, *Introduction to admissible representations of p-adic
groups*, Chapter III, *Induced representations and the Jacquet module*,
revision April 29, 2019, section 4, page 5, the definition of Iwahori
factorization and Lemma III.4.1. The registered source is
`casselman-2019-jacquet-module`, SHA256
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.
The retained original was read for this task; no applicable project errata
were found.

Casselman uses the strict chamber and motivates the basis by positive
congruence subgroups in the split case. The present weak-chamber containment
is a derived strengthening for actual GL, justified by the ideal-entry
argument above, including ratios on the boundary. The opposite-Levi-upper
order is retained. The proof asserts cofinal existence and the published
factorization predicate; it makes no assertion about contraction
convergence, compressed operators, canonical lifts, normality, or
simultaneous compatibility for other parabolics.
