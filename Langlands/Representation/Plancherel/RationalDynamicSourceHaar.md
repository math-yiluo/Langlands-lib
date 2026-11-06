# Actual rational dynamic measures at the common compact scale

Worker 200. This is a derived specialization of the published dynamic
subgroups, rational-point topology, compact-open containment, and existing
generic source Haar constructions. It compares their original objects and measures.

Waldspurger, *La formule de Plancherel pour les groupes p-adiques*
(2003), I.1, printed p.240 / PDF p.6, gives each closed subgroup Haar
measure with its intersection with the same special compact subgroup of
mass one. The gamma display immediately before Remark (3) integrates the
positive parabolic modulus at an Iwasawa Levi component over the opposite radical. The present
module makes this normalization comparison on actual dynamic rational
subgroups, retaining the structural and measure premises stated below.
The specialization does not establish the existence or properties of
Waldspurger's special compact subgroup.

The field is any nonarchimedean local field in an arbitrary universe and
characteristic. The group scheme is affine and locally of finite type;
neither splitness nor quasisplitness is imposed, and reductivity is not
needed for these comparisons. Its rational points have the published
rational-point topology and its Borel measurable space. Local compactness,
Hausdorffness, nonarchimedeanness, and second countability are supplied by
the existing rational-point results, not additional user premises.

For an actual cocharacter chi, `P`, `M`, and `U` are the existing dynamic
parabolic, centralizer, and radical at the identity test object. The
semidirect decomposition and its continuous projection are the published
actual dynamic constructions. Closedness of `P` and `U` is already proved;
`isClosed_levi` derives closedness of `M` from the continuous projection.
The three measure abbreviations reuse `Haar.subgroupCompactOpenHaar`
for these literal subgroups, with one supplied compact open `K`.

`compact_split_iff_limit_stable` specializes the algebraic compact
factorization equivalence to the actual dynamic limit homomorphism.
`productParabolicHaar_eq_of_limit_stable` uses this stability to identify
the normalized Levi-radical product pushforward with the existing Haar
on the original parabolic. Compact limit stability is a displayed
hypothesis; it is not inferred from arbitrary compactness, nor proved
for a chosen geometric special compact subgroup.

The radical measure is right invariant because the published dynamic
compact-open containment theorem covers each original radical element
by a compact open subgroup. The existing compact-cover Haar theorem
then applies. Its inversion invariance follows by regular Haar
uniqueness at the same compact intersection: the inverse measure is
left invariant and regular, and inversion preserves that intersection,
so its mass remains one. This also applies to the opposite radical.
No radical invariance is assumed as new data.

`gamma` is the existing open-cell constant for these measures on the
original parabolic and actual opposite dynamic radical. It is defined
before and independently of Iwasawa choices. Under compact limit
stability, `gamma_eq_semidirect_of_limit_stable` rewrites the proved
parabolic measure equality to identify it with the generic semidirect
source gamma, with no scalar adjustment.

Given the displayed factorization `G(F) = P(F) K`, `iwasawaModulus` reuses
the actual scalar modulus of the generic construction.
`isLocallyConstant_iwasawaModulus` applies the earlier spherical-weight
argument with proved rational closedness and projection continuity; no
regularity of chosen components is assumed.
`gamma_eq_lintegral_of_levi_rightInvariant` additionally retains
right invariance of the actual normalized Levi measure and compact limit
stability as explicit premises. With radical invariance and all subgroup
normalization premises now proved, it gives exactly the source
nonnegative lower integral over the original opposite radical.

No reductive or Levi unimodularity theorem is assumed as an available
proof: the final comparison remains conditional on its displayed Levi
measure premise. This module does not prove gamma finite or nonzero,
Bochner integrability, actual open-cell conullness, existence or
factorization properties of the source special compact, all semistandard
comparisons, gamma independence of parabolic with fixed Levi, root-index
products, or any Plancherel conclusion. The generic real-integration
results and the separate actual conullness proof target retain their
own hypotheses and obligations.
