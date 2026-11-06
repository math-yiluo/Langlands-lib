# Actual rational gamma using common-compact ambient Haar

Author: Worker 200.

This is derived internal content motivated by Waldspurger, *La formule de
Plancherel pour les groupes p-adiques*, I.1, printed p.240 / PDF p.6, DOI
10.1017/S1474748003000082. That passage fixes left Haar measures with
`H ∩ K` of mass one, gives the open-cell integration formula (2), and
defines gamma by the positive parabolic-modulus integral over the opposite
radical. The local argument here is not a separately printed source lemma.

The setting is an arbitrary-universe nonarchimedean local field in any
characteristic and an affine locally finite-type group scheme. All
topological and measurable structures are the canonical ones on its actual
identity-test rational points. No splitness, quasisplitness or reductivity
hypothesis is used. A compact open subgroup `K` is supplied; this module
does not construct a special maximal compact.

`ambientHaar K hK` abbreviates the existing
`RankinSelberg.normalizedCompactOpenHaar K hK`. It is the regular left Haar
measure on the actual ambient rational-point group with `K` of mass one,
as `ambientHaar_self` records. It does not depend on a cocharacter.
The existing `gamma`, `gammaReal`, subgroup measures and `iwasawaModulus`
are unchanged.

`map_mul_right_eq_self_of_unipotent` proves that right translation by each
element of the actual dynamic radical preserves every ambient left Haar
measure. The existing regularity instance applies in the canonical locally
compact Hausdorff second-countable Borel topology. The published radical
compact-open containment theorem,
applied to a singleton, puts the element in a compact open subgroup of the
radical. The image of that subgroup under the actual inclusion is a compact
subgroup of the ambient group containing the element. The published theorem
`CompactFactorization.map_mul_right_eq_self_of_mem` then gives the equality
of pushforward measures. This needs neither smoothness nor whole-group
unimodularity. `map_mul_right_ambientHaar_of_unipotent` applies it to the
specified ambient Haar.

With the additional hypothesis `Smooth G.X.hom`,
`gamma_ne_zero_ne_top_of_smooth` proves that the original gamma is finite
and nonzero. Closedness supplies local compactness of the actual parabolic
and opposite radical. The published actual open embedding of their cell map,
together with the proved right invariance along the opposite radical,
instantiates the restricted local gamma theorem. Its local compact
intersection argument does not require conullness. In particular, the
finiteness conclusion has no supplied ambient measure or ambient
right-invariance premise. `gammaReal_pos_of_smooth` and
`ofReal_gammaReal_of_smooth` prove positivity and exact finite-value
conversion for the existing real gamma.

The last two results additionally retain the explicit factorization
`G(F) = P(F) K`, stability of `P(F) ∩ K` under the actual dynamic limit, and
right invariance of the actual normalized Levi Haar.
`integrable_iwasawaModulus_of_levi_rightInvariant` proves genuine Bochner
integrability on the original opposite radical with its unchanged normalized
Haar. The implemented proof restricts the existing locally constant scalar
modulus to that radical, obtains strong measurability from continuity,
uses positivity to identify the norm lower integral, and applies the existing
exact lower-integral gamma comparison and the new finiteness result.
It assumes no continuity of chosen Iwasawa components.

`gammaReal_eq_integral_of_levi_rightInvariant` converts the nonnegative
integral to its lower integral and uses that same gamma comparison to recover
the original real gamma exactly. The accompanying integrability conclusion
prevents the identity from relying on a default value for a divergent Bochner
integral.

General Levi unimodularity, realization of the displayed factorization and
compact-limit stability for a special compact, open-cell conullness and the
global integration formula, arbitrary same-Levi independence, and the
Plancherel conclusions remain separate obligations. This module removes the
ambient right-invariance premise of the earlier actual rational convergence
adapter; it does not assert any of those further results.
