# Actual auxiliary subgroups and opposite source gamma

Author: Worker 200.

This derived normalization step follows Waldspurger (2003), I.1 Remark (3),
printed pp.240–241 / PDF pp.6–7. It proves the special case of opposite
parabolics and the existence of a usable small subgroup for that pair.
It does not establish the general same-Levi assertion of the remark.

The existing actual `exists_dynamic_oppositeIwahoriContractionBasis`
theorem supplies one compact open H below any prescribed open K, with
factorization in both radical-first orders. Its source is the actual
cocharacter contraction construction and rational open-cell theorem,
already proved in the rational-point framework. The adapter uses global
uniqueness of rational open-cell factors and Levi normalization of each
radical to recover all three H memberships from the product. This yields
the precise Levi-first local membership conditions used in the gamma
index formula, for both a cocharacter and its opposite.

`gammaAuxiliarySubgroup` chooses such an actual H. Its specification
records compactness, containment in K and both membership equivalences.
The choice affects only evaluation of a pre-existing gamma: it does not
replace the fixed K, any Haar measure or the normalization of gamma.
`gamma_eq_auxiliary_gammaIndex` discharges the local H hypothesis of the
index formula using this choice. Compact-limit stability of K remains
explicit.

The actual centralizer is unchanged by reversing the cocharacter, and
reversing twice recovers it. The two radical trace indices swap, so
`gammaIndex_oppositeCocharacter` follows by commutativity. Evaluating the
two original gammas on the same auxiliary H then proves
`gamma_oppositeCocharacter`, under compact-limit stability for each
parabolic. This uses no ambient or Levi right-invariance premise and no
Iwasawa factorization premise.

The setting retains the arbitrary-universe local field, arbitrary
characteristic, canonical rational-point topology and connected reductive
group scheme. The selected small subgroup is proved for one opposite
pair. A single H valid for all parabolics, root-subgroup product indices,
general same-Levi independence and the main Plancherel conclusions remain
separate obligations. No special compact realization or removal of the
K stability premises is claimed.

This module uses ten distinct explicit local instance names with the
`sourceGammaOpposite` prefix so that the Iwasawa and gamma branches can be
imported together. This internal naming correction leaves every instance
type and body, mathematical declaration, hypothesis and proof unchanged.
