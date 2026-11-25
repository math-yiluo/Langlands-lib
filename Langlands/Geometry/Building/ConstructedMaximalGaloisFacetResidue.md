# Rational residue parabolics of constructed maximal Galois facets

Module `Langlands.Geometry.Building.ConstructedMaximalGaloisFacetResidue`.
This internal consequence works at arbitrary universe `u` and in both
characteristics.

Use the actual maximal-unramified coefficient extension of a nonarchimedean
local field `F`, a supplied maximal split-torus apartment with its original
Galois stability, actual centralizer and full omega compatibility. The
extended affine group is assumed connected reductive, and geometric
connectedness of the original group is required for model descent. In the
fixed-point problem `UnramifiedFixedPointSplitTorusStatement`, which this
module serves, the original connected reductivity supplies this
geometric connectedness. Let `E` be an original maximal Galois facet, meaning
a full facet meeting the coefficient-fixed locus and maximal among such
facets under original building incidence.

`ConstructedMaximalGaloisFacetResidueStatement` constructs actual downstairs
relative component models recovering the actual model at `E`, and valid
reductive quotient data `Q0` for its neutral special fibre. Every rational
parabolic inclusion into `Q0.quotient` is an isomorphism. It also proves the
algebraic consequence: every maximal split torus of this same quotient is
central and factors through every maximal torus, with maximal splitness
preserved in the factor. No model family, quotient descent comparison,
image bijection or coefficient covariance is supplied as a hypothesis.

## Implemented proof

Choose the published `UnramifiedZeroDatum.ofConnectedReductive` for the
extended group. Apply `unramifiedIntegerFacetModels` to the original integer
building data. It constructs actual full and neutral models for all full
facets with the two exact generic-point fixer formulas and actual incidence
morphisms. The published recovered-quotient theorem then constructs actual
downstairs component models and a valid downstairs quotient from the full
integral-point formula and the Galois facet. The actual upstairs quotient
is the literal residue base change of this quotient, projected through the
actual neutral model recovery; its identification with that base change
is the identity. The same theorem proves its validity and covariance of
all actual incident-facet images under the canonical residue coefficient
action.

The constructed family has the actual full facet-parabolic order bijection
for this valid quotient, by
`unramifiedIntegerFacetModels_hasFacetParabolicOrderBijection`. Feed it,
the canonical covariance and `MaximalUnramified.exists_order_eq_one` into
the published `galoisFacetResidueParabolics` theorem. The latter shows that
a base-changed rational parabolic has a coefficient-fixed incident facet;
maximality makes that facet `E`, whose image is the whole quotient. Faithfully
flat reflection then makes the original parabolic inclusion an isomorphism.
The published no-proper-parabolic split-torus result gives centrality and
containment in every maximal torus. All these conclusions concern the same
constructed downstairs quotient.

The transitive proof route uses the generic root-fixer and torus-adapter
results and no building-descent statement. This module does not lift
residue tori or prove fixation of the prescribed building point by units of
a maximal `F`-split torus; those are further steps towards
`UnramifiedFixedPointSplitTorusStatement`, which the Library proves as
`unramifiedFixedPointSplitTorus` in `UnramifiedFixedPointSplitTorusProof`.
