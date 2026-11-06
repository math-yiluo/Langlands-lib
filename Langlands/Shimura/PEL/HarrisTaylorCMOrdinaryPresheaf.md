# The ordinary normalized CM presheaf on the full original test category

Author: Worker 344.

Fix an original Harris level whose Hodge image preserves the fixed Harris
integral source span. This internal construction uses the ordinary quotient of
the existing full Tate-normalized CM representatives. Its relation requires an
actual integral-order equivariant abelian-scheme isomorphism, the original
scalar polarization as integral cross-multiple data, and the original level
equation. The actual model still carries its original rational action,
determinant and dimension conditions, polarization, integral action and full
integral Tate normalization.

The canonical geometric point comparison uses the already constructed actual
ordinary point map along a chosen geometric path. The preceding path
independence theorem ensures that any such path gives the same quotient map.
`tateNormalizedCMOrdinaryClassEquiv_geometricComparison` compares this with the
unchanged normalized canonical point comparison by the identity on models.
`TateNormalizedCMOrdinaryGeometricFamily` consists of an ordinary class at each
actual geometric point, satisfying those canonical compatibility equations.
The pointwise quotient equivalences assemble to
`tateNormalizedCMOrdinaryFamilyEquiv`. Compatibility in both directions follows
from the point comparison square, and the inverse identities hold pointwise.

Ordinary family pullback applies actual ordinary quotient base change at each
pushed geometric point. Its coherence follows from the unchanged normalized
family pullback and the injective identity-on-models comparison. Quotient
base-change comparison gives an exact square for the family equivalence.
There is no construction of pullback by an inverse to a forgetful equivalence.

On a componentwise admissible base, the value is the product of these ordinary
families over its actual connected component schemes. Pullback uses the actual
restricted component morphism selected by the original scheme morphism and
the actual ordinary family pullback. The componentwise comparison commutes
with these maps. Its injectivity transfers identity and composition from the
unchanged normalized componentwise pullback. This constructs
`tateNormalizedCMOrdinaryDisconnectedPresheaf` on the full original test
category, with the unique empty-product value on an empty base.

`tateNormalizedCMOrdinaryDisconnectedNormalizedIso` is a natural isomorphism
with the existing full Tate-normalized presheaf. It requires no existence of
normalized models, fibre-affineness theorem or lattice-realization theorem.
The forward map is pointwise the identity-on-models quotient comparison.
Composing with the existing natural forgetful map gives
`tateNormalizedCMOrdinaryDisconnectedForget`. Under the two explicit generic
prerequisites `ProperFibreAmpleAffineOpenStatement` and
`CommensurableInvariantLatticeRealizationStatement`, the existing normalized
presheaf comparison gives `tateNormalizedCMOrdinaryDisconnectedIso` to the
original CM presheaf. Its forward map is exactly that forgetful map. The
source-stabilizer hypothesis remains in all ordinary constructions.

The provenance is internal: these are consequences of the existing ordinary
class relation comparison, actual point/base transport and full normalized
presheaf. No new external assertion is assumed. This compares presheaves of
the same actual normalized models. It does not construct an independent
ordinary PEL parameter scheme, discharge the generic normalization
prerequisites, treat arbitrary transporter levels, or prove division-case
representability.
