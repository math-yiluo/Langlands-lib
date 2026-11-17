# Reducing torus rigidity to split affine bases

This internal derived reduction uses the original all-test conjugation
predicate and the unchanged `ReductiveIsogenyTorusRigidityStatement`.

`fppfLocallyTorusConjugate_of_cover` assumes an fppf cover of the base and
local conjugating covers for the canonical pullbacks on all its members. It
composes these covers. Each conjugating point projects to the original
commutative group by `baseChangePointsEquiv`; the all-test conjugation equation
transports by `torusConjugates_baseChange_iff`. The parameter scheme differs
from the composed cover member only by the identity map of its underlying
scheme, so restriction gives the required point and predicate.

`SplitAffineIsogenyTorusConjugacyStatement` is the remaining local existence
proposition. Over every affine base, the source and target are reductive group
schemes with supplied commutative groups whose inclusions have aligned full
split maximal-torus coordinates. For two isogenies, the first torus restriction
factors through the supplied target torus, and the two restrictions agree. The
conclusion is the existence of an fppf cover with all-test torus conjugators.
Each coordinate package is aligned with its own supplied inclusion; the two
root data need not be identified, and compatibility of the isogenies with
those data is not supplied as an additional premise.
No proof of this local existence proposition is asserted in this unit.

`fppfLocallyTorusConjugate_of_splitAffine` assumes that local existence
proposition. For the two supplied relative maximal tori over an arbitrary
scheme, simultaneous splitting gives an affine etale neighbourhood of every
base point with both aligned coordinate packages. Choose one neighbourhood
per point and regard the family as an fppf cover. Reductivity, isogenies, the
torus factorization and equality of torus restrictions all pull back. The
supplied affine existence proposition applies on each member; composing its
conjugating covers gives the conclusion over the original base.

`reductiveIsogenyTorusRigidity_of_splitAffine` proves the unchanged published
rigidity statement from that single local proposition. The forward implication
is the preceding reduction. The reverse implication is
`FppfLocallyTorusConjugate.torusRestriction_eq`. For uniqueness,
`TorusConjugates.difference_mem_center_of_isogeny` says that two conjugating
points have central difference, and the centre predicate gives the required
commutation after every scheme refinement.

The provenance is the imported simultaneous splitting theorem, actual
base-change conjugator transport, isogeny stability and the previously proved
descent and uniqueness implications. These are formal consequences of those
results; no new external source is used. The affine existence premise remains
an explicit proof obligation, so this reduction is conditional and does not
by itself finish the full rigidity task. All constructions preserve the
universe and apply to arbitrary base schemes, including nonreduced and empty
bases.
