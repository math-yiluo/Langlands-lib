# Parabolic conjugation is linear on actual vector layers

This internal construction for Task 7200 proves that actual conjugation by a
parabolic base point induces a linear automorphism on a root-weight vector
quotient. The point need not centralize the cocharacter. The base ring and
universe are arbitrary, and the comparison holds on every scheme test.
Rank-zero layers are included.

The inputs retain the geometric identifications needed by a consumer:

- `W : RootWeightData C`, an ambient inclusion `j : U ⟶ G` whose underlying
  morphism over the base is a monomorphism, and a cocharacter `χ` of `G`.
- The actual contracting subgroup `Dynamic.unipotent χ` is represented by
  `W.inclusion 0 ≫ j`.
- `G` is separated over the base, so the dynamic limit decomposition applies.
  The actual range of `W.inclusion d ≫ j` is normalized by
  `Dynamic.parabolic χ`.
- An action `a` of the multiplicative group on `W.groupScheme d`, together
  with its actual ambient `χ`-conjugation equation on every test. The actual
  `W.quotientMap d` intertwines `a` with `powerWeightAction` of exponent
  `N : ℕ`. The root-weight cocharacter-equivariance construction supplies
  this input in the realized-face application.
- A base point `p ∈ Dynamic.parabolic χ`, actual automorphisms `e` and `eK`
  of the consecutive represented terms, and
  `W.step d ≫ e.hom = eK.hom ≫ W.step d`. The action of `e` on every test
  has the ambient equation for conjugation by the constant pullback of `p`.
  Thus these are term automorphisms with a specified actual geometric
  meaning. No quotient linearity or quotient equivariance of `e` is assumed.
- For the linear equivalence and matrix conclusions, `0 < N`.

`quotientMap_eq_of_unipotent_conjugation` first proves that conjugation by
any point of the actual contracting subgroup is killed by the actual
vector quotient. Representability lifts that point to the first positive
term; cancellation of `j` and the positive-term commutator result reduce
the assertion to `quotientMap_eq_of_positive_conjugation`.

`quotientMap_parabolic_scalar` works on an arbitrary test scheme, even
before a chosen term automorphism is supplied. For a parabolic point `p`,
write `z = Dynamic.limit χ p` and `u = p*z⁻¹`. The existing limit theorems
put `z` in the actual dynamic centralizer and `u` in the actual contracting
subgroup. Normalization supplies a represented term point with ambient
image `z*x*z⁻¹`. Conjugation by `u` does not change the quotient image.
Since `z` commutes with every value of `χ`, its conjugation commutes with
the given term action. The assumed equivariance of the actual quotient
map then shows that conjugation by `p` commutes with the scalar action
after quotienting. There is no commutation assumption on `p` itself.

`conjugationQuotientIso` constructs the actual vector-group automorphism
from `e`, `eK`, and the compatible step equation by full fppf quotient
uniqueness. `conjugationQuotientIso_fac` proves
`quotientMap ≫ E.hom = e.hom ≫ quotientMap`.

The generic lemma
`FppfQuotientComparison.isEquivariant_of_fac_mod_kernel` transfers
equivariance modulo a full quotient kernel to the actual descended map.
It assumes that the quotient morphism is quasi-compact and uses local
flat surjective lifts of quotient points. It requires no global lift of
an arbitrary quotient point. In the root-weight application,
quasi-compactness follows from the affine coordinate descriptions of the
source, target and quotient morphism. Applying the preceding parabolic
calculation to these local lifts proves
`conjugationQuotientIso_isEquivariant`.

`conjugationQuotientIso_hasScalarWeight` derives the all-coefficient-algebra
scalar-weight identity of the actual quotient automorphism.
`parabolicLayerLinearEquiv` then constructs its linear equivalence over
each coefficient algebra, using the arbitrary-ring positive-weight
linearity theorem. Finally, `conjugationQuotientIso_eq_matrixHom` identifies
the original actual quotient morphism with the matrix morphism of its
base-ring matrix. As an equality of group-scheme morphisms, this comparison
applies to all scheme tests.

The provenance is internal. The proof combines the existing actual dynamic
limit decomposition and centralizer identity, the positive-term
commutator/kernel argument, full fppf quotient uniqueness and descent, and
arbitrary-ring scalar-weight rigidity. Construction of the supplied
geometric term automorphisms, different-torus comparisons and final finite
filtration descent remain consumer obligations.
