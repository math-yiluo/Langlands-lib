# Bilinearity of the finite Weil pairing along an actual homomorphism

This internal unit proves bilinearity of the existing
`finiteWeilAlongHomValue` and packages the same pairing as
`finiteWeilAlongHomBilinearMap`. Its inputs are exactly those of
`FiniteWeilAlongHom`: a quasi-separated base, the actual abelian
scheme, its chosen dual and dual geometry, the seven explicit
tensor/Picard constructor propositions, an actual inverse Poincaré
bundle with evaluation, and an actual homomorphism `lam` to that
constructed dual abelian scheme.

The homomorphism need not be a polarization. The result therefore
applies to every `lam` satisfying `IsPolarization`, without needing
ampleness or isogeny hypotheses for bilinearity. Every natural
`n`, including zero, and every test scheme over the base is included.
The zero case concerns a multiplication kernel and makes no
finiteness assertion.

## Actual torsion restrictions preserve the group law

The reusable helper
`Langlands.GroupScheme.Tate.kernelLevelMapPointsAddHom` proves
that postcomposition with the actual `kernelLevelMap f n` is
additive on test-scheme points, using additive notation for their
group law. It works for any homomorphism of commutative group
objects in `Over S`.

The proof applies the injective additive equivalence
`kernelLevelEquiv` at the target. The existing
`kernelLevelEquiv_map` identifies the resulting map with the
published additive `levelMap`. Identity and addition then follow
from those two additive maps. The lemmas `kernelLevelMap_comp_one`
and `kernelLevelMap_comp_mul` express the same facts in the
multiplicative notation of group-scheme points. Thus the point
map is the existing scheme morphism, rather than a replacement
map specified by abstract group data.

## Bilinearity of the constructed pairing

`finiteWeilAlongHomValue_one_right` and
`finiteWeilAlongHomValue_mul_right` unfold the pullback definition,
use these actual torsion-map laws, and apply the corresponding
published right-variable laws of `finiteWeilValue`.

`finiteWeilAlongHomBilinearMap` is a curried additive homomorphism
from two copies of the additive group of actual `A[n](T)` points
to the additive notation for actual `μ_n(T)`. Its evaluation is
definitionally the existing `finiteWeilAlongHomValue`.
The second-variable laws are the preceding results; the
first-variable laws are those of the already constructed
`finiteWeilAlongHomValueHom`.

The theorem `finiteWeilAlongHomBilinearMap_apply` identifies this
value with evaluation of the original product-scheme morphism
`finiteWeilAlongHomPairing` on every pair of points. The final
two lemmas transfer the second-variable identity and multiplication
laws to that same scheme morphism. Throughout, the formula is

```text
e_n^lam(x,y) = e_n(x,lam[n](y)) = beta(lam[n](y))(x).
```

No arbitrary pairing, torsion map or bilinearity proof is supplied
as an input. This is an internal consequence of the published
point equivalences, the actual torsion map, and the bilinearity of
the Poincaré-derived finite Weil pairing.

The unit proves no alternation, Cartier perfectness,
nondegeneracy, transition compatibility, dual-homomorphism
functoriality or inverse-limit pairing. It makes no assertion of
integral perfectness for arbitrary nonprincipal polarizations.
