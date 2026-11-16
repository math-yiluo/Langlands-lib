# Natural rational comparison of successive coefficient extensions

This module derives naturality of the existing actual `baseCompIso` internally
from the original atlas-map transition square and the established chart
coordinate formulas for coefficient extension. No new literature assertion
is made. The original principal-open covers agree, coordinate types are
finite and may differ, and coefficient tests have the base-ring universe.

`baseCompIterSource_sourceChart` proves that the successive choices of an
original preimage chart agree under equality of original covers, using the
existing preimage-choice lemma twice.

`Hom.baseComp_natural` proves that the target comparison after twice extending
an integral map equals directly extending the map after the source comparison.
The proof compares actual chart coordinate series: the target comparison is
the original transition from the successively selected generator to the
directly selected one; the original map's transition square commutes; the
source comparison gives its original transition with transported indices.

`Hom.baseComp_inv_natural` proves the reverse comparison square using this
forward equation, associativity and the two actual inverse equations of
`baseCompIso`.

Let `O` be a commutative ring, `R` a commutative `O`-algebra, and `F` a field
`O`-algebra. For successive coefficient tests `S` over `R` and `T` over `S`,
the directly extended atlas uses `restrictTest S T` and its composite
`O`-algebra structure. `RationalHom.baseComp_natural` and
`baseComp_inv_natural` prove the same squares in the global tensor
`F ⊗[O] BasicAtlas.Hom`, with rationalizations of the actual integral
comparison maps. Tensor induction handles sums by additivity and pure tensors
by the explicit tensor composition and extension formulas and the integral
equations. No injectivity of rationalization or detection by chart evaluation
is assumed.

With `IsDomain O` and `IsFractionRing O F`, `baseCompQuasiIsogeny X S T`
rationalizes the existing actual `X.baseCompIso S T`, retaining both comparison
maps and their inverse equations. The `hom` and `inv` projection lemmas
identify the rationalizations of `baseCompHom` and `baseCompInv`.
`QuasiIsogeny.baseComp_natural` and `baseComp_inv_natural` prove the
corresponding two squares for quasi-isogenies: the forward maps satisfy the
rational equations, and uniqueness of a two-sided inverse proves equality of
the entire quasi-isogenies.

These laws retain the existing selected preimage charts and the specified
actual comparison. This module does not assert independence of arbitrary
comparisons, coherence for three successive extensions or identity units,
supplied-target scalar transport, full-order equivariance, local rational
gluing, heights, framing, polarization, descent, levels or representability.
