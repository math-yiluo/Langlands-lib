# The scalar algebra of rational formal endomorphisms

Let `M` be an actual finite-coordinate formal `O`-module over a commutative
`O`-algebra and let `F` be a field over `O`. This module equips the existing
composition ring on `ModuleLaw.RationalHom F M M = F ⊗[O] Hom M M` with
its `F`-algebra structure. Composition is bilinear over `F`. The scalar
`a` acts as the endomorphism `a • id M`.

The map `ofHomEnd` is the ring homomorphism sending an actual integral formal
endomorphism `f` to `1 ⊗ f`. The map `mapEnd` is the `F`-algebra homomorphism
given by the existing extension of coefficients on the whole tensor product.
Their laws follow from the integral identity and composition equations and
the corresponding tensor equations for coefficient extension.

This internal algebra structure is used to extend a formal action of the
local division order to its rational division algebra in the construction
associated with Drinfel'd, *Coverings of p-adic symmetric regions* (1976),
§2 A, printed p. 109.
