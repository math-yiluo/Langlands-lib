# Complex splitting of the quadratic Deligne point functor

Author: Worker 57.

This module constructs a natural algebraic splitting of the quadratic model
`Complexification S = QuadraticAlgebra S (-1) 0` over every commutative
complex algebra `S`. It then gives a multiplicative natural isomorphism from
its unit groups to the product of two scalar unit groups. Norm is identified
with multiplication, and quadratic conjugation with interchange of the two
factors.

## Internal provenance and scope

This is a derived internal algebraic prerequisite for the Deligne-torus
construction. It starts with the actual quadratic algebras and units defined
in `Langlands.Shimura.Unitary.Deligne`, and uses Mathlib's
`QuadraticAlgebra.lift`, `Units.mapEquiv`, and `MulEquiv.prodUnits`.
The formulas and inverse identities are proved directly in this module; no
additional external-source claim or representability assumption is made.
The imported `tensorEquiv` supplies the previously constructed identification
with scalar extension of the complex numbers.

The declarations lie in `Langlands.Shimura.DeligneTorus`. The coefficient
algebras have arbitrary universes `u` and `v`; each bundled functor uses one
universe `u`. The algebra and unit equivalences require only `CommRing S`
and `Algebra ℂ S`. No field, domain, reducedness, nontriviality or
finite-generation assumption is imposed. The tensor version additionally
uses a real-algebra structure for forming the tensor product. The functor
isomorphism applies to all complex algebras and their algebra homomorphisms,
but this module does not yet construct an isomorphism of the pullback of the
real Deligne group scheme with a product of multiplicative group schemes.
That scheme comparison, smoothness, and the global arithmetic and PEL
constructions remain subsequent obligations.

## Explicit algebra equivalence

Write `i_S = algebraMap ℂ S Complex.I` and
`h_S = algebraMap ℂ S (1/2)`. The two elementary identities
`i_S * i_S = -1` and `h_S * 2 = 1` follow by applying the algebra map to the
corresponding complex identities. Private helpers record these facts.

`splitHom S` is the product of the two algebra homomorphisms obtained by
sending the quadratic generator to `i_S` and to `-i_S`.
`splitHom_apply` identifies its value on `a + bω` with
`(a + b*i_S, a - b*i_S)`.

`splitEquiv S` upgrades this homomorphism to an `S`-algebra equivalence by
the explicit inverse

`(x,y) ↦ h_S*(x+y) + (-(i_S*h_S)*(x-y))ω`.

Both inverse identities are proved componentwise as polynomial identities
using the two scalar relations above; they do not divide by an element of
`S`. `splitEquiv_apply` and `splitEquiv_symm_apply` expose these formulas.
`tensorSplitEquiv S` composes the inverse of the imported `tensorEquiv S`
with `splitEquiv S`, giving an `S`-algebra equivalence from
`S ⊗[ℝ] ℂ` to `S × S`.

`splitEquiv_star` says that the quadratic involution changes `(x,y)` to
`(y,x)`. This involution fixes the coefficient algebra; it is not complex
conjugation of coefficients in `S`. `splitEquiv_norm` identifies the
quadratic norm with the product of the two coordinates. The former proof
expands the involution, and the latter expands the norm and uses
`i_S² = -1`.

## Units and naturality

`splitPointsEquiv S` first applies `Units.mapEquiv` to the algebra
equivalence, then applies `MulEquiv.prodUnits`. Thus its domain is the
original `Points S`, with its original multiplication, and its target is
`Sˣ × Sˣ`. The `_fst` and `_snd` equations give the underlying scalar values
`a + b*i_S` and `a - b*i_S`. `splitPointsEquiv_norm` proves equality of
units between the existing `norm S z` and the product of these two units.
The proof uses injectivity of the coercion from units and `splitEquiv_norm`.

`splitEquiv_natural` states that for every complex-algebra homomorphism
`f : S →ₐ[ℂ] T`, splitting after the existing quadratic coefficient-change
map equals applying `f` to both split coordinates. Its proof uses the
explicit formulas and the fact that `f` preserves the scalar `i`.
`splitPointsEquiv_natural` lifts this equation to unit groups by applying
unit extensionality to each component.

`complexFunctor` is the existing quadratic-unit construction evaluated on
complex algebras: objects are `Points S`, and arrows are `Units.map` of the
existing quadratic `map`. `splitFunctor` sends `S` to `Sˣ × Sˣ` and every
algebra map to the product of its two induced maps on units. Both functors
have proved identity and composition laws.

Finally, `splitFunctorIso` has component `splitPointsEquiv S` converted to
an isomorphism in `GrpCat`. Its naturality square is precisely
`splitPointsEquiv_natural`. This is a natural multiplicative equivalence on
all test algebras, with an explicit inverse at each test algebra.
