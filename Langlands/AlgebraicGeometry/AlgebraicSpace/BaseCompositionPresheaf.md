# Composing the base of a relative presheaf

Author: Worker 109.

This internal construction composes the base of an actual relative presheaf and
compares its point fibres. It is derived from the published total-presheaf and
fibre-presheaf constructions in `OriginalBaseTransport`; no literature theorem
is asserted as proved by this module.

For schemes `S,T : Scheme.{u}`, a morphism `g : S ⟶ T` and a presheaf `F` on
schemes over `S`, `BaseComposition.presheaf g F` takes a test `V` over `T` to
pairs `(s,x)` where `s : V.left ⟶ S`, `s ≫ g = V.hom`, and `x` is a section of
`F` on `V.left` equipped with `s`. Restriction uses the underlying scheme map
and restricts `x` over `S`. The existing `fiberPresheaf` of `totalToBase F`
composed with the Yoneda image of `g` supplies the functor laws.

`map g f` applies a natural transformation to `x` and keeps `s`.
`presheafFunctor` proves preservation of identities and composition.
`liftSection g F U` sends a section on a test `U/S` to `(U.hom,x)` on that same
test viewed over `T`. It is injective and commutes with `map`.

For any `f : F ⟶ G`, test `U/S` and section `y` of `G` on `U`, `fibreEquiv`
identifies the original fibre `{x // f(x) = y}` with the fibre of the composed
map above `liftSection g G U y`. Equality to that target first identifies the
source's structure map with `U.hom`. The remaining equality is precisely
`f(x) = y`, proving surjectivity of `fibreMap`; injectivity follows from
injectivity of `liftSection`. `card_fibre` gives equality of the two natural
cardinals, without finiteness assumptions.

The result uses all schemes as tests and values in `Type (u+1)` at arbitrary
`u`. It does not yet construct an fppf sheaf or an algebraic space over `T`,
nor transport geometric properties. Those are additional obligations for the
arithmetic application. The unconditional adelic smooth-openness target
remains unchanged and is not established here.
