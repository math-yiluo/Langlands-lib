# Reduction of formal O-modules on nilpotent coefficient algebras

Let O → R be a homomorphism of commutative rings, π ∈ R, and A an
object of `Nilp R π`. Each coefficient R-algebra is given its canonical
structural O-algebra, as in `NilpotentAlgebras`. `Nilp.quotientO` is the
actual quotient homomorphism A → A/(π) regarded as an O-algebra map.
`scalarMap` and `reducedScalarMap` likewise regard a Nilp morphism and
its induced quotient map as O-algebra maps. `quotientO_natural` proves
that their square commutes; the image of π under `quotientO` is zero.
These are restrictions of the maps constructed in `NilpotentReduction`.

For a finite-coordinate formal O-module M over A, `ModuleLaw.reduction`
changes every group-law and scalar-action coefficient along this actual
quotient. It is a formal O-module over A/(π), with the inherited natural
tangent action. The corresponding `Hom.reduction` and `Iso.reduction`
reduce actual integral maps and isomorphisms. Identity and composition
of integral maps are preserved.

`RationalHom.reduction` is an F-linear map on the actual tensor product
F ⊗_O Hom and preserves identity and composition. On pure tensors it
sends a ⊗ f to a ⊗ (the reduction of f). For O a domain and F its fraction
field, `QuasiIsogeny.reduction` reduces both rational maps and preserves
their two inverse equations. It preserves identity, inverse, composition
and the quasi-isogeny associated with an integral isomorphism. These
claims follow by specializing the established coefficient-extension laws.

For a Nilp morphism f : A → B, `reductionBaseChangeIso` is the canonical
isomorphism between reducing M after base change to B and changing the
base of its reduction along A/(π) → B/(π). It has identity coordinates
and is constructed by applying `mapSquareIso` to the actual commutative
quotient square. Its naturality is proved for integral formal maps,
rational Hom and quasi-isogenies. In particular these comparisons are
compatible with a rigidifying quasi-isogeny, as required for later moduli
constructions.

This is derived algebraic infrastructure for the reductions in the
triples defining Drinfeld's G(B), *Coverings of p-adic Symmetric Regions*
(1976), §2 A, printed p.109. It uses the previously constructed actual
principal-ideal quotients and formal coefficient maps, without choosing
a nilpotence exponent. It concerns finite-coordinate presentations and
makes no rigidity, locally glued formal-group, height, special-module
or representability assertion.
