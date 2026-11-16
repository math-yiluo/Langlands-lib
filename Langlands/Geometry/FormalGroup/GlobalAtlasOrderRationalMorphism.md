# Global full-order rational maps and their atlas restrictions

This internal construction restricts global rational formal maps commuting with
an actual order action to atlases induced on a supplied principal-open cover.
It is derived from the existing global rational restriction, actual order-linear
chart comparisons and full-order rational centralizers. It makes no additional
original-literature assertion.

## Parameters and meaning

O and R are commutative rings, R is an O-algebra, D is a possibly noncommutative
ring with an O-algebra structure, and F is a field O-algebra. The global formal
O-module laws have possibly different finite coordinate types in `Type`. Their
actual order actions E and E' act through formal endomorphisms. A set s of
elements of R is supplied with `Ideal.span s = ⊤`; both induced atlases use this
cover and the equality `ofGlobalCover_opens_eq M N s hs`. Test algebras have
R's universe v.

The source full-order rational Hom is the centralizer inside the actual global
tensor `F ⊗[O] ModuleLaw.Hom M N`. The target full-order rational Hom is the
chartwise centralizer inside the global tensor of compatible integral atlas
maps. Neither is defined as the tensor product of integral D-linear maps, and
no equality with such a tensor product is asserted. In particular this module
retains global finite tensor sums, without introducing locally rational gluing.

## Restriction and its chart formula

`ofGlobalOrderRationalHom_mem` proves that ambient global rational restriction
lands in the full-order atlas centralizer. On each test chart, form the actual
full-order rational composite, in application order:

1. Rationalize the source `globalOrderChartIso.hom`.
2. Apply coefficient extension from R to the test algebra A to the given map.
3. Rationalize the target `globalOrderChartIso.inv`.

Each factor is an order-equivariant formal rational map, so the composite
commutes with every element of D. The existing ambient chart equation
`onChart_ofGlobalRationalHom` transports that commutation equation to the
restricted atlas map. The proof uses equality congruences on composition,
retaining the precise formal Hom types.

`ofGlobalOrderRationalHom s hs` is the resulting F-linear map between the two
centralizers. Its underlying value is exactly `ofGlobalRationalHom s hs f.val`.
Additivity and F-scalar preservation follow from the ambient linear map by
subtype extensionality. Restriction agrees with rationalization of the existing
integral `ofGlobalOrderHom`, preserves identity and composition, and therefore
gives the ring homomorphism `ofGlobalOrderRationalEnd` on full-order rational
endomorphisms. Each compatibility proof forgets the commutation proof and
applies the corresponding ambient restriction equation.

`onChart_ofGlobalOrderRationalHom` states the preceding three-factor formula
inside the actual coordinate full-order rational centralizer. Its proof is
subtype extensionality applied to the ambient chart equation; this is equality
of formal rational maps, rather than only of point functions.

## Quasi-isogenies

The quasi-isogeny section additionally assumes O is a domain and F is its
fraction field. `ofGlobalOrderQuasiIsogeny` restricts the two maps of an actual
global full-order quasi-isogeny. Both inverse equations follow by forgetting
the order, using the existing ambient global-to-atlas quasi-isogeny, and
applying subtype extensionality. The forward and inverse projections are the
two full-order rational restrictions. Forgetting the order gives exactly
`ofGlobalQuasiIsogeny f.toModuleQuasiIsogeny s hs`.

The construction preserves identity, inverse, composition and rationalization
of actual integral order-linear isomorphisms. The imported uniqueness of the
rational inverse reduces each equality to its forward-map equation. These are
respectively identity preservation, definitional equality, composition
preservation and integral rationalization compatibility.

`onChart_ofGlobalOrderQuasiIsogeny` identifies chart evaluation with the source
order-linear chart comparison, the coefficient-extended global quasi-isogeny,
and the inverse target comparison, in that order. Forward-map extensionality
reduces the proof to the rational Hom chart equation and associativity.

No injectivity, surjectivity, independence of covers, locally rational gluing,
height, framing, polarization, descent, levels or representability is asserted.
