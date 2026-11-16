# Global rational formal maps and their atlas restrictions

This internal construction extends the integral map in `GlobalAtlasMorphism`
by rational scalars and transports actual two-sided quasi-isogenies to the
atlases of a supplied principal-open cover. It is derived from the existing
coefficient comparisons, integral formal Hom and tensor composition APIs.
It makes no additional original-literature assertion.

## Parameters and meaning

O and R are commutative rings with R an O-algebra. F is a field with an
O-algebra structure. Source, target and intermediate global formal O-module
laws have possibly different finite coordinate types in `Type`. A set s of
elements of R is supplied together with the equality `Ideal.span s = ⊤`;
both atlases use this same cover. `ofGlobalCover_opens_eq` records their
cover equality with both complete atlas types, allowing the heterogeneous
Hom module structures to elaborate without reducing the atlas definitions.
Test algebras have R's universe v.

Both rational Hom spaces are actual scalar extensions `F ⊗[O] Hom`.
The atlas Hom consists of compatible families of integral formal maps on
test charts before taking this tensor product. Consequently each rational
atlas map is a global finite tensor sum. This construction does not replace
it by the generally different space of all locally rational maps.

## Linear restriction and composition

`ofGlobalHomLinear s hs` packages the existing `ofGlobalHom` as an O-linear
map. The helpers `globalChartHom_add` and `globalChartHom_smul` first use
`ModuleLaw.Hom.mapLinear` to preserve addition and O-scalars in coefficient
extension, then distribute the source and target `globalChartIso`
compositions using the existing bilinearity laws. Extensionality on test
charts proves the two linear-map laws from those helpers.

`ofGlobalIso` applies the integral construction to both maps of a global
isomorphism. Preservation of composition and identity transports both inverse
equations; no new inverse is assumed.

`ofGlobalRationalHom s hs` is the F-linear scalar extension of
`ofGlobalHomLinear`. Its tensor formula sends `a ⊗ f` to
`a ⊗ ofGlobalHom f s hs`. The formula at a = 1 proves compatibility with
integral rationalization. Identity preservation follows from the integral
identity formula. Composition preservation follows by tensor induction in
both inputs: additivity reduces sums to their summands, and on pure tensors
the scalar product and the integral composition formula agree.

The module also supplies the composition ring on global rational
endomorphisms, using the existing associative, bilinear composition and
rational identity. Natural and integer casts are tensors of the respective
field casts with the integral identity. This is the global counterpart of
the existing atlas endomorphism ring. `ofGlobalRationalEnd` is the ring
homomorphism induced by rational restriction; its additive laws come from
F-linearity and its multiplicative and unit laws from the preceding formulas.

## The actual chart map

`onChart_ofGlobalRationalHom` identifies the evaluated rational map with the
following composite, in application order:

1. The rationalization of the source `globalChartIso.hom`.
2. The actual coefficient extension of the original rational map from R to A.
3. The rationalization of the target `globalChartIso.inv`.

This is an equality of formal tensor homomorphisms, not merely of point
functions. Its proof uses tensor induction. For sums, bilinearity distributes
the two fixed comparison maps. For a pure tensor, the integral chart map is
the defining conjugation and the extra field factors are both 1.

## Quasi-isogenies

The quasi-isogeny constructions additionally assume O is a domain and F is
its fraction field. `ofGlobalQuasiIsogeny` restricts both actual rational maps.
The proved composition and identity equations transport both inverse
equations into the atlas Hom. Its forward and inverse projections are the
corresponding `ofGlobalRationalHom` images.

The construction preserves identity, inverse, composition and rationalization
of integral isomorphisms. Equality is detected by the forward map using the
imported uniqueness of the rational inverse. Each resulting forward-map
equation is respectively identity preservation, definitional equality,
composition preservation or compatibility with integral rationalization.

`onChart_ofGlobalQuasiIsogeny` identifies its chart evaluation with the
coefficient-extended global quasi-isogeny between the actual source and target
chart comparisons. Extensionality on the forward map reduces the proof to
`onChart_ofGlobalRationalHom` followed by associativity to match the
parenthesization of the quasi-isogeny composites. The two-sided inverse is
already part of the constructed objects.

No injectivity, surjectivity, independence of covers, locally rational gluing,
full-order equivariance, height, framing, polarization, descent, levels or
representability is asserted here.
