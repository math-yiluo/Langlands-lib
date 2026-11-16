# Coefficient extension of rational formal atlas maps

This internal construction extends the published integral atlas base change
by rational scalars, and transports actual two-sided quasi-isogenies. It is
derived from integral formal coefficient extension and the existing tensor Hom
composition API. It makes no additional original-literature assertion.

## Parameters and meaning

O and R are commutative rings with R an O-algebra, and F is a field O-algebra.
The source, target and intermediate formal O-module atlases may have different
finite coordinate types in `Type`. Source and target have the same supplied
principal-open cover, with equality h. A coefficient algebra S is an object of
`CommAlgCat.{v} R`, where v is R's universe. The base-changed covers are the
images of the original covers under `algebraMap R S`; `baseOpens_eq S h`
identifies these image covers. This permits noninjective coefficient maps and
does not require a bijection of cover indices. The original base-change
construction selects a preimage generator for each image generator.

Rational Hom is the global tensor `F ⊗[O] Hom`, where integral Hom consists of
compatible actual formal maps on test charts. Coefficient extension in this
module retains that global finite tensor interpretation. It does not replace
rational Hom with all locally rational chart maps.

## Linear coefficient extension

`Hom.baseChangeLinear S` packages the existing integral `Hom.baseChange` as an
O-linear map. On a test chart its formula is the original formal chart map
between the actual source and target coefficient comparison isomorphisms.
The two linear-map laws distribute the fixed comparison maps using the existing
bilinearity of actual formal composition. Extensionality on charts gives the
integral atlas equalities.

`RationalHom.baseChange S` extends this O-linear map by F-scalars. Its pure
tensor formula sends `a ⊗ f` to `a ⊗ f.baseChange S`, and hence it agrees with
rationalization of integral formal maps. Identity preservation follows from
the integral identity formula. Tensor induction in both inputs proves
composition preservation: additivity handles sums, and on pure tensors the
integral composition formula and field multiplication coincide.

`RationalHom.baseChangeRingHom X S` packages these equations as a homomorphism
of rational endomorphism composition rings. Its additive laws follow from
F-linearity and its multiplicative and unit laws are the preceding formulas.

## The actual chart equation

`RationalHom.onChart_baseChange` states that evaluating the extended tensor
map is the following composite, in application order:

1. Rationalize the actual `baseSourceChartIso.hom`, which uses the original
   cover equality to identify the selected source chart.
2. Evaluate the original rational atlas map on `restrictTest S A`, at the
   target's selected original generator `Y.baseSource S b`.
3. Rationalize the target `baseChartIso.inv`.

This is equality in actual formal rational Hom. The proof uses tensor
induction. For sums it distributes the two fixed comparison maps. A pure tensor
reduces to the defining integral chart conjugation with two extra field factors
of 1. The generator choice and transported source index are precisely those
of the published integral base change.

## Quasi-isogenies

This section additionally assumes O is a domain and F is its fraction field.
`QuasiIsogeny.baseChange` applies rational base change to both original maps.
Identity and composition preservation transport the two actual inverse
equations. Its forward and inverse projections are the corresponding rational
base changes; no inverse is supplied as new input.

Base change preserves identity, inverse, composition and rationalization of
integral atlas isomorphisms. Forward-map extensionality, using the imported
uniqueness of the rational inverse, reduces these statements to the respective
rational Hom formulas. `QuasiIsogeny.onChart_baseChange` identifies chart
evaluation with the source comparison, the original chart quasi-isogeny and
the inverse target comparison. Its proof uses the rational Hom chart formula
and associativity to adjust the parenthesization.

No injectivity, surjectivity, independence of generator choices, coherence of
successive coefficient extensions, full-order equivariance, locally rational
gluing, heights, framing, polarizations, descent, levels or representability
is asserted here.
