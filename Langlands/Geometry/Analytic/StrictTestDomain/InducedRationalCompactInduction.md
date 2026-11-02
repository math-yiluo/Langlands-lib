# Compact induction of full sections on the induced rational spectrum

Author: Worker 13.

This module constructs a natural isomorphism of smooth representation functors
between all compactly supported locally constant functions on the actual
induced rational spectrum and compact induction of all local-spectrum
sections. The coefficient action is the original diagonal action throughout.
The main declaration is `compactInductionNatIso` in
`Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction.OpenSubgroupTransport.CompactSections`.

This is an internal construction from the published modules
`InducedRationalCompactSupport` and `Representation.Induction.OpenAdjunction`.
It does not assert a new original-literature theorem. Its purpose is to connect
the constructed geometric section module to the existing representation
functors, including their coefficient maps.

## Inputs, universes and conventions

The field `K : Type u` is complete, normed and ultrametric, `P` is a presented
strict affinoid algebra over `K`, and `G : Type v` is a topological group with a
rational spectral action `ρ` on `P`. Let `X : ρ.OpenSubgroupTransport`, with
open subgroup `H = X.subgroup.toSubgroup`. The space `X.LocalSpectrum` is the
actual Banach spectrum of the rational quotient algebra in `X`; it is compact
and Hausdorff by the imported spectrum results. The space
`X.InducedSpectrum = G ×_H X.LocalSpectrum` is the constructed balanced
quotient with its continuous left `G` action. Its representatives obey
`[a h,x] = [a,h x]`, and its component map takes `[a,x]` to `aH` in `G/H`.

The ring `R : Type r` is any commutative ring. A coefficient object
`M : SmoothRep.{r,v,w} R G` has its module carrier in independent universe `w`.
There is no topology on that carrier and no dimension or finiteness condition.
The local section carrier has universe `max u w`; both full induced-spectrum
compact sections and the compactly induced carrier have universe `max u v w`.
No local compactness or total disconnectedness assumption on `G` is added.
No stable-neighbourhood hypothesis for a sheaf category is needed here.

The imported compact-induction convention is covariance
`F(hg) = σ(h) F(g)` and right translation `(a.F)(g) = F(g a)`.
Its quotient support is in `H\\G`, represented by the right cosets `H g`.
The geometric component labels are the left cosets `aH`. Inversion relates
these conventions; no normality of `H` is assumed.

## Local sections and coefficient functors

`localRepresentation X M` is the full module of locally constant functions
`X.LocalSpectrum → M`, with action

```
(h.s)(x) = M(h) (s(h⁻¹.x)).
```

`localRepresentation_isSmooth` first restricts the smooth coefficient
representation to `H`, then uses the existing compact-space diagonal-action
smoothness theorem. It proves smoothness of every original local section;
it does not replace the carrier by a smooth-vector submodule.

`localCoefficientFunctor` bundles these representations and sends each
coefficient intertwiner `b : M → N` to pointwise composition `s ↦ b ∘ s`.
The coefficient functor identities hold pointwise.
`compactInducedCoefficientFunctor` applies the existing
`compactInductionFunctor H` after forgetting the smoothness predicate on
these local representations. Using this functor directly keeps the independent
carrier universes; it does not impose an equality of the local carrier universe
with a universe already containing `v`.

## Forward coordinates and their obligations

`inverseComponent` is the map `G/H → H\\G` sending `aH` to `H a⁻¹`.
The quotient relation and closure of `H` under inversion prove it is well
defined. `inverseComponent_mk` records its value on representatives.

For `f : Functions X`, the twisted chart restriction is
`inductionCoordinate X M f`, with evaluation formula

```
F(g)(x) = M(g) (f([g⁻¹,x])).
```

It is locally constant in `x`: restriction along the continuous chart
`X.inducedChart g⁻¹` preserves local constancy, and composition with the
linear coefficient map preserves it as well.
`inductionCoordinate_covariant` proves `F(hg) = σ(h)F(g)` using the
representation multiplication law and the balanced chart relation.
`inductionCoordinate_action` proves that the full geometric diagonal action
on `f` corresponds to right translation of `F`.

`finite_quotientSupport_inductionCoordinate` bounds the quotient support of
`F` by the image under `inverseComponent` of the finite component support of
`f`. If `F(g)` is a nonzero local section, some `x` has
`f([g⁻¹,x]) ≠ 0`; the component `g⁻¹H` therefore occurs in that finite set.
This proves finite, hence compact, quotient support.

`toCompactInduction` chooses an open subgroup fixing the entire original
compact section from the proved smoothness of `smoothRepresentation X M`.
The action formula then gives a uniform open right stabilizer for `F`.
Together with covariance and finite quotient support, these are all intrinsic
fields of the existing `CompactFunctions` constructor.
`toCompactInduction_eval` states the displayed coordinate formula.
`toCompactInductionIntertwiner` proves linearity pointwise and full
`G` equivariance by `inductionCoordinate_action`.

`toCompactInduction_injective` evaluates at `a⁻¹` and applies `M(a)` to
recover `f([a,x])`. Quotient induction covers every point of the actual
balanced quotient, so the coordinate map is injective on the full section
module.

## Inverse construction and inverse laws

`localChartExtension_apply_of_not_mem` records that local-chart zero extension
vanishes outside its chart. `toCompactInduction_localChartExtension` proves
that zero extension from the unit chart becomes the existing
`unitFunction H ... s`. For `g ∈ H`, the balanced chart relation and local
extension evaluation give the covariance value `σ(g)s`. For `g ∉ H`, the
point `[g⁻¹,x]` is outside the unit chart, so the value is zero.

`unitExtension X M` equips the existing unit-chart extension linear map with
its subgroup equivariance. The proof applies the injective forward coordinate
map and reduces to the equivariance of the existing compact-induction
`unitMap`. It therefore retains the original coefficient and spatial actions.

`fromCompactInductionIntertwiner` is the existing `cosetSum` applied to this
subgroup intertwiner. Explicitly it sends `F` to the finite sum

```
∑_{H g} g⁻¹ . unitExtension(F(g)).
```

The imported construction proves representative independence, finiteness,
linearity and full `G` equivariance of this sum.
`toCompactInduction_unitExtension` identifies the restricted forward map
composed with unit extension with `unitMap`.
`to_fromCompactInduction` then uses naturality of `cosetSum` in its target
and `cosetSum_unitMap` to prove that the forward map after this inverse is
identity. `from_toCompactInduction` follows by injectivity of the forward map.
These arguments prove both inverse laws without an additional continuity
assumption or an assumed equivalence.

`fromCompactInduction_eval` recovers the explicit inverse formula

```
f([a,x]) = M(a) (F(a⁻¹)(x)).
```

Its proof applies the right inverse law at `a⁻¹` and cancels the inverse
coefficient action. The inverse is already a well-defined compactly supported
locally constant function by its coset-sum construction.

## Natural isomorphism and scope

`compactInductionIso X M` bundles the two intertwiners and proved inverse laws
as an isomorphism of smooth representations.
`compactInductionNatIso X` assembles these into

```
coefficientFunctor X ≅ compactInducedCoefficientFunctor X.
```

Its naturality proof evaluates at `g,x` and uses the original coefficient
intertwiner relation `b(M(g)m) = N(g)(b(m))`. Consequently the inverse maps are
also natural, as follows from the constructed natural isomorphism.

The endpoints are full degree-zero function modules on the actual induced
rational spectrum and its actual local rational quotient spectrum. This unit
does not construct an analytic or etale sheaf comparison, identify higher
cohomology with compact induction, construct a Godement comparison, or
specialize arithmetic towers or Harris's particular groups and coefficients.
Those remain separate construction and theorem obligations of the wider task.
