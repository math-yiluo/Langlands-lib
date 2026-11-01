# Renard II.1.3: products of t.d. spaces, tensor products and Fubini

Author: Worker 1219. This file gives closed proposition definitions for the
assertions of David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, subsection II.1.3 "Produit
tensoriel de distributions", printed page 32 / PDF page 38. The whole
subsection is on that page. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The
recalled II.1.1 and II.1.2 material is on printed pages 30–31 / PDF pages
36–37. These are statements only. They prove none of the new targets, and
they do not construct a tensor product or an inverse isomorphism.

## Source-to-declaration correspondence

The source sentences of II.1.3, in order, correspond to these
declarations in the namespace
`Langlands.HarmonicAnalysis.Distribution.TensorProductStatements`.

| Source (printed p.32) | Declaration |
| --- | --- |
| "munissons X×Y de la topologie produit, qui en fait un espace t.d." | `ProductLocallyProfinite` |
| "les parties de la forme U×V, où U (resp. V) est un ouvert compact de X (resp. de Y) forment une base de voisinages de X×Y" | `CompactOpenRectangleBasis` |
| "écrire tout ouvert compact de X×Y comme réunion disjointe finie d'ouverts compacts de la forme U×V" | `CompactOpenRectanglePartition` |
| "Toute fonction dans D(X×Y) est donc une combinaison linéaire de fonctions caractéristiques d'ouverts compacts disjoints de la forme U×V" | `RectangleIndicatorDecomposition` |
| "D(X×Y) ≃ D(X)⊗D(Y), l'isomorphisme étant donné par (f⊗g)(x,y) = f(x)g(y)" | `TensorLinearMapBijective` |
| "T1⊗T2 est défini sur D(X×Y) par ⟨T1⊗T2, f⊗g⟩ = ⟨T1,f⟩⟨T2,g⟩" | `TensorExistsUnique` |
| "les formules de Fubini sont valables : pour tout f ∈ D(X×Y), …" | `Fubini` |
| Proposition: "Supp(T1⊗T2) = Supp(T1)×Supp(T2)" | `SupportTensor` |
| "En particulier, le produit tensoriel de deux distributions à support compact est à support compact" | `CompactSupportTensor` |

`Assertions.{uX, uY}` is exactly the conjunction of these nine
propositions at the same two universe parameters.

## Spaces, carriers and maps

Every target quantifies arbitrary `X : Type uX` and `Y : Type uY` with
independent universes and their supplied topologies. `X × Y` carries
Mathlib's product topology and lives in `Type (max uX uY)`.

`ProductLocallyProfinite` uses the Library's literal source predicate
`Langlands.Topology.IsLocallyProfinite`: Hausdorff with a compact open
neighborhood basis at every point. This is the II.1.1 definition of a t.d.
space. Its hypotheses are the two t.d. conditions and its conclusion is the
same predicate on `X × Y`. The other eight targets state the t.d.
hypothesis on each factor as `T2Space`, `LocallyCompactSpace` and
`TotallyDisconnectedSpace` instance binders. The public theorem
`Langlands.Topology.isLocallyProfinite_iff_mathlib` proves that these three
classes are equivalent to `IsLocallyProfinite`. The required classes on
`X × Y` come from Mathlib's product instances. The hypotheses are only
these classes, so empty spaces are included. No compactness,
nonemptiness, metrizability, countability, group structure or measurable
structure is assumed.

`SchwartzBruhat X` is the published complex submodule of locally constant,
compactly supported functions `X → ℂ`, that is Renard's D(X).
`Distribution X` is its full complex algebraic linear dual, Renard's
D′(X), with no topology and no continuity condition. Every tensor product
is the algebraic tensor product over ℂ. The maps are all imported from the
public Library by name:

- `Langlands.Hecke.TestFunction.characteristic hs hc` is the actual
  characteristic function of a compact clopen set `s`. It takes the value 1
  on `s` and 0 off `s`.
- `SchwartzBruhat.tensor f g` is the external-product test with the
  original formula `(x, y) ↦ f x * g y`.
- `SchwartzBruhat.tensorLinearMap` is the lift of this bilinear external
  product to `SchwartzBruhat X ⊗[ℂ] SchwartzBruhat Y →ₗ[ℂ]
  SchwartzBruhat (X × Y)`. It sends `f ⊗ₜ g` to `SchwartzBruhat.tensor f g`.
- `Distribution.partialApplySnd S` sends a product test f to the test
  `x ↦ S (y ↦ f (x, y))` on X. `Distribution.partialApplyFst T` sends f to
  `y ↦ T (x ↦ f (x, y))` on Y.
- `Distribution.tensor T S` is the published distribution product, defined
  as `T ∘ partialApplySnd S`.
- `Distribution.support D` is the actual topological support: the
  complement of the union of the open sets U with `restrictOpen hU D = 0`.
  This is Renard's definition in II.1.2, printed p.31 / PDF p.37.
  `Distribution.compactlySupported` is the published submodule of
  distributions whose topological support is compact, Renard's E′(X).

The older closed-annihilator predicate `supportedOn` is not used. Renard's
pairing notation `⟨T, f⟩ = ∫_X f dT` is notation for the evaluation `T f`.
The Fubini integrals are therefore stated as evaluations.

## The geometric and test-function targets

`CompactOpenRectangleBasis` states that the sets `U ×ˢ V` with U open
compact in X and V open compact in Y form a topological basis of `X × Y`
(Mathlib's `IsTopologicalBasis`). "Base de voisinages de X×Y" is read as
a basis of the product topology. The source states this fact as the input
of the rectangle partition, so it is kept as a target.

`CompactOpenRectanglePartition` takes every open compact `K : Set (X × Y)`.
It asserts a natural number n and families `U : Fin n → Set X` and
`V : Fin n → Set Y` with three properties. Each `U i` and each `V i` is
open and compact. Distinct indices give disjoint product sets
`U i ×ˢ V i`. The union over `i` of `U i ×ˢ V i` is exactly K. The case
n = 0 is allowed, so `K = ∅` and empty products are included. Empty
rectangles are also allowed, matching the source.

`RectangleIndicatorDecomposition` takes every actual
`f : SchwartzBruhat (X × Y)`. It asserts finite families `U i`, `V i` with
proofs that they are clopen and compact, and complex coefficients `c i`.
Distinct indices give disjoint rectangles. The proposition then asserts
two equalities in `SchwartzBruhat (X × Y)`:

1. `f = Σ i, c i • characteristic (U i ×ˢ V i)`, using the characteristic
   function of the actual product set, whose clopenness and compactness
   proofs are `IsClopen.prod` and `IsCompact.prod`.
2. `f = Σ i, c i • SchwartzBruhat.tensor (characteristic (U i))
   (characteristic (V i))`, with the same families and coefficients.

The first is the source's sentence. The second records each rectangle
indicator as the external product of the coordinate indicators, using the
original pointwise formula. This is the form used for the isomorphism. The
coordinate sets are written as compact clopen because that is the domain of
`characteristic`. In a Hausdorff space a compact open set is closed, so this
is exactly Renard's compact-open condition. Again n = 0 is allowed. This
covers zero tests and empty spaces. No tensor inverse or formal rectangle
expansion is supplied.

The source also recalls "d'après la remarque II.1.2" that every
f in D(X×Y) is a linear combination of characteristic functions of
disjoint compact open subsets of X×Y. This is not a new II.1.3 assertion.
It is the II.1.2 lemma applied to the t.d. space X×Y. The Library states
it as `Langlands.HarmonicAnalysis.TestFunctionDistributionStatements.DisjointIndicatorDecomposition`
at universe `max uX uY`. That lemma decomposes into compact open subsets of
the ambient space, not into rectangles, so it is not a substitute for the
two rectangle targets above. It is not restated here.

`TensorLinearMapBijective` states that the published canonical map
`SchwartzBruhat.tensorLinearMap` is bijective. This expresses the source's
linear isomorphism D(X)⊗D(Y) ≃ D(X×Y) through the map given by the
source's formula. No inverse map or `LinearEquiv` is chosen. A later proof
may build one from this bijectivity.

## The distribution targets

`TensorExistsUnique` takes arbitrary `T : Distribution X` and
`S : Distribution Y`. It asserts two things:

- existence: `Distribution.tensor T S (SchwartzBruhat.tensor f g) =
  T f * S g` for all tests f on X and g on Y;
- uniqueness: every `D : Distribution (X × Y)` with the same values on all
  external products equals `Distribution.tensor T S`.

Renard defines T1⊗T2 by its values on the f⊗g. The definition is sound
only because these values determine a unique algebraic functional on
D(X×Y). This proposition states exactly that, for the actual published
product. The published construction already proves the existence formula
as `Distribution.tensor_apply_tensor`. It is restated so that the aggregate
contains the entire source definition. Uniqueness is new and is not assumed as a hypothesis.

`Fubini` takes T, S and every test `f : SchwartzBruhat (X × Y)`, not only
external products. It asserts
`Distribution.tensor T S f = T (Distribution.partialApplySnd S f)` and
`Distribution.tensor T S f = S (Distribution.partialApplyFst T f)`. These
are Renard's two iterated integrals
∫_X (∫_Y f(x,y) dT2(y)) dT1(x) and ∫_Y (∫_X f(x,y) dT1(x)) dT2(y). The
inner integrals are the actual published partial-evaluation tests. Because
`Distribution.tensor` is defined by evaluating in Y first, the first
equality holds by definition. The second is the substantive Fubini
exchange. Both are kept because the source states both.

`SupportTensor` states the set equality
`Distribution.support (Distribution.tensor T S) =
Distribution.support T ×ˢ Distribution.support S` for every T and S.
`CompactSupportTensor` states two things for every T and S. First, if
`support T` and `support S` are compact, then `support (tensor T S)` is
compact. Second, the same implication holds as membership in
`Distribution.compactlySupported`. Membership is definitionally
compactness of the support, so the second part specializes the first to
the existing E′ submodule. The source gets compactness "immédiatement" from
the support formula, as a product of compact sets. It is still stated
separately, as the source does.

Zero distributions are included. For example, `Distribution.support 0` is
empty, so the support formula specializes to `∅ = ∅ ×ˢ support S` when
T = 0. If X is empty, then `X × Y` is empty. The test and distribution
spaces on X and on `X × Y` are then zero, and `support T` and the support
of the product are both empty. The support formula then reads `∅ = ∅ ×ˢ
support S`. The case of empty Y is symmetric. These cases are instances of
the targets, not exclusions.

## Scope and provenance

All nine propositions are source assertions of II.1.3. Their hypotheses are
only the t.d. structures of X and Y, and all conclusions are new targets.
Some formulation choices are derived: the three-class form of t.d.; the
`Fin n` indexing of finite families; clopen coordinate sets in the
characteristic functions; the extra external-product form of each
rectangle indicator; bijectivity of the canonical map instead of a chosen
equivalence; and the existence-and-uniqueness reading of "est défini par".

Renard's proofs are not formalized here. Those are the topology argument,
the disjoint refinement of II.1.1 (ii), "les intégrales se ramènent à des
sommes finies", and the proof of the support proposition. The support
proof restricts T1⊗T2 to an open rectangle U×V and identifies the result
with T1,U⊗T2,V. That identification is an intermediate step of the proof,
not a separate stated result. This unit leaves it to the support-product
proof, which may state and prove it over `Distribution.restrictOpen`.
The geometric and tensor-map proofs, the uniqueness and Fubini proofs and
the support-product proofs are left to later proof tasks over these exact
public declarations. The vector-valued II.1.2 maps (II.1.2.3)–(II.1.2.4)
belong to a separate unit and are not stated here.
