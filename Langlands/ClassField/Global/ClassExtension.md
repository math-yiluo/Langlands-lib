# Relative idele-class extensions indexed by actual second cohomology classes

This module assigns an actual topological group extension of `E ≃ₐ[K] E` by
the actual idele class group `C_E = NumberField.IdeleClassGroup (𝓞 E) E` to
every class `x` in `relativeIdeleClassCohomology K E 2`. It also proves that
the result does not depend on the chosen representative, up to a continuous
equivalence over both ends. All declarations are in
`Langlands.ClassField.Global` or in its namespaces `RelativeIdeleCocycle` and
`ClassExtension`.

## Setting

The field parameters are `K : Type u` and `E : Type v`, in independent
universes, with `[Field K] [Field E] [NumberField E] [Algebra K E]`. The
acting group `E ≃ₐ[K] E` and the coefficient group `C_E` both lie in
`Type v`. As in the published `Langlands.ClassField.Global.Cocycle` and
`Langlands.ClassField.Global.Cohomology`, the module installs the published
arithmetic action `relativeIdeleClassAction K E` and the published discrete
topology `relativeGaloisTopology K E` as local instances. It accepts no other
action or topology. Outside the module they can be installed with
`letI := relativeIdeleClassAction K E` and `letI := relativeGaloisTopology K E`.
`C_E` keeps Mathlib's quotient topology.

## Converse cochain theorem for idele-class cocycles

In `RelativeIdeleCocycle`, `exists_cochain_of_cohomologyClass_eq` assumes
normalized idele-class cocycles `c, d` with
`c.cohomologyClass = d.cohomologyClass` in the actual cohomology group. It
gives `b : (E ≃ₐ[K] E) → C_E` with

`c(σ,τ) * b(στ) = b(σ) * (σ • b(τ)) * d(σ,τ)` for all `σ, τ`,

where `σ •` is the arithmetic action. It is the generic theorem of
`Langlands.GroupTheory.CocycleClassEquiv`, which is proved through Mathlib's
`H2π_eq_iff`, specialized to these carriers.
`cohomologyClass_eq_iff_exists_cochain` combines it with the published
`cohomologyClass_eq_of_cochain` as an equivalence. The forward direction is
reused, not reproved.

`classCochain hcd` is the cochain chosen from a proof `hcd` of class
equality, and `classCochain_spec` states its equation. The module does not
claim it is unique or canonical. As an unformalized remark, multiplying it by
any one-cocycle `z`, that is `z(στ) = z(σ) * (σ • z(τ))`, gives another valid
cochain.

## Equivalence of the extensions of cohomologous representatives

`extensionEquiv hcd : Extension c ≃ₜ* Extension d` is the generic
`continuousEquivOfCohomologyClassEq`. That is the published
`MapData.continuousEquivOfEquivs` applied to the identity continuous
equivalences of `C_E` and `E ≃ₐ[K] E` and to the chosen cochain. Since
`E ≃ₐ[K] E` is discrete, the cochain is continuous. The extensions are the
published `RelativeIdeleCocycle.Extension`, with the topology induced from
the product `C_E × (E ≃ₐ[K] E)`. Neither group nor topology is rebuilt.

With `b = classCochain hcd`, the coordinate identities hold by reflexivity:

- `extensionEquiv_left`, `extensionEquiv_right`: `(a, σ) ↦ (a * b(σ), σ)`;
- `extensionEquiv_symm_apply`: the inverse is `(a, σ) ↦ (a / b(σ), σ)`.

The equivalence fixes `C_E` and commutes with projection to `E ≃ₐ[K] E`, in
both directions:

- `extensionEquiv_inclusion`: `inclusion c a ↦ inclusion d a`;
- `extensionEquiv_symm_inclusion`: `inclusion d a ↦ inclusion c a` under the
  inverse;
- `projection_extensionEquiv`, `projection_extensionEquiv_symm`: the
  projections agree.

## The class-indexed extension

In `ClassExtension`, `representative x` is the normalized idele-class
cocycle chosen from the published
`RelativeIdeleCocycle.cohomologyClass_surjective x`, and
`cohomologyClass_representative x` states that its actual class is `x`.
The choice is made by `Classical.choose` and nothing distinguishes it.

`ClassExtension x : Type v` is by definition
`RelativeIdeleCocycle.Extension (ClassExtension.representative x)`, the
published group of pairs for that cocycle. It is not an arbitrary carrier,
a supplied extension, or a Weil-group package. Its instance
`ClassExtension.isTopologicalGroup` is the published
`extensionIsTopologicalGroup`. The following are the published constructions
for the representative, under the names of this namespace:

- `inclusion x : C_E →* ClassExtension x` and
  `projection x : ClassExtension x →* (E ≃ₐ[K] E)`. `continuousInclusion x`
  and `continuousProjection x` are the same maps as continuous homomorphisms
  `→ₜ*`.
- `sectionMap x`, the section `σ ↦ (1, σ)`.
- `inclusion_injective`, `projection_surjective`, and `exact`. The last says
  the range of the inclusion equals the kernel of the projection.
- `continuous_inclusion`, `continuous_projection`, `continuous_sectionMap`.
- `isOpenEmbedding_inclusion` and `isOpenQuotientMap_projection`. So `C_E`
  carries exactly its quotient topology inside the extension, and the
  quotient carries the discrete topology.
- `factorSet`: the factor set of `sectionMap x` is `representative x`.
- `conjugation` and `conjugation_mk`: conjugating `inclusion x a` by `t` gives
  the inclusion of the arithmetic image of `a` under `projection x t`. On
  idele representatives this image is given by `ideleEquiv`.

## Representative independence

Let `c` be any normalized idele-class cocycle and `hc : c.cohomologyClass = x`.
`equivOfRepresentative c hc : RelativeIdeleCocycle.Extension c ≃ₜ* ClassExtension x`
is `extensionEquiv` for the class equality `c ~ representative x` obtained
from `hc` and `cohomologyClass_representative`. The following theorems give
its coordinates and its compatibility with the ends:

- `equivOfRepresentative_left`, `equivOfRepresentative_right`: the
  `(a, σ) ↦ (a * b(σ), σ)` formula with the chosen cochain `b`;
- `equivOfRepresentative_inclusion`, `equivOfRepresentative_symm_inclusion`:
  `C_E` is fixed;
- `projection_equivOfRepresentative`,
  `projection_equivOfRepresentative_symm`: the projections agree.

`exists_continuousMulEquiv` states only that some continuous multiplicative
equivalence fixes `C_E` and commutes with the projections. The module claims
no uniqueness or canonicity. By Artin–Tate p.130, which this module does not
formalize, two such equivalences differ by a twist `(a, σ) ↦ (a * z(σ), σ)`
with `z` a one-cocycle. The module does not quotient by this ambiguity.

## Finite Galois number-field extensions

The section `FiniteGalois` adds `[NumberField K] [IsGalois K E]` and keeps the
same carrier `ClassExtension x`. `nat_card_quotient` is Mathlib's
`IsGalois.card_aut_eq_finrank`, giving `Nat.card (E ≃ₐ[K] E) = [E : K]`.
`index_range_inclusion` proves that the image of `C_E` has index `[E : K]` in
`ClassExtension x`. The proof rewrites the range as the kernel of the
surjective projection by `exact`, then uses `Subgroup.index_ker`.

## Provenance and scope

This is internal derived material. It reuses the normalized relative cocycle
extension of `Langlands.ClassField.Global.Cocycle`, built on
`Langlands.GroupTheory.CocycleExtension`. It also reuses the actual cohomology
and normalized representatives of `Langlands.ClassField.Global.Cohomology`
and `Langlands.GroupTheory.CocycleCohomology`, and the cochain maps of
`Langlands.GroupTheory.CocycleMap`. The converse cochain theorem comes from
the generic helper `Langlands.GroupTheory.CocycleClassEquiv`. The conventions
for factor sets, extensions and cohomologous cocycles follow Artin and Tate,
*Class Field Theory* (2009), Chapter XIII section 1, printed pp.127–130 (PDF
pp.136–139), registered as `artin-tate-2009-class-field-theory`, SHA256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`. Theorem 1
on p.130 there motivates representative independence.

The module does not select or characterize an arithmetic fundamental class.
It does not use the published `GlobalFundamentalClassStatement`. It does not
construct a relative or absolute Weil group. Fundamental-class
instantiation, tower transitions, inverse limits and local-global maps
remain separate obligations.
