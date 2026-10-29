# Injectivity and localization comparison for the actual power-kernel quotient

Authors: Worker 490 (Lean implementation and source verification), Worker 911
(published target and proof orientation in the task context).

The module `Langlands.Algebra.RenardEndomorphismQuotientProof` proves

```lean
theorem quotientLocalizationStatements : QuotientLocalizationStatements.{u, v}
```

in namespace `Langlands.Renard.EndomorphismLocalization`. This is exactly the
published target from
`Langlands.Algebra.RenardEndomorphismQuotientStatements`, imported unchanged.
The second import is the published
`Langlands.Algebra.RenardEndomorphismLocalizationKernelProof` by Worker 900.
It supplies the kernel criterion and injective-case theorem used below.
No unpublished theorem is assumed.

## Source and scope

David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, A.III.1, unnumbered lemma (ii) after example 5,
printed253/PDF259, is the original source. Registered ID:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The retained original is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
PDF258–259 were read and PDF259 was visually inspected.

The supplementary author errata
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were read on PDF18–19; those pages contain no entry for this lemma. This is
a bounded check of the older edition's errata. The 2026 edition governs.
The public Appendix A corrections and stable-quotient notes were also consulted.

The source asserts that the induced operator on the quotient by the union of
power kernels is injective, that its canonical localization map is injective,
and that its localization is isomorphic to the original localization. The
published target gives a precise derived comparison: the equivalence uniquely
carries the composite of the quotient projection and canonical map to the
original canonical map and intertwines the localized operators. The extension
from fields to arbitrary commutative unital rings is internal. The proof
constructs the two maps from the universal properties, as in the source, and
uses the published fraction-based kernel and injectivity results.

All generic helpers take `R : Type u` with `[CommRing R]`, `V : Type v` with
`[AddCommGroup V] [Module R V]`, and `a : Module.End R V`. The universes `u`
and `v` are independent. There is no finiteness, Noetherianity,
nontriviality, stabilization, or injectivity hypothesis on `a`. Zero rings,
zero modules and nilpotent endomorphisms are included.

The objects remain exactly the published ones:

| Mathematical object | Lean term |
| --- | --- |
| K, the union of the power kernels | `powerKernel a` |
| V/K and its projection | `PowerKernelQuotient a`, `quotientProjection a` |
| The induced operator | `quotientEnd a` |
| The two actual localizations | `Localized a`, `Localized (quotientEnd a)` |
| The canonical maps and localized operators | `iota`, `localizedEnd` |

The quotient lives in `Type v`; both localizations live in `Type (max u v)`.
The new comparison maps use these types directly.

## Injectivity

`quotientEnd_injective a` reduces injectivity to triviality of the kernel
using `LinearMap.ker_eq_bot` and `ker_eq_bot'`. Given a quotient element
annihilated by `quotientEnd a`, the surjective `quotientProjection a` gives
a representative `z`. The published `quotientEnd_projection` and
`ker_quotientProjection` identify the hypothesis with `a z ∈ powerKernel a`.
By `mem_powerKernel_iff` there is an `n` with `(a^n) (a z) = 0`.
Composition powers give `(a^(n+1)) z = 0`, so `z` lies in the power kernel
and its quotient class is zero.

`quotientIota_injective a` applies the published `iota_injective` to
`quotientEnd a` and the preceding injectivity result. Its kernel-criterion
proof is imported, not repeated.

## Descent and the two factor maps

Write `π = quotientProjection a`, `a' = quotientEnd a`, `ι = iota a`,
`ι' = iota a'`, `ã = localizedEnd a`, and `ã' = localizedEnd a'`.

`quotientIotaLift a`, denoted `d`, is the actual quotient descent
`(powerKernel a).liftQ (iota a) ...`. The well-definedness proof sends a
member of the power kernel to zero using `mem_powerKernel_iff` and the
published `iota_eq_zero_iff`. Its representative law
`quotientIotaLift_projection` is `d (π z) = ι z`, by reduction.
`quotientIotaLift_intertwines` proves `d (a' q) = ã (d q)` by taking a
representative of `q` and applying `iota_intertwines`.

`quotientLocalizationMap a`, denoted `F`, is

```lean
factor (quotientEnd a) (localizedEnd a) (isUnit_localizedEnd a)
  (quotientIotaLift a) (quotientIotaLift_intertwines a)
```

Thus `F : Localized a' →ₗ[R] Localized a`. Its `_iota` and `_intertwines`
theorems are the published `factor_comp_iota` (evaluated on an element)
and `factor_intertwines`: `F (ι' q) = d q` and `F (ã' z) = ã (F z)`.

`quotientProjection_iota_intertwines` shows that `ι' ∘ π` intertwines
`a` and `ã'`, by `quotientEnd_projection` and `iota_intertwines`.
`localizationQuotientMap a`, denoted `G`, applies `factor` to that composite
with invertible target `ã'`. Its `_iota` and `_intertwines` theorems give
`G (ι z) = ι' (π z)` and `G (ã z) = ã' (G z)`.

## Inverse identities and uniqueness

`quotientLocalizationMap_comp_localizationQuotientMap` proves `F ∘ G = id`
using the published `eq_of_intertwines` for the original localization.
Both the composite and the identity intertwine `ã` with itself; `ã` is
injective because it is a unit. On `ι z` the representative laws give
`F (G (ι z)) = F (ι' (π z)) = d (π z) = ι z`.

`localizationQuotientMap_comp_quotientLocalizationMap` similarly proves
`G ∘ F = id` on the localized quotient. For the required equality on
`ι' q`, choose `z` with `π z = q`; then
`G (F (ι' q)) = G (d (π z)) = G (ι z) = ι' q`.

`quotientLocalizationEquiv a` is `LinearEquiv.ofLinearMap F G` with
these two identities. Its theorems
`quotientLocalizationEquiv_comp_iota_projection` and
`quotientLocalizationEquiv_intertwines` give the exact two compatibility
laws in the target.

`quotientLocalizationEquiv_unique` takes any other equivalence `e` with
those laws. Its linear map and that of the constructed equivalence
intertwine `ã'` with the injective `ã`. The projection compatibility,
evaluated on representatives using surjectivity of `π`, shows they agree
after `ι'`. Hence `eq_of_intertwines` makes the linear maps equal, and
`LinearEquiv.toLinearMap_injective` makes the equivalences equal.
`quotientLocalizationComparison` combines this uniqueness with the
constructed witness in the exact `∃!` form.

## Aggregate and verification

`quotientLocalizationStatements` assembles the three ring statements
from `quotientEnd_injective`, `quotientIota_injective` and
`quotientLocalizationComparison`. The separate field statement applies
the same helpers to the commutative ring underlying each field. The
aggregate is closed, with independent universe parameters `u` and `v`.

The pinned Lean service compiles the module and inspects the aggregate.
Its only axioms are `propext`, `Classical.choice` and `Quot.sound`.
The proof uses no proof holes, new axioms or native decision procedure.
The target pair and its imported pairs are unchanged.

This unit does not establish additional inverse-power extension converses,
surjective-canonical-map corollaries, general algebra-action comparisons,
categorical localization packaging or the final C.II proposition. The
kernel/exhaustion aggregate is imported as published work.
