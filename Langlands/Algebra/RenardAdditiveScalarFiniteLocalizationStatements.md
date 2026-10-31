# Additive stable generation and scalar-linear localization

Worker 709 prepared these derived internal statements. Worker 702 checked
the exact hypotheses, imported predicates and source passages and submitted
the pair. The statements assert no equivalence with Renard's finiteness
terminology and prove no result.

The two propositions in
`Langlands.Algebra.AdditiveScalarStableGeneration` use a commutative
coefficient ring `R`, a possibly nonunital and noncommutative `R`-algebra
`A`, an ordinary `R`-module `M`, and its actual compatible action
`ρ : A →ₙₐ[R] Module.End R M`. The coefficient, algebra and carrier
universes are independent, in that order. The algebra structure is expressed
by `CommRing R`, `NonUnitalRing A`, `Module R A`, `IsScalarTower R A A`
and `SMulCommClass R A A`; the carrier has `AddCommGroup M` and
`Module R M`. Stability explicitly means
`∀ (a : A) (m : M), m ∈ P → ρ a m ∈ P`.

`ModuleGenerationComparisonStatement` says that existence of a finite set
generating `M` among all additive subgroups stable under `ρ` implies
existence of a finite set generating it among the scalar-linear submodules
stable under the same action.
`SubmoduleGenerationComparisonStatement` says that finite stable
generation of every stable additive subgroup implies finite stable
generation of every stable scalar-linear submodule. For each subgroup
or submodule the generating set is contained in that object, and every
stable object containing the set must contain the original object.
The propositions assert existence of generators in the conclusions; the
intended proof reuses the generators supplied by the additive hypotheses.
Neither proposition asserts the reverse implication.

`Langlands.Renard.AlgebraActionLocalization.AdditiveIdealFiniteLocalizationStatement`
specializes this comparison to a complex algebra `B`, a complex vector
space `V`, an actual compatible action `ρ` and self-intertwiner
`f : LinearIntertwiner ρ ρ`.
The algebra and carrier universes are independent. It retains
`NonUnitalRing B`, `Module ℂ B`, `IsScalarTower ℂ B B`,
`SMulCommClass ℂ B B`, `AddCommGroup V` and `Module ℂ V`.
Its three hypotheses are written out using actual additive subgroups:

- Every additive left ideal `P` of `B` contains a finite subset `S` such
  that every additive left ideal `Q` containing `S` contains `P`. Both
  ideals are stable under left multiplication by every `b : B`; neither
  is required to be closed under complex scalars.
- A finite subset generates `V` among all additive subgroups stable under
  its original action `ρ`.
- A finite subset generates the actual `Localized f.toLinearMap` among
  all additive subgroups stable under its actual action
  `localizedAction f.toLinearMap ρ (fun b v => f.map_action' b v)`.

The source and localized generation statements mean that every stable
additive subgroup containing the finite set is the whole additive group.
Addition, negation and the action participate in generation. These are
not assumptions of finite complex dimension.

The conclusion is the unchanged conjunction
`CompatibleLocalizationStabilizationAt ρ f` and
`∀ n, 0 < n → Stable (f.toLinearMap ^ n) →
CompatibleStablePowerImageAt ρ f n`.
Thus the actual canonical map is surjective; one positive exponent gives
its compatible kernel and stability; and every positive stable power
gives complementary compatible kernel and image and the unique normalized
complex-linear equivalence from the actual localization to that image.
The equivalence preserves the actions and operators, and its inverse is
the restriction of the actual canonical map. These conditions remain
inside the published unique-existence predicate.

`Langlands.Renard.AdditiveScalarFiniteLocalizationStatement` is exactly
the conjunction of the two generic comparisons and the complex
localization consequence, in that order, with universes `uR`, `uB`, `uV`.
All components are closed transparent propositions; each binds its own
algebraic inputs. They assume no unit-action law, nondegeneracy,
commutativity of `B`, nontriviality, countability or finite dimension.

## Provenance and boundary

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Worker 709 reread printed6/PDF12 and printed279/PDF285 directly from that
fingerprinted original for these statements. Worker 702 independently
reread those two pages, visually checked PDF285,
and rechecked the source fingerprint. No `notes/errata` directory is present
in the current Library `42ebad9dec7efaf48307e0b6085168e104486dfb`.
Worker 702 also read PDF18–19 of the registered older supplement
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`;
these pages do not resolve the convention. The earlier parent audit
also read the relevant localization, stability, scalar-unitization and
categorical finiteness passages.
The published
[finiteness source audit](../../notes/renard/nonunital-finiteness-sources.md)
records the original-reference and edition limits.

Renard permits nonunital rings and actions, and C.II assumes a commutative
Noetherian complex algebra, a finite source module and a finite actual
localization. The present statements are internal sufficient conditions
with every generation operation specified. They do not identify the
author's intended meaning of those finiteness phrases. Allowing a
noncommutative algebra and retaining canonical uniqueness are inherited
internal strengthenings. The generic coefficient-ring comparisons are
derived algebra, not separately numbered source assertions.

The intended proof forgets scalar closure from a stable scalar-linear
submodule to its actual underlying additive subgroup. It then applies the
published `stableIdealFiniteLocalization` after the two generation
comparisons, using the regular left action for the ideal hypothesis.
This is a proof route, not a conclusion assumed as input or a proof
supplied by this statement file. It uses the same actual localization
and compatible actions throughout.

The original-action categorical finiteness and integer-unitization
results retain their existing owners. These statements add no category
equivalence, subobject comparison, unitization action or localization
construction. The reverse generation comparisons, the source convention
identification, its inverse-polynomial proof and the full C.II and
whole-book assertions remain separate.
