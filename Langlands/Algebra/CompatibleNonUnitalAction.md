# Compatible nonunital algebra actions and actual linear endomorphisms

Authors: Worker 751 read the cited passages, designed and implemented this
module and wrote this note. Worker 709 specified the task and wrote the private
feasibility probe `CompatibleActionProbe.lean` (shared draft of task
`1af21cd4-c861-487b-b092-17818900b758`). The bodies of `ofLinearEndHom` and
`toLinearEndHom` below are taken from that probe, renamed and adapted. Everything
else here is new.

The module `Langlands/Algebra/CompatibleNonUnitalAction.lean` connects a
possibly noncommutative and nonunital `k`-algebra `B` acting on a `k`-module
`V` in two ways. One side is an actual nonunital `k`-algebra homomorphism
`B →ₙₐ[k] Module.End k V`. The other is the published ambient action
`Langlands.Algebra.NonUnitalModule B V` together with Mathlib's
`IsScalarTower k B V` and `SMulCommClass k B V`. It also connects `k`-linear
intertwiners to the published additive `NonUnitalModuleHom`. It reuses the
published `NonUnitalModule`, `NonUnitalModuleHom`, `NonUnitalModule.zero`,
`NonUnitalModule.ofModule`, `NonUnitalModule.equivEndHom` and `IsUnitalModule`
from `Langlands.Algebra.NonUnitalModule` by their Lean names. It does not
create a new ambient module category.

## Original source and provenance

David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated **9 July 2026**. This is the registered source
`renard-2026-representations-groupes-reductifs-padiques`, at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Printed page = PDF page minus 6. Worker 751 read the following passages directly:

- Chapter I, notation and conventions, printed pp. 5–6 / PDF pp. 11–12. Rings
  are not assumed unital unless explicitly stated. Modules over a unital ring are
  not assumed unital a priori; "unital module" means that `1_A` acts as the
  identity.
- Appendix A.III.1, example 5, printed p. 252 / PDF p. 258. Its final sentence
  says that if `B` is a `k`-algebra, the same construction can be made with
  `B`-modules in place of `k`-vector spaces and `B`-module endomorphisms in place
  of vector-space endomorphisms. The lemma after it, printed p. 253 / PDF p. 259,
  was read as context only.
- Appendix C.II, final proposition and proof, printed p. 279 / PDF p. 285. This
  is the motivating use, for a commutative noetherian `ℂ`-algebra `B` and a
  finitely generated `B`-module `L` with `a ∈ End_B(L)`.

Supplementary errata: the registered `renard-2010-corrections-complements`
(SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`).
Its appendix notes, PDF pp. 17–19, have no entry for these passages. This was a
limited check, not an exhaustive reading. The 2026 edition governs.

Provenance: the source states the convention that algebras and modules may be
nonunital. It uses "a `B`-module that is also a `k`-vector space with
`k`-linear `B`-endomorphisms" without spelling out a formal interface. Every
declaration in this module is **derived implementation content** that realizes
that convention: the homomorphism description, the compatibility structures,
the linear intertwiners, the conversions, round trips, the zero-action checks
and the unital specialization. None of them is a verbatim assertion of Renard.
The only mathematics involved is the standard correspondence between actions and
homomorphisms into endomorphism rings.

## Hypotheses, universes and the source-facing interface

Universes are independent throughout: `k : Type u`, `B : Type v`, `V : Type w`,
a target `W : Type x`, a third space `P : Type y`, and a fourth space
`Q : Type z` (only in `LinearIntertwiner.comp_assoc`). None of `B`, `V`, `W`
is assumed finite-dimensional, nontrivial or nondegenerate. `B` is never
assumed commutative or unital, except in the explicitly unital section.

**Weaker prerequisites used by the conversions.** The general lemmas assume
only

```text
[CommSemiring k] [NonUnitalRing B] [Module k B]
[AddCommGroup V] [Module k V]   (and the same for W, P, Q)
```

This is the generality in which Mathlib forms `B →ₙₐ[k] Module.End k V`. The
scalar ring `k` is a commutative semiring rather than a field. This extension is
deliberate and harmless: no conversion uses inverses in `k`.

**Complete source-facing interface.** The source has a field `k`, an
associative, possibly noncommutative and nonunital `k`-algebra `B`, and
`k`-vector spaces. In Lean this is

```text
[Field K] [NonUnitalRing A] [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
[AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
```

The last two class assumptions on `A` make multiplication `K`-bilinear. Mathlib's
`NonUnitalAlgHom` type does not require them. The conversions below do not use
them either, so they are absent from the general lemmas, which are therefore
stated in greater generality. This does **not** mean that every `Module k B`
over a `NonUnitalRing B` is a `k`-algebra. Nothing in this module asserts or
derives `IsScalarTower k B B` or `SMulCommClass k B B`, and nothing claims that
a homomorphism `ρ` forces bilinearity on `B`.

The section `FieldInterface` at the end of the file checks the specialization
to this exact interface. It does so by `example`s stated with all of the above
section variables in scope. Lean includes the instance variables
`[IsScalarTower K A A] [SMulCommClass K A A]` in each example because their
dependencies `K` and `A` occur there. The examples check:

- `Module.End K V` itself has `IsScalarTower` and `SMulCommClass` over `K`;
- the action formula and both compatibility laws for `ofLinearEndHom ρ`;
- both round trips and the equivalence `equivLinearEndHom K A V`;
- both intertwiner round trips;
- for `[Nontrivial V]`, the zero action is compatible and kills a nonzero vector;
- for a unital `K`-algebra `R` and `[Nontrivial V]`, the zero action is not
  unital;
- the unital specialization for `[Ring R] [Algebra K R] [Module R V]
  [IsScalarTower K R V]`, with `R : Type y`.

## 1. From a homomorphism to a compatible ambient action

Namespace `Langlands.Algebra.NonUnitalModule`. Here `ρ : B →ₙₐ[k] Module.End k V`.
No named type alias is introduced: a compatible action is the actual Mathlib
type `B →ₙₐ[k] Module.End k V`.

- `ext` (proof): two ambient actions `h₁ h₂ : NonUnitalModule B V` with the
  same scalar multiplication are equal. Route: apply the injectivity of the
  published equivalence `equivEndHom` to the equality of the two homomorphisms
  `toEndHom h₁ = toEndHom h₂`. That equality is proved by `NonUnitalRingHom.ext`
  and `AddMonoidHom.ext` from the hypothesis.
- `ofLinearEndHom ρ : NonUnitalModule B V` (an `abbrev`, **not** an instance).
  It defines `b • v := ρ b v`. Each ambient law is the corresponding law of `ρ`
  evaluated at `v`: `map_mul`, `map_add`, `map_zero` of `ρ`, and additivity of
  each `ρ b`.
- `ofLinearEndHom_smul`: `b • v = ρ b v` under `letI := ofLinearEndHom ρ`
  (by `rfl`).
- `ofLinearEndHom_smul_assoc`: `(c • b) • v = c • (b • v)`. This is `map_smul ρ c b`
  evaluated at `v`.
- `ofLinearEndHom_smul_comm`: `b • (c • v) = c • (b • v)`. This is
  `(ρ b).map_smul c v`.
- `ofLinearEndHom_isScalarTower ρ` and `ofLinearEndHom_smulCommClass ρ`: the named
  explicit adapters, stated under `letI := ofLinearEndHom ρ`. They package the
  two laws as `IsScalarTower k B V` and `SMulCommClass k B V`.
- `toEndHom_ofLinearEndHom_apply`: the published additive description
  `toEndHom (ofLinearEndHom ρ)` evaluates `ρ`.

## 2. From a compatible ambient action to a homomorphism

- `toLinearEndHom k : B →ₙₐ[k] Module.End k V`, with instance binders
  `[h : NonUnitalModule B V] [hT : IsScalarTower k B V] [hC : SMulCommClass k B V]`.
  Each `b` acts by the `k`-linear map `v ↦ b • v`. Additivity is `smul_add`;
  `k`-linearity is `smul_comm`. The homomorphism laws use the ambient laws
  `zero_smul`, `add_smul`, `mul_smul` and the tower law `smul_assoc`, each proved
  by linear-map extensionality.
- `toLinearEndHom_apply` (simp): `toLinearEndHom k b v = b • v`.
- `toLinearEndHom_ofLinearEndHom ρ`: **homomorphism round trip**. This is an
  equality of actual homomorphisms. The structures are supplied by the named
  arguments `(h := ofLinearEndHom ρ) (hT := ofLinearEndHom_isScalarTower ρ)
  (hC := ofLinearEndHom_smulCommClass ρ)`. Proof: extensionality, then `rfl`.
- `ofLinearEndHom_toLinearEndHom`: **action round trip**. This is an equality of
  the retained ambient structures, `ofLinearEndHom (toLinearEndHom k) = h`,
  proved with `ext`.
- `equivLinearEndHom k B V` is an exact equivalence between the subtype
  `{h : NonUnitalModule B V // IsScalarTower k B V ∧ SMulCommClass k B V}` and
  `B →ₙₐ[k] Module.End k V`. In the subtype, both structures are read with `h`
  as the action. The proof uses the two round trips together with
  `Subtype.ext`. Its simp lemmas are `equivLinearEndHom_apply` and
  `equivLinearEndHom_symm_apply_coe`.

The scalar-tower and commuting proofs are propositions, so the subtype records
all compatibility data. The equivalence therefore identifies compatible ambient
actions with homomorphisms, with nothing lost.

## 3. Linear intertwiners

`LinearIntertwiner ρ σ` (for `ρ : B →ₙₐ[k] Module.End k V` and
`σ : B →ₙₐ[k] Module.End k W`) is a structure extending the actual linear-map
type `V →ₗ[k] W` by the field `map_action' : f (ρ b v) = σ b (f v)`. It has
`FunLike` and `LinearMapClass` instances, and the following lemmas:

- `ext`, `coe_toLinearMap`, `coe_mk`;
- `map_action` (the intertwining equation);
- `toLinearMap_comp_action`: `f ∘ₗ ρ b = σ b ∘ₗ f`;
- `id ρ` and `comp g f`, where composition intertwines by rewriting with both
  intertwining equations;
- `id_apply`, `comp_apply`, `toLinearMap_id`, `toLinearMap_comp`;
- `id_comp`, `comp_id`, `comp_assoc`, all by `rfl`.

The bridge to the published additive intertwiners for the actions
`ofLinearEndHom ρ` and `ofLinearEndHom σ` is as follows. Its statements are
written under `letI := NonUnitalModule.ofLinearEndHom ρ` and
`letI := NonUnitalModule.ofLinearEndHom σ`; see the next section for why.

- `toNonUnitalModuleHom f : NonUnitalModuleHom B V W`. The underlying additive
  map is that of `f`, and the intertwining equation is `f.map_action`. Its
  application lemma is `toNonUnitalModuleHom_apply`.
- `ofNonUnitalModuleHom f hf : LinearIntertwiner ρ σ` converts an ambient
  intertwiner **only** when its `k`-linearity
  `hf : ∀ c v, f (c • v) = c • f v` is supplied separately. Nothing infers
  `k`-linearity from additivity. Its application lemma is
  `ofNonUnitalModuleHom_apply`.
- `ofNonUnitalModuleHom_toNonUnitalModuleHom` and
  `toNonUnitalModuleHom_ofNonUnitalModuleHom`: the underlying-map round trips,
  as equalities of the actual bundled maps (`rfl`).
- `equivNonUnitalModuleHom ρ σ`: an exact equivalence between `LinearIntertwiner
  ρ σ` and `{f : NonUnitalModuleHom B V W // ∀ c v, f (c • v) = c • f v}`.
- `toNonUnitalModuleHom_id` and `toNonUnitalModuleHom_comp`: identity and
  composition agree with the published `NonUnitalModuleHom.id` and
  `NonUnitalModuleHom.comp` (`rfl`).

For actions already given as instances, the namespace
`Langlands.Algebra.NonUnitalModuleHom` works with
`[NonUnitalModule B V] [IsScalarTower k B V] [SMulCommClass k B V]` and the same
for `W` and `P`:

- `toLinearIntertwiner k f hf`: from an ambient intertwiner and its supplied
  `k`-linearity to `LinearIntertwiner (toLinearEndHom k) (toLinearEndHom k)`.
  It is `LinearIntertwiner.ofNonUnitalModuleHom`. This typechecks because
  `ofLinearEndHom (toLinearEndHom k)` unfolds definitionally to the given
  instance.
- `ofLinearIntertwiner f`: the converse, giving `NonUnitalModuleHom B V W` for
  the given instances.
- Lemmas: `toLinearIntertwiner_apply`, `ofLinearIntertwiner_apply`,
  `toNonUnitalModuleHom_toLinearIntertwiner`,
  `ofLinearIntertwiner_toLinearIntertwiner`,
  `toLinearIntertwiner_ofLinearIntertwiner`, `toLinearIntertwiner_id`,
  `toLinearIntertwiner_comp`. The last takes the two linearity hypotheses and
  proves linearity of the composite by rewriting with `comp_apply`.

## Action-instance ambiguity and how to select the action

`ofLinearEndHom`, `zero`, `ofModule` and `unitalLinearEndHom` are named
constructions; none is a global instance. Downstream code selects the intended
action in one of two ways:

- locally, with `letI := NonUnitalModule.ofLinearEndHom ρ`, as in this module's
  statements;
- for `toLinearEndHom`, by passing the named arguments `(h := …) (hT := …)
  (hC := …)`.

The published instance `NonUnitalModule.actionSMul` has priority 1200. Once a
`NonUnitalModule B V` structure is local, `b • v` therefore uses that specified
action, even when the carrier types also have another canonical `SMul B V`.
`ofLinearEndHom_zero_self_smul` checks this. For a field `K` and the zero
homomorphism `K →ₙₐ[K] Module.End K K`, under the `letI`, `c • d = 0` holds by
`rfl` for all `c d : K`. So notation selects the zero action, not
multiplication in `K`.

Three consequences matter for downstream code:

1. Projections and coercions of `NonUnitalModuleHom B V W` have
   instance-implicit arguments. Lean synthesizes them, so writing
   `@NonUnitalModuleHom B V W _ _ _ (ofLinearEndHom ρ) (ofLinearEndHom σ)` and then
   using `f.toAddMonoidHom` fails ("failed to synthesize NonUnitalModule B V").
   This is why the bridge statements and binders are wrapped in `letI`. Since
   `letI` inlines its value, the resulting types are exactly the `@`-form above.
2. With an action `B`-structure local, a scalar `c : k` uses the `Module k V`
   action only when `k` and `B` are different types. If `k = B` (as in
   `K` acting on `K`), `c • v` written under the `letI` would select the
   specified action. The general statements here are elaborated with distinct
   variables `k` and `B`, so they keep the `Module k V` scalar action when
   instantiated. New statements about the case `k = B` should write the
   `k`-scalar action explicitly.
3. Two different actions on the same carrier type should not be made local
   simultaneously. The generic statements use distinct variables `V`, `W`, `P`;
   instantiating them with equal carriers substitutes the elaborated terms and
   does not re-run instance search.

## 4. The zero action and the unital specialization

Zero action (general hypotheses):

- `ofLinearEndHom_zero`: `ofLinearEndHom 0 = NonUnitalModule.zero`, the
  published zero action (by `ext`);
- `isScalarTower_zero` and `smulCommClass_zero`: the zero action is compatible.
  The first uses `smul_zero` in `V`. The second does not use `Module k B` and
  omits it.
- `toLinearEndHom_zero`: the published zero action corresponds to the zero
  homomorphism.

Nonzero-space regressions, checked independently:

- `not_isUnitalModule_ofLinearEndHom_zero`: for `[Ring B] [Module k B]` and
  `[Nontrivial V]`, the zero action is not an `IsUnitalModule`. A nonzero `v`
  would satisfy `v = 1 • v = 0`.
- `ofLinearEndHom_zero_self_smul`: on the nonzero space `K` over a field `K`,
  every `c • d` is `0` (the action-selection check above).
- `ofLinearEndHom_zero_ne_ofModule`: this zero action differs from the ordinary
  action `NonUnitalModule.ofModule K K`, because `1 • 1` is `1` for the latter
  and `0` for the former.

Unital specialization (section `Unital`; hypotheses `[CommSemiring k] [Ring B]
[Algebra k B] [AddCommGroup V] [Module k V] [Module B V] [IsScalarTower k B V]`):

- `unitalLinearEndHom k B V : B →ₙₐ[k] Module.End k V` is the named,
  non-instance definition `(Algebra.lsmul k k V).toNonUnitalAlgHom`. This is
  Mathlib's unital algebra homomorphism `b ↦ (v ↦ b • v)` with its unit
  forgotten. `unitalLinearEndHom_apply` gives `b • v` with the original module
  action. `unitalLinearEndHom_one` records that the unit maps to the identity.
- `ofModule_isScalarTower` and `ofModule_smulCommClass`: the published unital
  adapter `NonUnitalModule.ofModule B V` is compatible. The tower law is the
  assumed `IsScalarTower k B V`; the commuting law is `smul_comm`, whose
  `SMulCommClass k B V` Mathlib derives from the tower law for an algebra
  (`IsScalarTower.to_smulCommClass`).
- `ofLinearEndHom_unitalLinearEndHom`: the ambient action of this homomorphism
  is exactly `NonUnitalModule.ofModule B V`. So the specialization retains the
  actual module action.
- `toLinearEndHom_ofModule`: conversely, `ofModule` corresponds to
  `unitalLinearEndHom`.
- `isUnitalModule_ofLinearEndHom_unitalLinearEndHom`: this action is unital, by
  `one_smul`.

None of these is an instance, so none imposes unitality or overrides a
separately specified action such as the zero action above.

## Deferred obligations

This unit provides only the interface and its intrinsic laws. The following
remain separate obligations of the surrounding Renard development:

- the localized `B`-action on `V_a` and its `B`-linear universal property;
- `B`-stability of kernels and images;
- compatible submodule and quotient machinery;
- equivalences of bundled categories;
- the stable-endomorphism and finite-localization theorems of C.II.

None of them is assumed as a field of this interface or proved here.
