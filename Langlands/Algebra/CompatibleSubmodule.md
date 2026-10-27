# Stable subspaces, restricted actions and quotient actions of a compatible action

Author: Worker 277 read the cited passages, designed and implemented this module
and wrote this note. The task contract (task
`225c0c50-f2f1-4da9-9cbd-b70bd64c5b33`, published by Worker 6) fixes the text of
the stability predicate `∀ a m, m ∈ S → ρ a m ∈ S` and the quotient formula
`ρQuot a (S.mkQ m) = S.mkQ (ρ a m)`. No draft or probe of another worker was
reused. The module imports, and reuses by Lean name, the compatible-action bridge
`Langlands.Algebra.CompatibleNonUnitalAction` (task
`1af21cd4-c861-487b-b092-17818900b758`; Worker 751, with Worker 709) and the
published `Langlands.Algebra.NonUnitalModule`.

The module `Langlands/Algebra/CompatibleSubmodule.lean` works with an actual
compatible action `ρ : A →ₙₐ[k] Module.End k M` of a possibly noncommutative and
nonunital algebra `A` on a vector space `M`. It provides:

1. the stability predicate `IsStableSubmodule ρ S` for an actual
   `S : Submodule k M`, and the bundled type `CompatibleSubmodule ρ` of stable
   subspaces with its complete lattice, inherited from `Submodule k M`;
2. the actual restricted action `S.restrictAction : A →ₙₐ[k] Module.End k S` and
   quotient action `S.quotientAction : A →ₙₐ[k] Module.End k (M ⧸ S)`, the subtype
   inclusion and quotient projection as linear intertwiners, and the corresponding
   ambient actions and ambient intertwiners obtained through the bridge;
3. for a linear intertwiner `f : LinearIntertwiner ρ σ` (the bridge's type), the
   stable kernel and image, stable inverse and direct images, and the restrictions
   and descents of `f` to stable subspaces and quotients, built from the actual
   Mathlib linear maps;
4. checks for the zero original action, including `A = k = M = ℂ`.

Everything here is a definition or one of its short intrinsic laws. No unit of
`A`, unit law, nondegeneracy, simplicity, exactness or finiteness is assumed or
asserted (see "Excluded content").

## Sources and provenance

Governing source: David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated **9 July 2026**, registered as
`renard-2026-representations-groupes-reductifs-padiques`, file
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`
(checked by Worker 277). Printed page = PDF page − 6. Worker 277 read these
passages in the PDF:

- Notation and conventions, printed pp. 5–6 / PDF pp. 11–12: "Les anneaux ne sont
  pas supposés unitaires, sauf mention explicite du contraire. [...] Si 𝐴 est un
  anneau unitaire, les modules sur 𝐴 ne sont pas supposés unitaires a priori."
  Hence `A` has no unit here, and no unit law is imposed on the action.
- I.2.1, printed p. 14 / PDF p. 20: "Si 𝐴 est une ℂ-algèbre sans unité, il n'y a
  pas de structure de ℂ-espace vectoriel canonique sur Hom_𝐴(𝑋,𝑌) [...] l'on y
  remédie en introduisant l'algèbre unitaire Ã = 𝐴 ⊕ ℂ·1_𝐴 [...] Si 𝑋 et 𝑌 sont
  deux 𝐴-modules et aussi des ℂ-espaces vectoriels, ils deviennent naturellement
  des Ã-modules unitaires et l'on a Hom_Ã(𝑋,𝑌) = Hom_𝐴(𝑋,𝑌) ∩ Hom_ℂ(𝑋,𝑌)". So the
  relevant objects are `A`-modules that are also vector spaces, with linear maps
  that intertwine the action. The vector-space structure is separate data, as
  in this module and the bridge.
- B.II (Lemme de Schur), printed p. 272 / PDF p. 278: "Soit 𝐴 une ℂ-algèbre (que
  l'on ne suppose pas forcément unitaire)"; "Théorème. Soit 𝑀 un 𝐴-module simple et
  un ℂ-espace vectoriel"; in the proof, "quitte à remplacer 𝐴 par Ã = 𝐴 ⊕ ℂ1_𝐴 où
  comme dans la section I.2.1 on ajoute une unité à 𝐴, on peut supposer que 𝐴 est
  une algèbre unitaire et 𝑀 un 𝐴-module unitaire", then "Comme ker 𝑓 et Im 𝑓 sont
  des sous-modules de 𝑀". This is the motivating use: subspaces stable under the
  action, and the stable kernel and image of a linear intertwiner. Nothing from
  B.II is formalized here.

Author errata: registered `renard-2010-corrections-complements`, file
`/home/taskhub/pilot/literature/Renard — Représentations des groupes réductifs p-adiques- corrections et compléments (2010 edition errata).pdf`,
SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`
(checked). Worker 277 read PDF pp. 18–19. The entry for the 2010 edition's p. 314
(PDF pp. 18–19) reads "dans le théorème, il faut supposer que M est en outre un
ℂ-espace vectoriel, car A n'a pas d'unité. On le précise d'ailleurs dans les
hypothèses, et l'on remarque pour la démonstration que l'on peut se ramener au
cas où A est unitaire, ainsi que le module M, en considérant l'algèbre
Ã = A ⊕ ℂ1A comme en I.2.1." The 2026 text quoted above already contains this
correction. It supports keeping the vector-space structure `Module k M` separate
from the `A`-action. This was a targeted check, not an exhaustive reading of the
errata. The 2026 edition governs.

Provenance: **derived**. The source states the conventions (possibly nonunital
algebras and modules; modules that are also vector spaces) and uses submodules,
kernels, images and quotient modules without giving a formal interface. Every
declaration here is derived implementation content that realizes those
conventions for actual vector subspaces. None is a verbatim assertion of Renard,
and the extra generality (commutative ring `k` and the declaration list below) is
not attributed to the source. The mathematics is elementary: a subspace stable
under every `ρ a` carries the restricted and quotient actions, and the stable
subspaces form a complete sublattice of all subspaces.

## Hypotheses, universes and the source-facing interface

All declarations are in the namespace `Langlands.Algebra`. The general variables
are

```text
{k : Type u} {A : Type v} {M : Type w} {N : Type x} {P : Type y}
[CommRing k] [NonUnitalRing A] [Module k A]
[AddCommGroup M] [Module k M]   (and the same for N and P)
ρ : A →ₙₐ[k] Module.End k M,  σ : A →ₙₐ[k] Module.End k N,  τ : A →ₙₐ[k] Module.End k P
```

- The universes `u` (scalars), `v` (algebra), `w`, `x`, `y` (source, target and
  third space) are independent. `CompatibleSubmodule ρ` lives in `Type w`, and
  `IsStableSubmodule` has level parameters `u v w`. `N` and `P` occur only from
  the section on kernels and images onward.
- `A` is never assumed commutative or unital. No action unit law, nondegeneracy,
  finite dimension or nontriviality is assumed. The zero subspace, the zero
  quotient and the zero space are allowed.
- The action is the actual Mathlib homomorphism type `A →ₙₐ[k] Module.End k M`. No
  type alias is introduced.
- **Commutative-ring extension.** The source has a field (`ℂ`). Here `k` is any
  commutative ring. A ring rather than a semiring is used because Mathlib's
  quotient `M ⧸ S` needs subtraction. No construction uses inverses in `k`. The
  field case is checked in section `FieldInterface` and the complex case in
  section `ComplexZero` (below).
- **Complete source-facing interface.** For a field `K`, the source's associative,
  possibly noncommutative and nonunital `K`-algebra with bilinear multiplication is

  ```text
  [Field K] [NonUnitalRing A] [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
  ```

  with `K`-vector spaces `[AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]`
  of arbitrary dimension, in the independent universes `u v w x`. The last two
  class assumptions on `A` make multiplication `K`-bilinear. No construction here
  uses them, so the general declarations omit them. This does not mean that a
  homomorphism `ρ` forces bilinearity on `A`, and nothing here asserts or derives
  `IsScalarTower k A A` or `SMulCommClass k A A`.
- Imports: the bridge `Langlands.Algebra.CompatibleNonUnitalAction` (which imports
  `Langlands.Algebra.NonUnitalModule`); `Mathlib.Algebra.Module.Submodule.Invariant`
  (`Module.End.invtSubmodule`); `Mathlib.LinearAlgebra.DFinsupp`
  (`Submodule.mem_iSup_iff_exists_finsupp`); `Mathlib.LinearAlgebra.Quotient.Basic`
  (quotients, `mkQ`, `mapQ`, `liftQ`); `Mathlib.Order.Hom.CompleteLattice`
  (`CompleteLatticeHom`); `Mathlib.Basic.Complex.Basic` (only for the `ℂ` examples).

## 1. The stability predicate

`IsStableSubmodule ρ S : Prop` (a `def`, for `S : Submodule k M`) is

```text
∀ (a : A) (m : M), m ∈ S → ρ a m ∈ S
```

exactly the predicate of the task. The inspected type is
`{k : Type u} → {A : Type v} → {M : Type w} → [CommRing k] → [NonUnitalRing A] →
[Module k A] → [AddCommGroup M] → [Module k M] → (A →ₙₐ[k] Module.End k M) →
Submodule k M → Prop`, and the inspected body is `∀ (a : A), ∀ m ∈ S, (ρ a) m ∈ S`.

Reformulations, each proved by unfolding the definitions:

- `isStableSubmodule_iff_le_comap`: `IsStableSubmodule ρ S ↔ ∀ a, S ≤ S.comap (ρ a)`;
- `isStableSubmodule_iff_map_le`: `↔ ∀ a, S.map (ρ a) ≤ S`
  (by `Submodule.map_le_iff_le_comap`);
- `isStableSubmodule_iff_mem_invtSubmodule`: `↔ ∀ a, S ∈ Module.End.invtSubmodule (ρ a)`.
  So stability under `ρ` is membership in Mathlib's sublattice of invariant
  subspaces of every `ρ a`.

Closure lemmas (namespace `IsStableSubmodule`): `bot`, `top`, `inf`, `sup` (by the
`bot_mem`, `top_mem`, `inf_mem`, `sup_mem` of the sublattice
`Module.End.invtSubmodule (ρ a)`), `sInf` (by `Submodule.mem_sInf`) and `sSup`
(by `sSup_le` and monotonicity of `Submodule.comap`), for an arbitrary set of
stable subspaces.

## 2. Bundled stable subspaces

`CompatibleSubmodule ρ` is a structure extending the actual `Submodule k M` by the
field

```text
action_mem' : ∀ (a : A) (m : M), m ∈ carrier → ρ a m ∈ carrier
```

(the pattern of Mathlib's `LieSubmodule`). Its projection
`CompatibleSubmodule.toSubmodule` is the faithful coercion to `Submodule k M`
(registered with `attribute [coe]`, and as a `CoeOut` instance).

Instances: `SetLike (CompatibleSubmodule ρ) M` (carrier = carrier of the underlying
subspace); `PartialOrder` via `PartialOrder.ofSetLike`, i.e. inclusion of
carriers; `AddSubgroupClass` and `SMulMemClass … k M`.

Basic declarations:

- `coe_toSubmodule`, `mem_toSubmodule`, `mem_carrier`: the underlying subspace has
  the same carrier and the same membership (`rfl`).
- `ofStable S hS`: bundles `S : Submodule k M` with `hS : IsStableSubmodule ρ S`;
  `ofStable_toSubmodule`, `mem_ofStable`.
- `isStable : IsStableSubmodule ρ S.toSubmodule`, `action_mem a hm : ρ a m ∈ S`,
  `le_comap_action a : S.toSubmodule ≤ S.toSubmodule.comap (ρ a)`.
- `toSubmodule_injective` (by `cases` and `congr`; the stability field is a
  proposition), `toSubmodule_inj`.
- `ext`: extensionality by membership (`SetLike.ext`).
- `toSubmodule_le_toSubmodule`, `toSubmodule_lt_toSubmodule`: the order is the
  inclusion order of the underlying subspaces (`Iff.rfl`).
- `exists_toSubmodule_eq_iff S`: a subspace underlies a bundled stable subspace iff
  it is stable.

## 3. The complete lattice and its carriers

The operations are defined by applying `ofStable` to the corresponding operation
of `Submodule k M`, with the closure lemmas of section 1:

| Operation | Instance | Underlying subspace | Carrier |
| --- | --- | --- | --- |
| `⊥` | `Bot` | `⊥` | `{0}` (`mem_bot`: `m ∈ ⊥ ↔ m = 0`) |
| `⊤` | `Top` | `⊤` | all of `M` (`mem_top`) |
| `S ⊓ T` | `Min` | `S ⊓ T` | intersection (`mem_inf`) |
| `S ⊔ T` | `Max` | `S ⊔ T` | `{y + z ∣ y ∈ S, z ∈ T}` (`mem_sup`) |
| `sInf s` | `InfSet` | `sInf (toSubmodule '' s)` | intersection of all members; `M` if `s = ∅` (`mem_sInf`, `mem_iInf`) |
| `sSup s` | `SupSet` | `sSup (toSubmodule '' s)` | span of the union, i.e. the finite sums of vectors of the members; `{0}` if `s = ∅` (`sSup_toSubmodule_eq_span`, `iSup_toSubmodule_eq_span`, `mem_iSup_iff_exists_finsupp`) |

The `CompleteLattice (CompatibleSubmodule ρ)` instance is Mathlib's
`Function.Injective.completeLattice` along `toSubmodule_injective`. It reuses the
inclusion order and the operations above, so it is the lattice of the actual
`Submodule k M` restricted to stable subspaces; no abstract subobject category is
introduced. Preservation by forgetting:

- `bot_toSubmodule`, `top_toSubmodule`, `inf_toSubmodule`, `sup_toSubmodule`,
  `sInf_toSubmodule`, `sSup_toSubmodule`: by `rfl`;
- `sInf_toSubmodule_eq_iInf`, `sSup_toSubmodule_eq_iSup`: the same as indexed
  infima and suprema (`sInf_image`, `sSup_image`);
- `toSubmoduleHom : CompleteLatticeHom (CompatibleSubmodule ρ) (Submodule k M)`:
  forgetting is an actual complete lattice homomorphism (both laws `rfl`), with
  `toSubmoduleHom_apply`;
- `iInf_toSubmodule`, `iSup_toSubmodule`: indexed infima and suprema
  (`map_iInf`, `map_iSup` of `toSubmoduleHom`).

The carrier lemmas for suprema use `Submodule.span_iUnion₂`, `Submodule.iSup_eq_span`
and `Submodule.mem_iSup_iff_exists_finsupp`.

## 4. Stable subspaces are not stable additive subgroups

The published `Langlands.Algebra.NonUnitalSubmodule A M` (stable additive
subgroups of an ambient `NonUnitalModule A M`) is a different notion.
`S.toNonUnitalSubmodule` is the stable additive subgroup underlying `S` for the
ambient action `NonUnitalModule.ofLinearEndHom ρ`, which is selected by `letI` in
its statement. Lemmas: `mem_toNonUnitalSubmodule` (same membership),
`toNonUnitalSubmodule_le_iff` (same order), `toNonUnitalSubmodule_injective`.

This map is **not** surjective in general. The regression in section `ComplexZero`
proves this for the zero action `0 : ℂ →ₙₐ[ℂ] Module.End ℂ ℂ`: the additive
subgroup `AddSubgroup.zmultiples 1 = ℤ·1 ⊆ ℂ` is stable, but if it underlay some
`S`, then `Complex.I = Complex.I • 1 ∈ S`, so `Complex.I = n • 1` for an integer
`n`. Comparing imaginary parts gives `1 = 0`.

## 5. Restricted and quotient actions

Namespace `CompatibleSubmodule`; `S : CompatibleSubmodule ρ`. The carrier types are
the actual Mathlib types `↥S.toSubmodule` (subtype) and `M ⧸ S.toSubmodule`
(quotient module).

**Restriction.** `S.restrictAction : A →ₙₐ[k] Module.End k S.toSubmodule` sends `a`
to Mathlib's `(ρ a).restrict (S.isStable a)`. Each homomorphism law (`map_smul`,
`map_zero`, `map_add`, `map_mul`) is the corresponding law of `ρ` evaluated at the
underlying vector (linear-map extensionality and `Subtype.ext`). Laws:

- `restrictAction_apply_coe` (simp): `↑(S.restrictAction a m) = ρ a ↑m`;
- `restrictAction_apply`: `S.restrictAction a m = ⟨ρ a m, _⟩`;
- `restrictAction_eq_restrict`: it is `(ρ a).restrict _`.

**Quotient.** `S.quotientAction : A →ₙₐ[k] Module.End k (M ⧸ S.toSubmodule)` sends
`a` to Mathlib's `S.toSubmodule.mapQ S.toSubmodule (ρ a) (S.le_comap_action a)`.
Well-definedness is the hypothesis of `mapQ`, namely stability. It is also
recorded elementwise as:

- `action_sub_mem`: `m - m' ∈ S → ρ a m - ρ a m' ∈ S` (linearity of `ρ a` and
  stability);
- `mkQ_action_eq_of_mkQ_eq`: if `S.mkQ m = S.mkQ m'` then
  `S.mkQ (ρ a m) = S.mkQ (ρ a m')`.

The homomorphism laws are proved with `Submodule.linearMap_qext` (linear maps out
of a quotient agree if they agree after `mkQ`), reducing each to the law of `ρ`.
Laws:

- `quotientAction_apply_mkQ`: `S.quotientAction a (S.mkQ m) = S.mkQ (ρ a m)`, the
  task's equation (`rfl`);
- `quotientAction_apply_mk` (simp): the same for `Submodule.Quotient.mk`;
- `quotientAction_eq_mapQ`, `quotientAction_comp_mkQ`
  (`S.quotientAction a ∘ₗ S.mkQ = S.mkQ ∘ₗ ρ a`, by `Submodule.mapQ_mkQ`);
- `eq_quotientAction`: any endomorphism of `M ⧸ S` satisfying the quotient
  formula equals `S.quotientAction a` (uniqueness, by `Submodule.linearMap_qext`).

**Inclusion and projection as linear intertwiners** (the bridge's
`LinearIntertwiner`):

- `S.subtypeIntertwiner : LinearIntertwiner S.restrictAction ρ`, with underlying
  linear map the actual `S.toSubmodule.subtype`. The intertwining equation holds
  by `rfl`. Lemmas: `subtypeIntertwiner_apply`, `subtypeIntertwiner_toLinearMap`,
  `subtype_restrictAction`, `subtype_comp_restrictAction`.
- `S.mkQIntertwiner : LinearIntertwiner ρ S.quotientAction`, with underlying linear
  map the actual `S.toSubmodule.mkQ`. Again the equation holds by `rfl`. Lemmas:
  `mkQIntertwiner_apply`, `mkQIntertwiner_toLinearMap`, `mkQ_action`.

## 6. The corresponding ambient actions through the bridge

These use the bridge's `NonUnitalModule.ofLinearEndHom`, `ofLinearEndHom_isScalarTower`,
`ofLinearEndHom_smulCommClass` and `LinearIntertwiner.toNonUnitalModuleHom`. No
replacement ambient category is introduced.

- `S.restrictNonUnitalModule : NonUnitalModule A S.toSubmodule` and
  `S.quotientNonUnitalModule : NonUnitalModule A (M ⧸ S.toSubmodule)` are the
  published ambient actions `ofLinearEndHom S.restrictAction` and
  `ofLinearEndHom S.quotientAction`. They are `abbrev`s, **not** instances.
- `restrictNonUnitalModule_smul_coe`: `↑(a • m) = ρ a ↑m`, and
  `quotientNonUnitalModule_smul_mk`: `a • mk m = mk (ρ a m)`, both under the
  corresponding `letI` (`rfl`). So the ambient actions have the same underlying
  maps as `restrictAction` and `quotientAction`.
- Separate scalar compatibility: `restrictNonUnitalModule_isScalarTower`,
  `restrictNonUnitalModule_smulCommClass`, `quotientNonUnitalModule_isScalarTower`,
  `quotientNonUnitalModule_smulCommClass` (the bridge adapters).
- `S.subtypeNonUnitalModuleHom : NonUnitalModuleHom A S.toSubmodule M` and
  `S.mkQNonUnitalModuleHom : NonUnitalModuleHom A M (M ⧸ S.toSubmodule)` are the
  published ambient intertwiners `toNonUnitalModuleHom` of the two linear
  intertwiners, for the actions `restrictNonUnitalModule`, `ofLinearEndHom ρ` and
  `quotientNonUnitalModule`. `subtypeNonUnitalModuleHom_apply` and
  `mkQNonUnitalModuleHom_apply` show that their underlying maps are the subtype
  inclusion and `S.mkQ`.

Action selection follows the bridge's documented convention. Statements select
the action with `letI`. The published instance `NonUnitalModule.actionSMul` has
priority 1200, so under such a `letI` the notation `a • m` uses the specified
action. Two consequences:

- When `k = A` (as for `ℂ` acting on itself), `c • m` written under such a `letI`
  denotes the original action, not scalar multiplication. The general statements
  are elaborated with distinct variables `k` and `A`, so instantiating them keeps
  the `Module k` scalar action. The last example of section `ComplexZero` checks
  this: under `restrictNonUnitalModule` for the zero action on `⊤ ⊆ ℂ`, `1 • ⟨1, _⟩`
  is `0`, while without the `letI` it is the nonzero scalar multiple.
- Two actions on the same carrier should not be made local simultaneously.
  `subtypeNonUnitalModuleHom` and `mkQNonUnitalModuleHom` use two `letI`s on
  different carrier types.

## 7. Kernels, images, inverse and direct images

Here `f : LinearIntertwiner ρ σ`, `g : LinearIntertwiner σ τ`. Each object is the
corresponding Mathlib subspace bundled with `ofStable`. Its stability proof uses
the intertwining equation `f (ρ a m) = σ a (f m)`.

- `LinearIntertwiner.ker f : CompatibleSubmodule ρ`, underlying
  `LinearMap.ker f.toLinearMap` (`ker_toSubmodule`; `mem_ker`: `m ∈ f.ker ↔ f m = 0`).
  Stability: `f (ρ a m) = σ a (f m) = σ a 0 = 0`.
- `LinearIntertwiner.range f : CompatibleSubmodule σ`, underlying
  `LinearMap.range f.toLinearMap` (`range_toSubmodule`; `mem_range`:
  `n ∈ f.range ↔ ∃ m, f m = n`; `mem_range_self`). Stability:
  `σ a (f m) = f (ρ a m)`.
- `CompatibleSubmodule.comap f T : CompatibleSubmodule ρ` (written `T.comap f`),
  underlying `T.toSubmodule.comap f.toLinearMap` (`comap_toSubmodule`; `mem_comap`:
  `m ∈ T.comap f ↔ f m ∈ T`).
- `CompatibleSubmodule.map f S : CompatibleSubmodule σ` (written `S.map f`),
  underlying `S.toSubmodule.map f.toLinearMap` (`map_toSubmodule`; `mem_map`:
  `n ∈ S.map f ↔ ∃ m ∈ S, f m = n`).
- `map_le_iff_le_comap` and `gc_map_comap` (a Galois connection; from
  `Submodule.map_le_iff_le_comap`), `map_mono`, `comap_mono`.
- Identity and composition: `comap_id`, `comap_comp`
  (`U.comap (g.comp f) = (U.comap g).comap f`), both `rfl`; `map_id`, `map_comp`
  (`S.map (g.comp f) = (S.map f).map g`), by `toSubmodule_injective` and
  `Submodule.map_id`, `Submodule.map_comp`.
- `ker_eq_comap_bot`, `range_eq_map_top`; `ker_mkQIntertwiner`
  (`S.mkQIntertwiner.ker = S`, by `Submodule.ker_mkQ`) and
  `range_subtypeIntertwiner` (`S.subtypeIntertwiner.range = S`, by
  `Submodule.range_subtype`).

## 8. Restriction and descent of linear intertwiners

Namespace `LinearIntertwiner`. All constructions have the actual Mathlib linear maps
as their underlying maps (the `_toLinearMap` lemmas, all `rfl`).

- `f.restrict h : LinearIntertwiner S.restrictAction T.restrictAction` for
  `h : S ≤ T.comap f`. Underlying map: `f.toLinearMap.restrict _`. Laws:
  `restrict_apply_coe` (`↑(f.restrict h m) = f ↑m`), `restrict_toLinearMap`,
  `subtypeIntertwiner_comp_restrict`, `restrict_id`, `restrict_comp` (all `rfl`).
- `f.domRestrict S : LinearIntertwiner S.restrictAction σ := f.comp S.subtypeIntertwiner`;
  `domRestrict_apply`, `domRestrict_toLinearMap` (`= f.toLinearMap.domRestrict S`).
- `f.codRestrict T h : LinearIntertwiner ρ T.restrictAction` for `h : ∀ m, f m ∈ T`.
  Underlying map: `LinearMap.codRestrict`. Laws: `codRestrict_apply_coe`,
  `codRestrict_toLinearMap`, `subtypeIntertwiner_comp_codRestrict`.
- `f.rangeRestrict : LinearIntertwiner ρ f.range.restrictAction`, the corestriction
  to the stable image; `rangeRestrict_toLinearMap` (`= f.toLinearMap.rangeRestrict`),
  `subtypeIntertwiner_comp_rangeRestrict`.
- `f.mapQ S T h : LinearIntertwiner S.quotientAction T.quotientAction` for
  `h : S ≤ T.comap f`. Underlying map:
  `S.toSubmodule.mapQ T.toSubmodule f.toLinearMap h`. The intertwining equation is
  proved on representatives (`Submodule.Quotient.induction_on`) from that of `f`.
  Laws: `mapQ_apply_mk` (simp), `mapQ_apply_mkQ`
  (`f.mapQ S T h (S.mkQ m) = T.mkQ (f m)`), `mapQ_toLinearMap`,
  `mapQ_comp_mkQIntertwiner`, `mapQ_id` (`(id ρ).mapQ S S h = id S.quotientAction`)
  and `mapQ_comp` (`(g.comp f).mapQ S U _ = (g.mapQ T U _).comp (f.mapQ S T _)`).
  The last two are proved by extensionality and induction on quotient
  representatives.
- `f.liftQ S h : LinearIntertwiner S.quotientAction σ` for `h : S ≤ f.ker`.
  Underlying map: `S.toSubmodule.liftQ f.toLinearMap h`; intertwining as for
  `mapQ`. Laws: `liftQ_apply_mk` (simp), `liftQ_apply_mkQ`
  (`f.liftQ S h (S.mkQ m) = f m`), `liftQ_toLinearMap`, `liftQ_comp_mkQIntertwiner`
  and `comp_liftQ` (`g.comp (f.liftQ S h) = (g.comp f).liftQ S _`).

The `id` and `comp` here are the bridge's `LinearIntertwiner.id` and
`LinearIntertwiner.comp`. All the lemmas above are intrinsic construction laws.
None is an exactness or isomorphism theorem.

## 9. The zero original action

General hypotheses as above, with `0 : A →ₙₐ[k] Module.End k M`:

- `isStableSubmodule_zero S`: every subspace is stable, since `0 ∈ S`;
- `CompatibleSubmodule.zeroOrderIso`: an order isomorphism between the bundled
  stable subspaces and `Submodule k M` (inverse `ofStable`; both round trips `rfl`);
- `CompatibleSubmodule.restrictAction_zero`, `CompatibleSubmodule.quotientAction_zero`:
  the restricted and quotient actions are `0`;
- `CompatibleSubmodule.bot_ne_top_zero`: for `[Nontrivial M]`, `⊥ ≠ ⊤`.

Section `ComplexZero` checks `A = k = M = ℂ` with
`0 : ℂ →ₙₐ[ℂ] Module.End ℂ ℂ` by `example`s:

- every complex subspace of `ℂ` is stable;
- the restricted and quotient original actions are `0`;
- the original action is distinct from scalar multiplication: `0 1 1 = 0` while
  `(1 : ℂ) • (1 : ℂ) ≠ 0`;
- the zero subspace `⊥` and the zero quotient `ℂ ⧸ ⊤` are permitted (both
  subsingletons; `Submodule.Quotient.subsingleton_iff`);
- `⊥ ≠ ⊤` on the nonzero space `ℂ`;
- the action-selection check of section 6;
- the non-surjectivity of `toNonUnitalSubmodule` of section 4.

## 10. Field specialization

Section `FieldInterface` takes `[Field K] [NonUnitalRing A] [Module K A]
[IsScalarTower K A A] [SMulCommClass K A A]`, `K`-vector spaces `M`, `N` in
universes `u v w x`, and `ρ`, `σ`. Its `example`s check, at this exact interface:
the complete lattice and the preservation of `sSup`/`sInf`; the restricted and
quotient action formulas; the scalar compatibility of both ambient actions; the
`ker`/`range` membership formulas; and the application formulas of `mapQ`,
`restrict` and `liftQ`.

## Excluded content

The following are separate obligations of the surrounding Renard development and
are neither assumed as fields nor proved here:

- the unitization `Ã = A ⊕ k·1` and its lattice equivalence or action comparison;
- recovery of a canonical scalar structure for nondegenerate modules;
- simplicity, and comparisons between simplicity for stable subspaces and for
  stable additive subgroups; Schur's lemma;
- isomorphism theorems, exactness and categorical equivalences;
- finite generation, noetherian conditions and localization.
