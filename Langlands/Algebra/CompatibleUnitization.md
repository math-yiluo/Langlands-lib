# The unitized action of a compatible nonunital algebra action

Author: Worker 734 read the cited passages, designed and implemented this module
and wrote this note. No draft code by another worker was reused. The task
(`2e6ba45d-844d-458a-aba5-3b706694aae6`, published by Worker 6) suggested
building the action from `Unitization.lift` with `Module.compHom`.

The module `Langlands/Algebra/CompatibleUnitization.lean` (namespace
`Langlands.Algebra.CompatibleUnitization`) adjoins a unit to a possibly
noncommutative and nonunital `k`-algebra `A` that acts on a `k`-module `M`
through an actual homomorphism `ρ : A →ₙₐ[k] Module.End k M`. It uses Mathlib's
`Unitization k A` with its actual unital `k`-algebra structure. The module
provides:

1. the unitized action, both as the algebra homomorphism `Unitization.lift ρ`
   and as a unital `Module (Unitization k A) M`, with its formula and its
   uniqueness;
2. the correspondence between unitized linear maps and `k`-linear maps
   intertwining the original actions, the intersection `Hom_A ∩ Hom_k` of I.2.1;
3. the endomorphism `k`-algebra of the given action, as the actual centralizer of
   `Set.range ρ`, and its `k`-algebra equivalence with
   `Module.End (Unitization k A) M`;
4. the zero original action, in general and on the nonzero complex line `ℂ`
   with `A = ℂ`.

Stable subspaces and quotients (part 3 of the task) are **not** in this module.
They need the stable-subspace interface `Langlands.Algebra.CompatibleSubmodule`
of task `225c0c50-f2f1-4da9-9cbd-b70bd64c5b33`, and are in the separate module
`Langlands/Algebra/CompatibleUnitizationSubmodule.lean`, which imports both.

The module imports the published bridge `Langlands.Algebra.CompatibleNonUnitalAction`
by Lean name and reuses its `LinearIntertwiner`, `LinearIntertwiner.id`,
`LinearIntertwiner.comp` and `NonUnitalModule.ofLinearEndHom`.

## Original source and provenance

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated **9 July 2026**. This is the registered source
`renard-2026-representations-groupes-reductifs-padiques`, at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Printed page = PDF page minus 6. Worker 734 read these passages directly:

- Chapter I, notation and conventions, printed pp. 5–6 / PDF pp. 11–12. Rings are
  not assumed unital, and modules over a unital ring are not assumed unital a
  priori.
- I.2.1, printed p. 14 / PDF p. 20. For a `ℂ`-algebra `A` without unit, Renard
  introduces the unital algebra `Ã = A ⊕ ℂ·1_A`, where `1_A` is decreed to be the
  unit of `Ã` ("ceci détermine une unique structure d'algèbre sur Ã"). If `X`
  and `Y` are `A`-modules and also `ℂ`-vector spaces, "ils deviennent
  naturellement des Ã-modules unitaires et l'on a
  `Hom_Ã(X,Y) = Hom_A(X,Y) ∩ Hom_ℂ(X,Y)`".
- B.II, printed p. 272 / PDF p. 278. The proof of Schur's lemma opens by
  replacing `A` with `Ã = A ⊕ ℂ1_A` "comme dans la section I.2.1". After that,
  `A` may be assumed unital and `M` a unital module.

Supplementary errata: the registered `renard-2010-corrections-complements`
(SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`).
PDF pp. 18–19 were checked. The item for the Schur lemma (2010 p. 314) asks that
`M` be a `ℂ`-vector space and that one reduce to `Ã` as in I.2.1. The 2026 text
already has this. No entry concerning I.2.1 was found. The 2026 edition governs.

Provenance: every declaration here is **derived implementation content** that
realizes the unitization of I.2.1 and the reduction at the start of B.II. Renard
states the construction and the Hom formula in prose. The formula
`x • m = x.fst • m + ρ x.snd m`, the uniqueness statements, the named adapters,
the `k`-linear equivalence of Hom spaces, the centralizer description and the
zero-action checks are not verbatim assertions of the author. Three choices are
ours:

- the source's "`A`-module that is also a `ℂ`-vector space" is represented by
  an actual homomorphism `ρ` into `k`-linear endomorphisms, as in the bridge;
- the scalar field `ℂ` is generalized to a commutative ring `k`;
- `Hom_A ∩ Hom_k` is represented by the `k`-submodule `intertwiners ρ σ` of
  `M →ₗ[k] N`.

Two further statements in I.2.1 are not claimed: the tensor-product formula, and
the equality (I.2.1.2) `Hom_Ã = Hom_A` for canonical scalar structures on
nondegenerate modules over idempotented algebras.

## Hypotheses, universes and action choices

Universes are independent: `k : Type u`, `A : Type v`, `M : Type w`,
`N : Type x`, `P : Type y`. No space is assumed finite-dimensional, nontrivial or
nondegenerate. `A` is never assumed commutative or unital, and `ρ` is arbitrary,
including `0`.

The scalar ring is a **commutative ring** `k`, which extends the source's field
`ℂ`. With it, `Unitization k A` is a `Ring`, so quotients are available for the
later subspace module. The unitized constructions assume

```text
[CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
[AddCommGroup M] [Module k M]   (and the same for N, P)
```

The two class assumptions on `A` make multiplication `k`-bilinear. Mathlib needs
them for the `k`-algebra `Unitization k A` (`Unitization.instAlgebra`). The
declarations that do not mention the unitization (`intertwiners`,
`mem_intertwiners`, `id_mem_intertwiners`, `comp_mem_intertwiners`,
`intertwinersEquiv` and its lemmas, `centralizer`, `mem_centralizer_iff`,
`toSubmodule_centralizer`, `coe_algebraMap_centralizer`) assume only
`[CommRing k] [NonUnitalRing A] [Module k A]` and the module assumptions.

The section `Field` checks the source-facing specialization: a field `K`, a
possibly noncommutative and nonunital `K`-algebra `A` with
`[IsScalarTower K A A] [SMulCommClass K A A]`, and `K`-vector spaces `V : Type w`
and `W : Type x`. Three `example`s instantiate the action formula and its
restrictions, `linearMapEquiv` and `endAlgEquiv` there.

**Action selection.** `module ρ` is a definition marked `@[instance_reducible]`,
**not** an instance. Every statement installs it locally with
`letI := module ρ`, and the target with `letI := module σ`. So no global instance
can override another chosen action, for instance when `A = k = M = ℂ`. Since
`Unitization k A` is a type distinct from `k` and from `A`:

- `x • m` with `x : Unitization k A` uses the chosen unitized action;
- `c • m` with `c : k` uses the given `Module k M`.

The named adapters `isScalarTower ρ`, `smulCommClass ρ` and `smulCommClass' ρ`
are theorems stated under `letI := module ρ`, and are installed with `letI`
where needed. The same carrier can carry two different unitized actions (for
`M = N` with `ρ ≠ σ`). The generic statements use distinct variables `M`, `N`,
`P`, and specializing them substitutes the elaborated instance terms.

## 1. The unitized action

Section `Action`; `ρ : A →ₙₐ[k] Module.End k M`.

- `endHom ρ : Unitization k A →ₐ[k] Module.End k M` is defined as
  `Unitization.lift ρ`, the actual unital algebra homomorphism of Mathlib's
  universal property.
- `endHom_apply`: `endHom ρ x m = x.fst • m + ρ x.snd m`. This holds by `rfl`,
  since `Unitization.lift ρ x = algebraMap k _ x.fst + ρ x.snd`.
- `endHom_inr` (simp): `endHom ρ a = ρ a` for `a : A` coerced by `inr`. Proof:
  linear-map extensionality, `endHom_apply`, `fst_inr`, `snd_inr`,
  `zero_smul`, `zero_add`.
- `endHom_inl` (simp): `endHom ρ (inl c) = algebraMap k (Module.End k M) c`, by
  `AlgHom.commutes`.
- `lift_symm_endHom` (simp): `Unitization.lift.symm (endHom ρ) = ρ`. The
  restriction along `A → Unitization k A` recovers `ρ`, by
  `Unitization.lift.symm_apply_apply`.
- `endHom_unique`: every `φ : Unitization k A →ₐ[k] Module.End k M` with
  `φ a = ρ a` for all `a : A` equals `endHom ρ`. This is uniqueness from the
  universal property, via `Unitization.algHom_ext''`.
- `module ρ : Module (Unitization k A) M := Module.compHom M (endHom ρ).toRingHom`,
  the actual unital module structure.
- `smul_def`: `x • m = endHom ρ x m`, and `smul_eq`:
  `x • m = x.fst • m + ρ x.snd m`. Both hold by `rfl`.
- `inr_smul` (simp): `(a : Unitization k A) • m = ρ a m`, so restricting to `A`
  gives `ρ`. Proof: `smul_def`, `endHom_inr`.
- `inl_smul` (simp): `inl c • m = c • m`, so the scalar coordinate acts by the
  original scalar action. Proof: `smul_def`, `endHom_inl`,
  `Module.algebraMap_end_apply`.
- `algebraMap_smul` (simp): `algebraMap k (Unitization k A) c • m = c • m`, by
  `AlgHom.commutes`.
- `one_smul`: `(1 : Unitization k A) • m = m`, by `map_one`.
- `ofLinearEndHom_smul_eq_inr_smul`: the bridge's ambient action
  `NonUnitalModule.ofLinearEndHom ρ` is the restriction of the unitized action
  to `A`.
- Named adapters, each stated under `letI := module ρ`:
  - `isScalarTower ρ : IsScalarTower k (Unitization k A) M`, because
    `endHom ρ (c • x) = c • endHom ρ x` (`map_smul`);
  - `smulCommClass ρ : SMulCommClass k (Unitization k A) M`;
  - `smulCommClass' ρ : SMulCommClass (Unitization k A) k M`.

  The last two hold because each `endHom ρ x` is `k`-linear. `smulCommClass'`
  supplies the `k`-module structure on unitized linear maps.
  `isScalarTower` and `smulCommClass'` supply the `k`-algebra structure on
  `Module.End (Unitization k A) M`.
- `module_unique ρ h hinl hinr`: let `h : Module (Unitization k A) M` be any
  unital module structure in which `inl c` acts by `c • m` and `a` acts by
  `ρ a`. Then `h = module ρ`. Proof: `Module.ext'`, then decompose
  `x = inl x.fst + inr x.snd` (`inl_fst_add_inr_snd_eq`) and use `add_smul`,
  `hinl` and `hinr`.
- `module_unique_of_isScalarTower ρ h hT hinr`: the same conclusion when the
  scalar hypothesis is replaced by `IsScalarTower k (Unitization k A) M` for `h`.
  Proof: `inl c = algebraMap k _ c = c • 1`, then `smul_assoc` and `one_smul`,
  then `module_unique`.

## 2. Unitized linear maps and intertwiners

Section `Hom`; `ρ : A →ₙₐ[k] Module.End k M`,
`σ : A →ₙₐ[k] Module.End k N` and
`τ : A →ₙₐ[k] Module.End k P`. Unitized linear maps are the actual type
`M →ₗ[Unitization k A] N` under `letI := module ρ; letI := module σ`.

- `intertwiners ρ σ : Submodule k (M →ₗ[k] N)`, with carrier
  `{f | ∀ a m, f (ρ a m) = σ a (f m)}`. This is `Hom_A ∩ Hom_k`: the `k`-linear
  maps that intertwine. Closure under `0`, `+` and `k`-scalars uses that each
  `σ a` is `k`-linear. `mem_intertwiners` gives the membership equation
  (`Iff.rfl`).
- `id_mem_intertwiners`, `comp_mem_intertwiners`.
- `intertwinersEquiv ρ σ : intertwiners ρ σ ≃ LinearIntertwiner ρ σ` identifies
  the submodule with the bridge's structure. Both round trips are `rfl`. Lemmas:
  `intertwinersEquiv_apply`, `intertwinersEquiv_symm_apply_coe`.
- `toLinearMap f : M →ₗ[k] N` is the actual restriction of scalars
  `f.restrictScalars k`, using `isScalarTower ρ` and `isScalarTower σ`.
  `toLinearMap_apply`: same underlying function.
- `toLinearMap_mem_intertwiners f`: `f (ρ a m) = σ a (f m)`. Rewrite both sides
  with `inr_smul` and apply `f.map_smul (inr a) m`.
- `ofLinearMap g hg`, for `g : M →ₗ[k] N` with `hg : g ∈ intertwiners ρ σ`, is
  the unitized linear map with the same function. Its `map_smul'` follows from
  `smul_eq`, `map_add`, `map_smul` and `hg`. `ofLinearMap_apply`: same
  underlying function.
- Round trips `toLinearMap_ofLinearMap` and `ofLinearMap_toLinearMap`, identity
  laws `toLinearMap_id` and `ofLinearMap_id`, and composition laws
  `toLinearMap_comp` and `ofLinearMap_comp`. All are `rfl`.
- `linearMapEquiv ρ σ : (M →ₗ[Unitization k A] N) ≃ₗ[k] intertwiners ρ σ` is the
  `k`-linear equivalence of the actual Hom spaces. The `k`-module on the left is
  Mathlib's `LinearMap.module` with `smulCommClass' σ`. Every field is `rfl`.
  Lemmas: `linearMapEquiv_apply_coe` (underlying map `toLinearMap f`) and
  `linearMapEquiv_symm_apply` (`ofLinearMap g.1 g.2`).
- Bridge form: `toLinearIntertwiner f : LinearIntertwiner ρ σ` and
  `ofLinearIntertwiner f`. Lemmas: application (`toLinearIntertwiner_apply`,
  `ofLinearIntertwiner_apply`), both round trips, identity against
  `LinearIntertwiner.id ρ`, composition against `LinearIntertwiner.comp`. All
  are `rfl`. `linearIntertwinerEquiv ρ σ` bundles them as an equivalence of
  types.

This correspondence is with `k`-linear intertwiners only. No correspondence with
all additive `NonUnitalModuleHom` is claimed. For an arbitrary `ρ` (for example
`ρ = 0`) an additive intertwiner need not be `k`-linear.

## 3. The endomorphism algebra as a centralizer

Section `Centralizer`; `ρ : A →ₙₐ[k] Module.End k M`.

- `centralizer ρ : Subalgebra k (Module.End k M) :=
  Subalgebra.centralizer k (Set.range ρ)`. This is the centralizer of the
  **given** action, not an abstract division algebra, and no Schur conclusion is
  assumed.
- `mem_centralizer_iff`: `f ∈ centralizer ρ ↔ ∀ a m, f (ρ a m) = ρ a (f m)`.
  Proof: `Subalgebra.mem_centralizer_iff` gives `ρ a * f = f * ρ a` for every
  element of the range. Evaluate with `LinearMap.congr_fun` in one direction and
  use `LinearMap.ext` in the other.
- `toSubmodule_centralizer`: `Subalgebra.toSubmodule (centralizer ρ) =
  intertwiners ρ ρ`.
- `coe_algebraMap_centralizer` (simp): the scalar algebra map of the centralizer
  is that of `Module.End k M` (`rfl`).
- `endAlgEquiv ρ : centralizer ρ ≃ₐ[k] Module.End (Unitization k A) M`, under
  `letI := module ρ`, `isScalarTower ρ` and `smulCommClass' ρ`. It sends `f` to
  `ofLinearMap f`, with the inverse given by `toLinearMap`. Every field
  (inverses, multiplication, addition, `commutes'`) is `rfl`.
- Checks: `endAlgEquiv_apply` and `endAlgEquiv_symm_apply` (same underlying
  functions); `endAlgEquiv_apply_eq` (it is `(linearMapEquiv ρ ρ).symm`, the Hom
  correspondence); `endAlgEquiv_mul` (products go to composites `∘ₗ`);
  `endAlgEquiv_one` (`1` goes to `LinearMap.id`); `endAlgEquiv_algebraMap`
  (scalar algebra maps correspond, by `AlgEquiv.commutes`);
  `algebraMap_end_apply` (`algebraMap k (Module.End (Unitization k A) M) c`
  acts by `c • m`).

## 4. The zero original action

Section `ZeroAction`, general hypotheses:

- `endHom_zero_apply`:
  `endHom (0 : A →ₙₐ[k] Module.End k M) x = algebraMap k (Module.End k M) x.fst`;
- `zero_smul_eq`: under `letI := module 0`, `x • m = x.fst • m`;
- `zero_inr_smul`: under `letI := module 0`, `(a : Unitization k A) • m = 0`.
  So `A` still acts by zero.

Section `Complex`, with `A = k = M = ℂ` and `ρ = 0 : ℂ →ₙₐ[ℂ] Module.End ℂ ℂ`:

- `complex_zero_lift_symm_endHom`: the restriction `Unitization.lift.symm` of
  the unitized homomorphism is still `0`;
- `complex_zero_smul`: `x • z = x.fst * z` for `x : Unitization ℂ ℂ` and
  `z : ℂ`, so the unitized action is exactly scalar action by `x.fst`;
- `complex_zero_inr_one_smul`: `((1 : ℂ) : Unitization ℂ ℂ) • 1 = 0` and
  `(1 : Unitization ℂ ℂ) • 1 = 1`. So the algebra unit of `A = ℂ` acts by zero
  and need not act as the identity, while the unit of the unitization does.

## Deferred obligations

The following remain separate obligations:

- part 3 of the task: the order isomorphism between stable `k`-subspaces of `ρ`
  and `Submodule (Unitization k A) M`, and the restricted and quotient
  comparisons. These are in `Langlands/Algebra/CompatibleUnitizationSubmodule.lean`,
  not here;
- the tensor-product formula of I.2.1, and the equality (I.2.1.2) for canonical
  scalar structures on nondegenerate modules;
- simplicity transfer, countable dimension, Schur, separation, finite
  generation and localization.

None of them is assumed or proved here.
