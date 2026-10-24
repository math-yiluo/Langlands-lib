# Congruence and fiber flattening of restricted products

Module `Langlands.LinearAlgebra.RestrictedProduct.Equiv` defines two generic
families of equivalences between Mathlib's algebraic restricted products
`Πʳ i, [R i, A i]_[𝓕]` (the type `RestrictedProduct R A 𝓕` of families
`x : Π i, R i` with `x i ∈ A i` for `𝓕`-eventually all `i`):

1. **Pointwise congruence.** Factorwise equivalences `φ i : R₁ i ≃ R₂ i`
   that eventually restrict to bijections `A₁ i → A₂ i` give an equivalence
   of restricted products. There are plain, additive and linear versions.
2. **Fiber flattening.** For `f : ι → ι₂`, the restricted product over `ι₂` of
   the full products over the fibers of `f` is identified with the restricted
   product over `ι`. There are plain and linear versions.

The module imports only `Mathlib.LinearAlgebra.Pi` (for `Submodule.pi`) and
`Mathlib.Topology.Algebra.RestrictedProduct.Basic` (for `RestrictedProduct`,
`RestrictedProduct.map`, `RestrictedProduct.mapAlong` and the `Module`
instance). It uses no topology. Every index type, factor family, filter and
coefficient semiring is arbitrary, with independent universe levels (each
`Type*`). Nothing is specialized to number fields, finite places or cofinite
filters except the two cofinite specializations `flattenEquiv'` and
`flattenLinearEquiv'`.

All declarations are structural. Each proof is a short well-definedness,
inverse, additivity, scalar or coordinate proof, described below. Every
coordinate lemma is proved by `rfl` and marked `@[simp]`.

## Pointwise congruence

Common variables: an index type `ι`, factor families `R₁ R₂ : ι → Type*` and a
filter `𝓕 : Filter ι`, all implicit.

### `Equiv.restrictedProductCongrRight`

```lean
def Equiv.restrictedProductCongrRight
    {A₁ : (i : ι) → Set (R₁ i)} {A₂ : (i : ι) → Set (R₂ i)}
    (φ : (i : ι) → R₁ i ≃ R₂ i)
    (hφ : ∀ᶠ i in 𝓕, Set.BijOn (φ i) (A₁ i) (A₂ i)) :
    Πʳ i, [R₁ i, A₁ i]_[𝓕] ≃ Πʳ i, [R₂ i, A₂ i]_[𝓕]
```

The forward map is `RestrictedProduct.map (fun i ↦ φ i) _`. Its side condition
`∀ᶠ i in 𝓕, Set.MapsTo (φ i) (A₁ i) (A₂ i)` follows from `hφ` by
`Set.BijOn.mapsTo`. The inverse is `RestrictedProduct.map (fun i ↦ (φ i).symm) _`.
Its side condition `Set.MapsTo (φ i).symm (A₂ i) (A₁ i)` follows from `hφ` by
`Set.BijOn.equiv_symm` and then `Set.BijOn.mapsTo`. The two inverse laws are
checked coordinatewise with `Equiv.symm_apply_apply` and
`Equiv.apply_symm_apply`. Coordinate lemmas:

- `Equiv.restrictedProductCongrRight_apply φ hφ x i :
  Equiv.restrictedProductCongrRight φ hφ x i = φ i (x i)`;
- `Equiv.restrictedProductCongrRight_symm_apply φ hφ y i :
  (Equiv.restrictedProductCongrRight φ hφ).symm y i = (φ i).symm (y i)`.

Only eventual bijectivity on the restricting sets is assumed. Outside an
`𝓕`-large set of indices, `φ i` need not map `A₁ i` into `A₂ i` at all.

### `AddEquiv.restrictedProductCongrRight`

```lean
def AddEquiv.restrictedProductCongrRight
    {S₁ S₂ : ι → Type*} [(i : ι) → SetLike (S₁ i) (R₁ i)] [(i : ι) → SetLike (S₂ i) (R₂ i)]
    [(i : ι) → AddMonoid (R₁ i)] [(i : ι) → AddMonoid (R₂ i)]
    [(i : ι) → AddSubmonoidClass (S₁ i) (R₁ i)] [(i : ι) → AddSubmonoidClass (S₂ i) (R₂ i)]
    {A₁ : (i : ι) → S₁ i} {A₂ : (i : ι) → S₂ i}
    (φ : (i : ι) → R₁ i ≃+ R₂ i)
    (hφ : ∀ᶠ i in 𝓕, Set.BijOn (φ i) (A₁ i) (A₂ i)) :
    (Πʳ i, [R₁ i, A₁ i]_[𝓕]) ≃+ (Πʳ i, [R₂ i, A₂ i]_[𝓕])
```

Here the restricting subsets are additive submonoids given through a
`SetLike`/`AddSubmonoidClass` family, so the restricted products carry
Mathlib's additive monoid structure. The underlying equivalence is
`Equiv.restrictedProductCongrRight (fun i ↦ (φ i).toEquiv) hφ`. Additivity is
checked coordinatewise by `map_add (φ i)`. Coordinate lemmas
`AddEquiv.restrictedProductCongrRight_apply` (`… x i = φ i (x i)`) and
`AddEquiv.restrictedProductCongrRight_symm_apply`
(`(…).symm y i = (φ i).symm (y i)`). This is the only additive helper. The
linear equivalence below uses it.

### `LinearEquiv.restrictedProductCongrRight`

```lean
def LinearEquiv.restrictedProductCongrRight
    {S₁ S₂ : ι → Type*} [(i : ι) → SetLike (S₁ i) (R₁ i)] [(i : ι) → SetLike (S₂ i) (R₂ i)]
    {T : Type*} [Semiring T]
    [(i : ι) → AddCommMonoid (R₁ i)] [(i : ι) → AddCommMonoid (R₂ i)]
    [(i : ι) → Module T (R₁ i)] [(i : ι) → Module T (R₂ i)]
    [(i : ι) → AddSubmonoidClass (S₁ i) (R₁ i)] [(i : ι) → AddSubmonoidClass (S₂ i) (R₂ i)]
    {A₁ : (i : ι) → S₁ i} {A₂ : (i : ι) → S₂ i}
    [(i : ι) → SMulMemClass (S₁ i) T (R₁ i)] [(i : ι) → SMulMemClass (S₂ i) T (R₂ i)]
    (φ : (i : ι) → R₁ i ≃ₗ[T] R₂ i)
    (hφ : ∀ᶠ i in 𝓕, Set.BijOn (φ i) (A₁ i) (A₂ i)) :
    (Πʳ i, [R₁ i, A₁ i]_[𝓕]) ≃ₗ[T] (Πʳ i, [R₂ i, A₂ i]_[𝓕])
```

The hypotheses are exactly those of the source. A semiring `T` acts on the
factors, and the restricting subobjects are closed under addition, zero and
`T`-scalars. These are the hypotheses of Mathlib's `Module T` instance on a
restricted product. Taking `S i = Submodule T (R i)` covers submodule
restrictions; a private probe instantiated the declaration with submodule
families and a principal filter. The underlying additive equivalence is
`AddEquiv.restrictedProductCongrRight (fun i ↦ (φ i).toAddEquiv) _`, with `hφ`
transported unchanged. `T`-linearity is checked coordinatewise by
`map_smul (φ i)`. Coordinate lemmas
`LinearEquiv.restrictedProductCongrRight_apply` (`… x i = φ i (x i)`) and
`LinearEquiv.restrictedProductCongrRight_symm_apply`
(`(…).symm y i = (φ i).symm (y i)`).

## Fiber flattening

All flattening declarations are in namespace `RestrictedProduct`. Common
variables: an index type `ι` with a filter `ℱ`, a factor family `G : ι → Type*`
with restricting sets `C`, an index type `ι₂` with a filter `𝒢`, and a map
`f : ι → ι₂`. For `j : ι₂` the fiber is the subtype `f ⁻¹' {j}`. The source
restricted product is

```
Πʳ j, [Π (i : f ⁻¹' {j}), G i, Set.pi Set.univ (fun (i : f ⁻¹' {j}) => C i)]_[𝒢]
```

so its `j`-th factor is the full product of the `G i` over the fiber of `j`,
restricted to the subset of families whose every coordinate lies in `C i`. A
fiber may be empty or infinite. No finiteness of fibers is assumed.

### `flatten`

```lean
def flatten (C : (i : ι) → Set (G i)) (hf : Filter.Tendsto f ℱ 𝒢) :
    Πʳ j, [Π (i : f ⁻¹' {j}), G i, Set.pi Set.univ (fun (i : f ⁻¹' {j}) => C i)]_[𝒢] →
    Πʳ i, [G i, C i]_[ℱ]
```

The map is `mapAlong _ G f hf (fun i x ↦ x ⟨i, rfl⟩) _`, so it sends `x` to the
family `i ↦ x (f i) ⟨i, rfl⟩`. Here `⟨i, rfl⟩` is `i` as an element of the fiber
over `f i`. The `MapsTo` side condition holds for every `i`: if every
coordinate of `x (f i)` is in the corresponding `C`, then so is the `i`-th
one. Mathlib's `mapAlong` uses `hf` to see that the result is eventually in
`C` along `ℱ`. Coordinate lemma
`flatten_apply C hf x i : flatten C hf x i = x (f i) ⟨i, rfl⟩`.

### `flattenEquiv`

```lean
def flattenEquiv (C : (i : ι) → Set (G i)) (hf : Filter.comap f 𝒢 = ℱ) :
    Πʳ j, [Π (i : f ⁻¹' {j}), G i, Set.pi Set.univ (fun (i : f ⁻¹' {j}) => C i)]_[𝒢] ≃
    Πʳ i, [G i, C i]_[ℱ]
```

The hypothesis is the equality `Filter.comap f 𝒢 = ℱ`: the filter on `ι` is
the pullback of the filter on `ι₂`. The forward map is `flatten C _`. Its
hypothesis `Filter.Tendsto f ℱ 𝒢` is `Filter.tendsto_iff_comap` applied to
the inequality `ℱ ≤ Filter.comap f 𝒢` contained in `hf`. The inverse sends
`y` to `fun j i ↦ y i.val`, that is, it regroups `y` along the fibers. To see
that this lands in the restricted product, `hf` and `Filter.eventually_comap`
turn `∀ᶠ i in ℱ, y i ∈ C i` into: for `𝒢`-eventually all `j`, every `i` with
`f i = j` has `y i ∈ C i`. This is the other inequality
`Filter.comap f 𝒢 ≤ ℱ`. Both inverse laws hold coordinatewise by `rfl`; the
left inverse law first destructures a fiber element as `⟨i, rfl⟩`. Coordinate
lemmas:

- `flatten_equiv_apply C hf x i : flattenEquiv C hf x i = x (f i) ⟨i, rfl⟩`;
- `flatten_equiv_symm_apply C hf y j i : (flattenEquiv C hf).symm y j i = y i.1`
  for `j : ι₂` and `i : f ⁻¹' {j}` (in the Lean statement the bound names are
  `x`, `i`, `j`).

Only `Filter.Tendsto f ℱ 𝒢` (that is, `ℱ ≤ comap f 𝒢`) is needed for the map
`flatten`. The module does not claim that `flatten` is an equivalence under
`Tendsto` alone. The inverse needs the reverse inequality `comap f 𝒢 ≤ ℱ`,
and the equivalence is stated under the equality.

### `flattenEquiv'`

```lean
def flattenEquiv' (C : (i : ι) → Set (G i))
    (hf : Filter.Tendsto f Filter.cofinite Filter.cofinite) :
    Πʳ j, [Π (i : f ⁻¹' {j}), G i, Set.pi Set.univ (fun (i : f ⁻¹' {j}) => C i)] ≃
    Πʳ i, [G i, C i]
```

This is the cofinite specialization: both restricted products are over
`Filter.cofinite`. It is `flattenEquiv C h` with
`h : Filter.comap f Filter.cofinite = Filter.cofinite` obtained by
`le_antisymm` from Mathlib's `Filter.comap_cofinite_le f` and from
`Filter.map_le_iff_le_comap.mp hf`. (By a standard fact that the module
neither states nor uses, `Tendsto f cofinite cofinite` holds exactly when every
fiber of `f` is finite.) Coordinate lemmas `flatten_equiv'_apply`
(`flattenEquiv' C hf x i = x (f i) ⟨i, rfl⟩`) and
`flatten_equiv'_symm_apply` (`(flattenEquiv' C hf).symm y j i = y i.1`).

### `flattenLinearEquiv` and `flattenLinearEquiv'`

```lean
def flattenLinearEquiv {T : Type*} [Semiring T]
    {G : ι → Type*} [(i : ι) → AddCommMonoid (G i)] [(i : ι) → Module T (G i)]
    (C : (i : ι) → Submodule T (G i)) (hf : Filter.comap f 𝒢 = ℱ) :
    Πʳ j, [Π (i : f ⁻¹' {j}), G i, Submodule.pi Set.univ (fun (i : f ⁻¹' {j}) => C i)]_[𝒢]
      ≃ₗ[T] Πʳ i, [G i, C i]_[ℱ]

def flattenLinearEquiv' {T : Type*} [Semiring T]
    {G : ι → Type*} [(i : ι) → AddCommMonoid (G i)] [(i : ι) → Module T (G i)]
    (C : (i : ι) → Submodule T (G i))
    (hf : Filter.Tendsto f Filter.cofinite Filter.cofinite) :
    Πʳ j, [Π (i : f ⁻¹' {j}), G i, Submodule.pi Set.univ (fun (i : f ⁻¹' {j}) => C i)]
      ≃ₗ[T] Πʳ i, [G i, C i]
```

These are the minimal linear wrappers for a constant coefficient semiring `T`
and submodule restrictions `C i`. On the fiber side the restricting submodule
is `Submodule.pi Set.univ (fun i ↦ C i)`, whose carrier is by definition
`Set.pi Set.univ (fun i ↦ C i)`. Both restricted products carry Mathlib's
`Module T` instance: the factor `Π (i : f ⁻¹' {j}), G i` has the pointwise
module structure. `flattenLinearEquiv C hf` has underlying equivalence
`flattenEquiv (fun i ↦ (C i : Set (G i))) hf`. Additivity and `T`-linearity
hold by `rfl`, because addition and scalar multiplication on restricted
products and on products are coordinatewise. `flattenLinearEquiv'` is
`flattenLinearEquiv` with the same cofinite filter equality as
`flattenEquiv'`. Coordinate lemmas `flattenLinearEquiv_apply`,
`flattenLinearEquiv_symm_apply`, `flattenLinearEquiv'_apply` and
`flattenLinearEquiv'_symm_apply` have the same forward formula
`x (f i) ⟨i, rfl⟩` and inverse formula `y i.1` as above.

A consumer whose target module structure is defined differently, for example
through an `Algebra` instance on a finite adele ring, must still identify that
scalar action with the coordinatewise one. The definitional coordinate
formulas above are available for that purpose.

## Provenance and adaptations

Adapted from Imperial College London FLT, commit
`923d45174c500aa1d994ba973bac38ea39eacbf7`,
`FLT/Mathlib/Topology/Algebra/RestrictedProduct/Equiv.lean`. The project
registered this source as `external-lean-reuse-snapshots-2026-10-21` (folder
`ImperialCollegeLondon--FLT/source`). The relevant lines are:

- lines 33-51: section variables and `Equiv.restrictedProductCongrRight`;
- lines 53-66: `MulEquiv.restrictedProductCongrRight` with its `to_additive`
  version `AddEquiv.restrictedProductCongrRight`;
- lines 105-124: `LinearEquiv.restrictedProductCongrRight`;
- lines 520-589: `flatten`, `flatten_apply`, `flattenEquiv`,
  `flatten_equiv_apply`, `flatten_equiv_symm_apply`, `flattenEquiv'`,
  `flatten_equiv'_apply`, `flatten_equiv'_symm_apply`.

Source header: Copyright (c) 2025 Kevin Buzzard; released under the Apache 2.0
license; authors Kevin Buzzard and Salvatore Mercuri. The Lean file keeps this
header and adds a modification notice. The upstream license is in the Library
at `licenses/ImperialCollegeLondon-FLT/LICENSE`.

Modifications by Worker 205:

- The module is standalone, with plain imports of two Mathlib modules instead
  of the FLT import closure. The module-system keywords (`module`,
  `public import`, `@[expose] public section`) are removed.
- `Equiv.restrictedProductCongrRight`: the source's `@[simps]` attribute is
  replaced by the explicit coordinate lemmas `_apply` and `_symm_apply` (forward
  and inverse coordinate formulas). The inverse laws are proved by
  `Equiv.symm_apply_apply`/`Equiv.apply_symm_apply` instead of `simp`, which
  made no progress at this project's Lean and Mathlib pin. The data (`toFun`,
  `invFun`) is the source's.
- `AddEquiv.restrictedProductCongrRight` is defined directly with the
  hypotheses that `to_additive` gives the source's `MulEquiv` version
  (`AddMonoid`, `AddSubmonoidClass`). Additivity is proved by `map_add`, and
  there are explicit `_apply` and `_symm_apply` lemmas. The multiplicative
  version is not ported.
- `LinearEquiv.restrictedProductCongrRight` is verbatim apart from the added
  `_apply` and `_symm_apply` lemmas.
- `flatten`, `flattenEquiv`, `flattenEquiv'` and their six lemmas keep the
  source names, including the snake-case lemma names, and the source proofs.
  The unused section variables `H` and `D` are dropped.
- `flattenLinearEquiv`, `flattenLinearEquiv'` and their four coordinate
  lemmas are new (internal additions). They supply the linear wrapper
  requested for the finite-adele base-change consumer. The source builds that
  linear structure inline at its use site.

Everything else in the source file is omitted: `MulEquiv.restrictedProductUnits`,
the multiplicative and ring congruences (lines 53-103 apart from the additive
form above), the reindexing equivalences `restrictedProductCongrLeft'`,
`restrictedProductCongrLeft` and `restrictedProductCongr` (lines 128-433), the
structure-map section, `Equiv.restrictedProductProd`,
`Equiv.restrictedProductPi`, `Equiv.restrictedProductMatrix` (lines 435-518)
and the principal-filter equivalences (lines 591-655). The source file has no
topological equivalences, and none are added.

## Scope

This module provides only generic equivalences. It defines no global
finite-adele map. It proves no tensor-product comparison, integral
comparison, topology, homeomorphism or norm statement. It does not show that
any map of fibers over finite places is finite-to-one.

## Checks

The module compiled with no errors or warnings in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). The full unapplied types of the
eight definitions were inspected and match the signatures above. Each type has
independent universe parameters for the index types, factor families, subobject
families and coefficient semiring. A private probe checked `simp` with the
coordinate lemmas for a submodule-restricted linear congruence over a
principal filter. It also checked the inverse formula of `flattenLinearEquiv`
over the bottom filter, and a round trip through `flattenEquiv'`.
For each of the eight definitions, `#print axioms` reports no axioms beyond
`propext`, `Classical.choice` and `Quot.sound`.
