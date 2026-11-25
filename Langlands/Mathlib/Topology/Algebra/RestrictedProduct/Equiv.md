# Congruence and fiber flattening of restricted products (stand-in for Mathlib)

Module `Langlands.Mathlib.Topology.Algebra.RestrictedProduct.Equiv`. It declares two families of
equivalences between Mathlib's algebraic restricted products `Πʳ i, [R i, A i]_[𝓕]`:

1. **Pointwise congruence**: `Equiv.restrictedProductCongrRight`, `AddEquiv.restrictedProductCongrRight`
   and `LinearEquiv.restrictedProductCongrRight`, with the coordinate lemmas
   `Equiv.restrictedProductCongrRight_apply`, `Equiv.restrictedProductCongrRight_symm_apply` and
   `AddEquiv.restrictedProductCongrRight_apply`.
2. **Fiber flattening** in the name space `RestrictedProduct`: `flatten`, `flattenEquiv`, `flattenEquiv'`
   and their six coordinate lemmas `flatten_apply`, `flatten_equiv_apply`, `flatten_equiv_symm_apply`,
   `flatten_equiv'_apply`, `flatten_equiv'_symm_apply`.

It imports `Mathlib.LinearAlgebra.Pi` and `Mathlib.Topology.Algebra.RestrictedProduct.Basic` and uses no
topology. The Library's own lemmas on these equivalences and the linear flattening are in
`Langlands.LinearAlgebra.RestrictedProduct.Equiv`, which imports this module.

## Origin, stand-in status and licence

The file is taken from the Imperial College London FLT project
(github.com/ImperialCollegeLondon/FLT) at commit `0198058` (`019805815d7da565ed1e9f427b6fbd0cbc9d00d3`), file
`FLT/Mathlib/Topology/Algebra/RestrictedProduct/Equiv.lean`, lines 31-49, 105-126 and 520-589. The project releases it under the Apache License 2.0; its licence is in
the Library at `licenses/ImperialCollegeLondon-FLT/LICENSE`, and the Lean file keeps the source's
copyright and author lines.

The file is a **stand-in for Mathlib**: the fourteen declarations have the names that the Imperial project gives them, and
are expected in Mathlib under these names. The file is to be deleted when the Library's Mathlib has
these declarations; the modules that use them then import Mathlib's module instead.

Until 22 November 2026 these declarations were in `Langlands/LinearAlgebra/RestrictedProduct/`, ported
from the earlier Imperial commit `923d45174c500aa1d994ba973bac38ea39eacbf7`. The
declarations that the Imperial project declares under the same name were then moved
here, with the Imperial text of commit `0198058` wherever the declaration is the same one, so that this
file can be compared line by line with its source. The header of the Lean file gives the line ranges
taken and every difference.

What is Imperial text and what is not:

- **Imperial text, verbatim**: the section variables and `Equiv.restrictedProductCongrRight` (lines
  31-49) except the attribute `@[simps]` (line 43); `LinearEquiv.restrictedProductCongrRight` with its
  section (lines 105-126); the flattening section (lines 520-589), whose unused variables `H` and `D` are
  back (the earlier port had dropped them; it only renames a universe parameter of the flattening
  declarations).
- **Library text**, marked `-- Library text:` in the Lean file:
  - the two inverse laws of `Equiv.restrictedProductCongrRight`, proved by `Equiv.symm_apply_apply` and
    `Equiv.apply_symm_apply`. Imperial's `by ext; simp` (lines 50-51) makes no progress in an ordinary
    (non-`module`) Lean file at this Lean and Mathlib: Mathlib's `RestrictedProduct.map_apply` fires only
    with `backward.isDefEq.respectTransparency` off, and the Library sets no such option here;
  - `Equiv.restrictedProductCongrRight_apply`, `Equiv.restrictedProductCongrRight_symm_apply` and
    `AddEquiv.restrictedProductCongrRight_apply`. The Imperial project generates lemmas of exactly these
    names, by `@[simps]` and by `@[to_additive (attr := simps! apply)]`, but with other statements (an
    equation of whole maps, `⇑e x = map … x`), while the Library's are coordinate lemmas
    `… x i = φ i (x i)`. Keeping the names and the Library's statements means dropping the
    attribute. When Mathlib adopts the Imperial file, these three lemmas will exist there with Imperial's
    statements, and the Library's uses must be adapted then;
  - `AddEquiv.restrictedProductCongrRight`, defined directly. Imperial obtains it by `to_additive` from
    `MulEquiv.restrictedProductCongrRight` (lines 53-66), which would bring the multiplicative version, not
    used by the Library, and the `simps!` lemma above. The definition is the same (the underlying
    equivalence is `Equiv.restrictedProductCongrRight`, additivity coordinatewise).
- **Left out**: the other declarations of the Imperial file (units, rings, reindexing, products,
  matrices, principal filters), which the Library does not use.

## Pointwise congruence

Common variables: an index type `ι`, factor families `R₁ R₂ : ι → Type*` and a
filter `𝓕 : Filter ι`, all implicit. In the order of the implicit arguments the Imperial text puts the
restricting families `A₁ A₂` (and, for the additive and linear versions, the subobject types `S₁ S₂` with
their `SetLike` instances) before `𝓕`; the Library's earlier port had `𝓕` first. The statements are
otherwise those of the earlier port, and each old statement is proved by the declaration as it is now.

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
checked coordinatewise by `map_add (φ i)`. Coordinate lemma
`AddEquiv.restrictedProductCongrRight_apply` (`… x i = φ i (x i)`); the inverse formula
`(…).symm y i = (φ i).symm (y i)` is the Library's
`Langlands.LinearAlgebra.AddEquiv.restrictedProductCongrRight_symm_apply`, in
`Langlands.LinearAlgebra.RestrictedProduct.Equiv`. This is the only additive helper. The
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
`map_smul (φ i)`. Its coordinate lemmas are the Library's
`Langlands.LinearAlgebra.LinearEquiv.restrictedProductCongrRight_apply` (`… x i = φ i (x i)`) and
`Langlands.LinearAlgebra.LinearEquiv.restrictedProductCongrRight_symm_apply`
(`(…).symm y i = (φ i).symm (y i)`), in `Langlands.LinearAlgebra.RestrictedProduct.Equiv`.

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

## Checks

The module builds with Lean 4.35.0 and Mathlib `56a0058`. Compared with the declarations before the move
(binders and statements, 22 November 2026): the flattening declarations are identical up to the name of a
universe parameter; the three congruences and their coordinate lemmas differ only in the order of the
implicit arguments, and the nine old statements, with the old variable order, are each proved by the
declarations as they are now applied to their explicit arguments.
