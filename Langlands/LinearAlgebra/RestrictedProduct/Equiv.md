# Restricted-product congruences and flattening: the Library's lemmas and the linear flattening

Module `Langlands.LinearAlgebra.RestrictedProduct.Equiv`. It imports the module
`Langlands.Mathlib.Topology.Algebra.RestrictedProduct.Equiv`, a stand-in for Mathlib, which holds the pointwise congruences
`Equiv.restrictedProductCongrRight`, `AddEquiv.restrictedProductCongrRight`,
`LinearEquiv.restrictedProductCongrRight` and the fiber flattening `RestrictedProduct.flatten`,
`flattenEquiv`, `flattenEquiv'` (names of the Imperial College London FLT project, expected in Mathlib under these names),
and `Mathlib.LinearAlgebra.Pi`. It declares the Library's own lemmas and constructions on them, which the
Imperial project does not have, in the name space `Langlands.LinearAlgebra` of this directory:

- `Langlands.LinearAlgebra.AddEquiv.restrictedProductCongrRight_symm_apply φ hφ y i :
  (AddEquiv.restrictedProductCongrRight φ hφ).symm y i = (φ i).symm (y i)`;
- `Langlands.LinearAlgebra.LinearEquiv.restrictedProductCongrRight_apply φ hφ x i :
  LinearEquiv.restrictedProductCongrRight φ hφ x i = φ i (x i)`;
- `Langlands.LinearAlgebra.LinearEquiv.restrictedProductCongrRight_symm_apply φ hφ y i :
  (LinearEquiv.restrictedProductCongrRight φ hφ).symm y i = (φ i).symm (y i)`;
- `Langlands.LinearAlgebra.RestrictedProduct.flattenLinearEquiv`, `flattenLinearEquiv'` and their four
  coordinate lemmas `flattenLinearEquiv_apply`, `flattenLinearEquiv_symm_apply`,
  `flattenLinearEquiv'_apply`, `flattenLinearEquiv'_symm_apply`.

All are `simp` lemmas proved by `rfl`, or definitions whose additivity and scalar compatibility hold by
`rfl`. The three coordinate lemmas have the hypotheses of the corresponding congruence (see the page of
the Mathlib stand-in module); they are stated with the Library's variable order (`𝓕` first among the implicit
arguments).

## Names and place (22 November 2026)

Until 22 November 2026 this module held all of the congruences and the flattening, with these nine
declarations in the root name spaces `AddEquiv`, `LinearEquiv` and `RestrictedProduct`. Then the
fourteen declarations that the Imperial project declares under the same name were moved to the
Mathlib stand-in module, and these nine, the Library's own, were put under `Langlands.LinearAlgebra`: each
name is the old one with the prefix `Langlands.LinearAlgebra.` (for instance
`RestrictedProduct.flattenLinearEquiv` became `Langlands.LinearAlgebra.RestrictedProduct.flattenLinearEquiv`).
The name space `Langlands.RestrictedProduct` was not used: inside a name space `Langlands.…`, Lean would
take `open RestrictedProduct` and `open scoped RestrictedProduct` to mean `Langlands.RestrictedProduct`,
and the Library has many such `open` commands for Mathlib's `RestrictedProduct` (its `Πʳ` notation).
Statements, proofs and variable lines are unchanged; no use outside this module names these
declarations.

### `Langlands.LinearAlgebra.RestrictedProduct.flattenLinearEquiv` and `flattenLinearEquiv'`

```lean
def Langlands.LinearAlgebra.RestrictedProduct.flattenLinearEquiv {T : Type*} [Semiring T]
    {G : ι → Type*} [(i : ι) → AddCommMonoid (G i)] [(i : ι) → Module T (G i)]
    (C : (i : ι) → Submodule T (G i)) (hf : Filter.comap f 𝒢 = ℱ) :
    Πʳ j, [Π (i : f ⁻¹' {j}), G i, Submodule.pi Set.univ (fun (i : f ⁻¹' {j}) => C i)]_[𝒢]
      ≃ₗ[T] Πʳ i, [G i, C i]_[ℱ]

def Langlands.LinearAlgebra.RestrictedProduct.flattenLinearEquiv' {T : Type*} [Semiring T]
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

## Provenance of the earlier port (all 23 declarations, before the move)

The paragraphs below describe the port of 2026, before fourteen of its declarations were
moved to `Langlands.Mathlib.Topology.Algebra.RestrictedProduct.Equiv`; they are kept as the
record of that port.

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

Modifications in Langlands-lib (2026):

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
  needed by the finite-adele base-change consumer. The source builds that
  linear structure inline at its use site.

Everything else in the source file is omitted: `MulEquiv.restrictedProductUnits`,
the multiplicative and ring congruences (lines 53-103 apart from the additive
form above), the reindexing equivalences `restrictedProductCongrLeft'`,
`restrictedProductCongrLeft` and `restrictedProductCongr` (lines 128-433), the
structure-map section, `Equiv.restrictedProductProd`,
`Equiv.restrictedProductPi`, `Equiv.restrictedProductMatrix` (lines 435-518)
and the principal-filter equivalences (lines 591-655). The source file has no
topological equivalences, and none are added.

## Checks

The module builds with Lean 4.35.0 and Mathlib `56a0058`. The types of the nine declarations are the same
as before the renaming up to the renamed constants.
