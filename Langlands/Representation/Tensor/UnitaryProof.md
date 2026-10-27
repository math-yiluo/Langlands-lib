# Invariant positive forms on finite external tensor products: proof

Author: Worker 725.

## Result

`Langlands.FiniteTensor.invariantPositiveForm` proves the Library proposition
`Langlands.FiniteTensor.InvariantPositiveFormStatement.{uI, uG, uV}` from
[UnitaryStatement](UnitaryStatement.md). The theorem's type is exactly that
proposition. It has no extra parameters, typeclass arguments or theorem-valued
assumptions, and its universe parameters `uI uG uV` stay independent.

Here is the statement in words. Let `ι` be any finite index type, possibly
empty. Let `G i` be groups, `V i` complex vector spaces (zero spaces are
allowed), `ρ i` actual representations and `b i` invariant positive forms on
them. Then the actual external tensor representation
`Langlands.FiniteTensor.external ρ` on `PiTensorProduct ℂ V` has an invariant
positive form `bT`. On pure tensors,

```text
bT.inner (tprod ℂ v) (tprod ℂ w) = ∏ i, (b i).inner (v i) (w i).
```

`bT` is a `Langlands.InvariantPositiveForm`. Its Hermitian symmetry,
sesquilinearity, nonnegativity and definiteness therefore hold on the whole
tensor carrier, including arbitrary finite sums of pure tensors. Its
`invariant` field covers every element of the product group `∀ i, G i`. The
proof assumes no topology, norm, completeness, finite dimension, nontriviality,
smoothness, admissibility or irreducibility. All normed structures below are
built locally from the given factor forms and never become hypotheses.

## Implemented proof

All auxiliary declarations are in the namespace
`Langlands.FiniteTensor.InvariantPositiveFormProof`.

1. **Pulling back a core.** `coreComap c f hf` takes a positive definite core
   `c` on `F` and an injective linear map `f : E →ₗ[ℂ] F`. It defines the core
   `x, y ↦ c.inner (f x) (f y)` on `E`. Conjugate symmetry, nonnegativity,
   additivity and conjugate-homogeneity in the first argument come from those
   of `c` and the linearity of `f`. Definiteness uses that `f x = 0` forces
   `x = 0`, by injectivity. `coreComap_inner` records the defining equation by
   `rfl`.
2. **Right-argument linearity.** `core_inner_add_right` and
   `core_inner_smul_right` prove additivity and complex linearity in the second
   argument of any core. They use conjugate symmetry and the first-argument
   laws.
3. **Binary tensor product.** `exists_core_tmul cE cF` gives cores `cE` on `E`
   and `cF` on `F`. It produces a core `C` on `E ⊗[ℂ] F` with
   `C.inner (x ⊗ₜ y) (x' ⊗ₜ y') = cE.inner x x' * cF.inner y y'`. Inside the
   proof, `InnerProductSpace.Core.toNormedAddCommGroup` and
   `InnerProductSpace.ofCore` turn each given core into a local
   `NormedAddCommGroup` and `InnerProductSpace ℂ` instance on that factor.
   Mathlib's `TensorProduct.instInnerProductSpace` then supplies an inner
   product space structure on the algebraic tensor product.
   `InnerProductSpace.toCore` extracts its core. `TensorProduct.inner_tmul`
   gives the product formula. The factor inner products of these local
   instances are, by construction, the given `cE.inner` and `cF.inner`. Mathlib
   proves positivity and definiteness without assuming finite dimension or
   completeness of `E` or `F`.
4. **`Fin n`-indexed tensors.** `exists_core_fin n V c` is proved by recursion
   on `n`. It produces a core on `PiTensorProduct ℂ V` for `V : Fin n → Type uV`
   whose value on pure tensors is `∏ i, (c i).inner (v i) (w i)`.
   - For `n = 0`, Mathlib's `PiTensorProduct.isEmptyEquiv` is a linear
     equivalence `PiTensorProduct ℂ V ≃ₗ[ℂ] ℂ` that sends every pure tensor to
     `1`. The core is the pullback, via `coreComap`, of ℂ's standard core
     `InnerProductSpace.toCore`. On pure tensors it equals
     `inner ℂ (1 : ℂ) 1 = 1`, the empty product.
   - For `n + 1`, recursion gives a core `C₁` on the tail tensor
     `PiTensorProduct ℂ (fun j : Fin n => V j.succ)`. Step 3 applied to
     `c 0` and `C₁` gives a core `C₂` on `V 0 ⊗[ℂ] (tail tensor)`. The Library
     linear equivalence `Langlands.FiniteTensor.headTailLinearEquiv`
     ([FiniteEquivalences](FiniteEquivalences.md)) splits off the first
     factor. The core is `C₂` pulled back along it. On pure tensors,
     `headTailLinearEquiv_tprod` gives
     `v 0 ⊗ₜ tprod ℂ (fun j => v j.succ)`. The formulas for `C₂` and `C₁`,
     together with `Fin.prod_univ_succ`, give the full product.
5. **Arbitrary finite index types.** `exists_core ι V c` takes
   `e := Fintype.equivFin ι : ι ≃ Fin (Fintype.card ι)`. It applies step 4 to
   the reindexed family `fun k => V (e.symm k)` and its cores. The result is
   pulled back along Mathlib's linear equivalence
   `PiTensorProduct.reindex ℂ V e`. `PiTensorProduct.reindex_tprod` rewrites
   pure tensors. `Equiv.prod_comp` identifies the reindexed product with
   `∏ i, (c i).inner (v i) (w i)`. The carrier universe stays `uV`.
6. **Invariance from pure tensors.** `core_inner_map_map C T hT` takes a core
   `C` on `PiTensorProduct ℂ V` and a linear operator `T` that preserves `C`
   on all pairs of pure tensors. It concludes that `T` preserves `C` on all
   pairs of vectors. The proof is `PiTensorProduct.induction_on` on the first
   argument and, in the scaled-pure-tensor case, on the second. The cases
   combine linearity of `T` with the left laws `C.add_left` and `C.smul_left`
   and the right laws from step 2.
7. **Main theorem.** Introduce `ι, G, V, ρ, b`. Step 5 applied to the
   underlying cores `(b i).toInnerProductCore` gives `C` and its product
   formula `hC`. The form `bT` has core `C`. For `g : ∀ i, G i`, step 6
   applies to `T := external ρ g`. On pure tensors, `external_tprod`
   ([Finite](Finite.md)) rewrites `external ρ g (tprod ℂ v)` to
   `tprod ℂ (fun i => ρ i (g i) (v i))`. After `hC`, invariance reduces to
   the factorwise identities `(b i).invariant (g i) (v i) (w i)`, combined by
   `Finset.prod_congr`. The pure-tensor formula of the statement is `hC`
   itself.

Nothing in the proof treats empty or zero factors specially. The empty index
type is the `n = 0` case of step 4. Zero factors need no case at all, because
steps 3–6 make no nontriviality assumption.

## Provenance

This is internal algebraic reasoning built on existing Library constructions
and pinned Mathlib. It proves a derived prerequisite for the tensor inducing
datum of Kudla, *The Local Langlands Correspondence: The Non-Archimedean
Case*, in *Motives*, Part 2, Proc. Sympos. Pure Math. 55, Part 2, AMS, 1994,
section 1.1, printed page 368 / retained PDF page 378, equations
(1.1.3)–(1.1.4). The registered source is
`kudla-1994-local-langlands-nonarchimedean`, SHA-256
`0e1f9bc9986fc136081f0eed1aaafb50302acacb5a23e9538581f2f5b533198b`. That
passage motivates the result only. It contains no proof of positivity of the
tensor form, and this proof does not follow any literature argument.

Mathlib facts used, at commit `5ed2965256430c3649e86755f9576b54eca72435`:

- `Mathlib/Analysis/InnerProductSpace/TensorProduct.lean`:
  `TensorProduct.instNormedAddCommGroup`,
  `TensorProduct.instInnerProductSpace` and `TensorProduct.inner_tmul`;
- `Mathlib/Analysis/InnerProductSpace/Defs.lean`:
  `InnerProductSpace.Core.toNormedAddCommGroup`, `InnerProductSpace.ofCore`
  and `InnerProductSpace.toCore`;
- `Mathlib/LinearAlgebra/PiTensorProduct/Basic.lean`:
  `PiTensorProduct.isEmptyEquiv`, `PiTensorProduct.isEmptyEquiv_apply_tprod`,
  `PiTensorProduct.reindex`, `PiTensorProduct.reindex_tprod` and
  `PiTensorProduct.induction_on`;
- `Fin.prod_univ_succ`, `Equiv.prod_comp`, `Fintype.equivFin` and
  `Finset.prod_congr`.

Library facts used: `Langlands.FiniteTensor.headTailLinearEquiv` and
`headTailLinearEquiv_tprod` from `Langlands.Representation.Tensor.FiniteEquivalences`,
`Langlands.FiniteTensor.external` and `external_tprod` from
`Langlands.Representation.Tensor.Finite`, and `Langlands.InvariantPositiveForm`
from `Langlands.Representation.Unitary.Basic`. The module imports
`Langlands.Representation.Tensor.UnitaryStatement`,
`Langlands.Representation.Tensor.FiniteEquivalences` and
`Mathlib.Analysis.InnerProductSpace.TensorProduct`. It does not modify the
target statement or anything that statement imports.

## Development checks

In environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0), development
compilation of this module gave no errors or warnings (diagnostic
`1096a57a-0018-43a8-a86b-66cbec0911b4`). Inspection reported a theorem with
universe parameters `uI uG uV` and exactly the axioms `propext`,
`Classical.choice` and `Quot.sound`. These checks are not independent
acceptance.
