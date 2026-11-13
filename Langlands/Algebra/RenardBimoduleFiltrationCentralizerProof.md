# Centralizers of filtered bimodules (Renard VI.10.4, Lemma): proof

Module `Langlands.Algebra.RenardBimoduleFiltrationCentralizerProof`.
Namespace `Langlands.Algebra`. Universe parameters `u, v`.

The module contains one theorem,
`Langlands.Algebra.renardBimoduleFiltrationCentralizer`, whose type is exactly
the published proposition
`Langlands.Algebra.RenardBimoduleFiltrationCentralizerStatement.{u, v}`. It
imports that statement module unchanged and adds no hypothesis. The theorem
depends only on the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

Worker 142 wrote this proof under the proof task
`74deb29a-d3ac-470e-a0c4-392f0fab8397` (Task 5606), following the route
suggested in that task's context by Worker 1222.

## What is proved

Let `A` be a commutative ring and `M` a module over `R = A ⊗[ℕ] Aᵐᵒᵖ`, i.e. an
`A`-bimodule. Let `F : ℕ → Submodule R M` satisfy `F 0 = ⊤`, `F (n + 1) = ⊥`,
`F (i + 1) ≤ F i` for `i ≤ n`, and suppose that for `i, j ≤ n` with `i ≠ j`
every `R`-linear map `Q_i → Q_j` is zero, where
`Q_i = ↥(F i) ⧸ (F (i + 1)).comap (F i).subtype`. Then the set of `a : A` with
`(a ⊗ₜ 1) • x = (1 ⊗ₜ op a) • x` for all `x : M` equals the intersection over
`i ∈ Finset.range (n + 1)` of the corresponding sets for `x : Q_i`.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`, VI.10.4,
the Lemma on printed pp.211–212 (PDF pp.217–218); Worker 142 read both PDF
pages for this proof. Renard proves the Lemma by induction on `n`, splitting
off `0 → M_1 → M → Q_0 → 0`, and states without detail that the hypothesis
forces the morphism `Q_0 → M_1` to vanish. The Lean proof below
uses the same two ingredients (the commutator map `m ↦ βm − mβ` is a bimodule
morphism, and `Hom(Q_k, M_{k+1}) = 0`), but organizes the induction as a
descending induction on the filtration index inside the fixed filtration,
which avoids re-indexing the filtration of `M_1`.

## The Lean proof

After introducing the data, the proof installs the same local instance as the
statement, `∀ i, AddCommGroup ↥(F i) := fun i => (F i).addCommGroup`, so that
the quotient types `Q_i` elaborate exactly as in the statement. It then proves
the set equality by `ext a` and two inclusions. Throughout, `R` is commutative:
Mathlib's commutative-ring instances on tensor products of commutative algebras
(`Algebra.TensorProduct.instCommSemiring`, `Algebra.TensorProduct.instCommRing`)
apply because `A` and `Aᵐᵒᵖ` are commutative.

### `𝒞_A(M) ⊆ 𝒞_A(Q_i)`

Every element of `Q_i` is the class `mk y` of some `y : ↥(F i)`
(`Submodule.Quotient.induction_on`). Since `Submodule.Quotient.mk` is linear,
`r • mk y = mk (r • y)`, and the coercion of `r • y` to `M` is `r • (y : M)`.
So the hypothesis on `(y : M)` gives the equality in `Q_i`.

### `⋂ 𝒞_A(Q_i) ⊆ 𝒞_A(M)`

Fix `a` centralizing every `Q_i`, `i ≤ n`.

1. **The commutator map.** `D x = (a ⊗ₜ 1) • x − (1 ⊗ₜ op a) • x` is defined
   as an `R`-linear endomorphism `D : M →ₗ[R] M`. Additivity is `smul_add`;
   `R`-linearity is `smul_comm`, valid because `R` is commutative. This is
   Renard's observation that `m ↦ βm − mβ` is a bimodule morphism.
2. **`D (F i) ⊆ F (i + 1)` for `i ≤ n`** (`hDstep`). For `y ∈ F i`, the
   centralizing hypothesis on `Q_i` applied to `mk ⟨y, _⟩` says that
   `mk ((a ⊗ₜ 1) • y − (1 ⊗ₜ op a) • y) = 0` in `Q_i`, i.e. the difference lies
   in `(F (i + 1)).comap (F i).subtype`, i.e. `D y ∈ F (i + 1)`.
3. **`Hom(Q_k, F j) = 0` for `k ≤ n` and `k < j ≤ n + 1`** (`hvanish`). The
   claim is phrased for linear maps `g : Q_k →ₗ[R] M` whose values all lie in
   `F j`, which avoids a separate codomain type. It is proved by induction on
   `m` with `j + m = n + 1`, i.e. by descending induction on `j`.
   - If `j = n + 1`, then `F j = ⊥`, so every value of `g` is `0`.
   - If `j ≤ n`, restrict the codomain of `g` to `F j` (`LinearMap.codRestrict`)
     and compose with the quotient map `F j → Q_j` (`Submodule.mkQ`). This is a
     linear map `Q_k → Q_j` with `k ≠ j`, hence zero by hypothesis. So every
     value of `g` lies in `(F (j + 1)).comap (F j).subtype`, i.e. in
     `F (j + 1)`, and the induction hypothesis for `j + 1` gives `g = 0`.

   This is the left exactness of `Hom(Q_k, −)` along
   `0 → F (j + 1) → F j → Q_j`, which Renard leaves implicit.
4. **`D` vanishes on every `F k`** (`hzero`), by induction on `m` with
   `k + m = n + 1`, i.e. by descending induction on `k`.
   - If `k = n + 1`, then `F k = ⊥` and `D 0 = 0`.
   - If `k ≤ n`, the induction hypothesis says `D` vanishes on `F (k + 1)`,
     so `D ∘ (F k).subtype` vanishes on `(F (k + 1)).comap (F k).subtype` and
     descends to `g : Q_k →ₗ[R] M` (`Submodule.liftQ`) with
     `g (mk y) = D y`. By step 2 every value of `g` lies in `F (k + 1)`, so
     `g = 0` by step 3 with `j = k + 1`. Evaluating at `mk ⟨y, _⟩` gives
     `D y = 0` for all `y ∈ F k`.
5. **Conclusion.** With `k = 0` and `F 0 = ⊤`, `D x = 0` for every `x : M`,
   which is `(a ⊗ₜ 1) • x = (1 ⊗ₜ op a) • x` by `sub_eq_zero`.

## Remarks

- The monotonicity hypothesis `F (i + 1) ≤ F i` is introduced as `_hmono` and
  not used. Because the statement defines `Q_i` as `F i` modulo the pullback
  of `F (i + 1)`, i.e. `F i / (F i ∩ F (i + 1))`, the argument above goes
  through without it. This does not weaken or change the proved statement.
- The local `AddCommGroup` instance is needed inside the proof for the same
  reason as in the statement: instance search does not find the additive group
  structure of `↥(F i)` for submodules over `A ⊗[ℕ] Aᵐᵒᵖ`.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Algebra.RenardBimoduleFiltrationCentralizerStatement` | the target proposition (and, transitively, Mathlib's bimodule and quotient-module API) |
