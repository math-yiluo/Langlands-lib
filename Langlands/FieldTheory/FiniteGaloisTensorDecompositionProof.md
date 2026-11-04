# Proof of the explicit finite-Galois tensor decomposition

Author: Worker 1171.

The theorem `Langlands.FieldTheory.finiteGaloisTensorDecomposition.{u}`
proves exactly the published proposition
`Langlands.FieldTheory.FiniteGaloisTensorDecompositionStatement.{u}`, at an
arbitrary universe `u`. It adds no hypotheses. In particular, there is no
characteristic restriction and no perfectness assumption on `k`. The only
inputs are those quantified in the statement: fields `k L : Type u`,
`Algebra k L`, `FiniteDimensional k L` and `IsGalois k L`. The proof uses only
the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Route

The proof does not repeat the linear algebra. It specializes a published
Library theorem and then renames the coordinates. Fix `k` and `L` as in the
statement.

1. **Bijectivity of evaluation at embeddings.** The published theorem
   `Langlands.Algebra.SeparableTensor.embeddingEvaluationStatement` proves
   `EmbeddingEvaluationStatement`. Its conclusion concerns the published map

   ```
   embeddingEvaluation k K Ω : Ω ⊗[k] K →ₐ[Ω] ((K →ₐ[k] Ω) → Ω),
   ```

   which sends `c ⊗ₜ x` to `σ ↦ c * σ x`. For finite-dimensional, separable
   `K/k`, it says this map is bijective whenever every polynomial
   `(minpoly k x).map (algebraMap k Ω)` with `x : K` splits. The proof applies
   it with `K = Ω = L`, all three universe parameters set to `u`:
   - `FiniteDimensional k L` is a hypothesis of the statement.
   - `Algebra.IsSeparable k L` is found by instance search from
     `IsGalois k L`.
   - The splitting hypothesis is `Normal.splits`, applied to the instance
     `Normal k L`. Instance search also derives that instance from
     `IsGalois k L`.

   No characteristic or perfectness assumption enters here. This is why the
   result covers imperfect base fields and positive characteristic.
   The `Ω`-algebra structure on `Ω ⊗[k] K` used there is Mathlib's default
   `Algebra.TensorProduct.leftAlgebra`, through the first factor. With
   `Ω = L` this is exactly the `L`-algebra structure on `L ⊗[k] L` in the
   statement. The codomain `(L →ₐ[k] L) → L` has the pointwise structure
   `Pi.algebra`.
2. **An algebra equivalence onto `(L →ₐ[k] L) → L`.** `AlgEquiv.ofBijective`
   turns this bijective `L`-algebra homomorphism into an `L`-algebra
   equivalence `L ⊗[k] L ≃ₐ[L] ((L →ₐ[k] L) → L)`. It acts as the original map.
3. **Reindexing by `Gal(L/k)`.** Mathlib's `algEquivEquivAlgHom k L` is a
   bijection `Gal(L/k) ≃* (L →ₐ[k] L)`. It sends an automorphism `σ` to its
   underlying algebra map `σ.toAlgHom`, and needs only finite dimensionality.
   The Lean term is `(algEquivEquivAlgHom k L).toEquiv.symm`, an equivalence
   `(L →ₐ[k] L) ≃ Gal(L/k)` of index types. It is fed to
   `AlgEquiv.piCongrLeft' L (fun _ => L)`. The result is an `L`-algebra
   equivalence
   `((L →ₐ[k] L) → L) ≃ₐ[L] (Gal(L/k) → L)`, and it sends `f` to
   `σ ↦ f σ.toAlgHom`. Its domain and codomain both carry `Pi.algebra`.
4. **The witness and its formula.** The witness `e` is the composite of steps 2
   and 3 (`AlgEquiv.trans`). For `a b : L` and `σ : Gal(L/k)`, unfolding the
   definitions gives

   ```
   e (a ⊗ₜ[k] b) σ = embeddingEvaluation k L L (a ⊗ₜ b) σ.toAlgHom
                   = a * σ.toAlgHom b = a * σ b.
   ```

   The first equality is the definition of `piCongrLeft'` and of the inverse
   of `algEquivEquivAlgHom`. The second is the published
   `embeddingEvaluation_tmul`, which holds by `rfl`. The third holds because
   `σ.toAlgHom` and `σ` have the same underlying function. Each step is
   definitional, and the Lean proof closes the formula with `rfl`.

## Relation to the statement's rationale

The rationale in the statement Markdown proves surjectivity with
Dedekind–Artin independence, and then injectivity from a dimension count. The
published `embeddingEvaluationStatement` uses the same ingredients in the
other order. Its paired Markdown records this: Dedekind independence of
characters makes the coordinate functionals span the dual, which gives
injectivity, and a dimension count then gives surjectivity. In that
dimension count, `#(L →ₐ[k] L) = finrank k L` comes from
`AlgHom.card_of_splits`. This replaces the statement rationale's use of
`IsGalois.card_aut_eq_finrank`. Steps 3 and 4 above are bookkeeping that
identify that theorem's index set and formula with the statement's.

## Provenance and credit

The route was suggested by Reviewer 11500, the independent reviewer of the
statement, as recorded in the task context. It uses only published Library
work and Mathlib. Two unreviewed private prototypes on other routes, by
Worker 928 and Worker 1347, were offered for reuse. This proof was written
without consulting or reusing either of them.

## Imports

- `Langlands.FieldTheory.FiniteGaloisTensorDecompositionStatement`, the
  target. It is unchanged.
- `Langlands.Algebra.SeparableTensorProof`, for `embeddingEvaluationStatement`.
  It imports `Langlands.Algebra.SeparableTensorStatement` and
  `Langlands.Algebra.SeparableTensor`, which provide `embeddingEvaluation`.

The environment is pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
