# Finite tensor decomposition of row Schwartz–Bruhat functions

The theorem `Langlands.HarmonicAnalysis.rowTensorDecomposition` proves the
published `Langlands.HarmonicAnalysis.RowTensorDecompositionStatement` from
`Langlands.HarmonicAnalysis.RowTensorDecompositionStatement`. Its full parameter
order is `X : Type u`, the `TopologicalSpace`, `LocallyCompactSpace`, `T2Space`,
and `TotallyDisconnectedSpace` instances on `X`, then `d : ℕ`. Its conclusion is
exactly that proposition, with no added hypotheses. Thus each
`f : SchwartzBruhat (Fin d → X)` admits a natural number `N`, coefficients
`c : Fin N → ℂ`, and factors
`g : Fin N → Fin d → SchwartzBruhat X` satisfying

```text
f x = ∑ j : Fin N, c j * ∏ i : Fin d, g j i (x i)
```

for every `x : Fin d → X`. Both Schwartz–Bruhat spaces are the actual
submodule carriers from `Langlands.HarmonicAnalysis.Basic`.

This is an internal derived proof by Worker 128 of the prerequisite specified
for Worker 110's row Fourier argument. It is not a transcription of an external
theorem. It uses the existing Mathlib clopen-basis, compactness, locally constant
indicator, and linear-span results. The compact-clopen neighborhood lemma
`Langlands.HarmonicAnalysis.exists_compact_clopen` is also public, so
[closed restriction](Distribution/ClosedRestrictionProof.md) can reuse the same
statement and proof. The other auxiliary declarations are private. The proof does not
construct an abstract tensor product or prove any Fourier or integration result.

The implemented argument proceeds as follows.

1. For a family of one-coordinate test functions `g`, define its pure pointwise
   tensor by `rowPure g x = ∏ i, g i (x i)`. Let `rowSpan X d` be the complex
   linear span of these functions in the ambient function module. Pointwise
   products of two Schwartz–Bruhat functions remain locally constant and
   compactly supported. Consequently, multiplying any element of this span by a
   pure tensor remains in the span. The proof first multiplies two generators
   coordinatewise, then uses `Submodule.span_induction` for zero, addition, and
   scalar multiplication.
2. A compact clopen subset of `X` has a Schwartz–Bruhat indicator. The indicator
   of a coordinate box `Set.pi Set.univ U` is the pure tensor of its coordinate
   indicators. Inside the box all factors are one; outside it at least one
   factor is zero. The product identities include the empty index type.
3. Every neighborhood of a point of `X` contains a compact clopen neighborhood.
   To obtain it, intersect the given neighborhood with a compact neighborhood,
   then use Mathlib's `loc_compact_Haus_tot_disc_of_zero_dim` clopen basis. The
   resulting clopen set is a closed subset of that compact set. For a row `x`,
   local constancy of `f` supplies a neighborhood on which `f` equals `f x`.
   `Filter.mem_pi` gives coordinate neighborhoods, each refined as above. Their
   box `B x` contains `x`, is open, and lies in the indicated fiber of `f`.
4. Compactness of the topological support of `f` supplies finitely many such
   boxes covering it. On each box, the restricted function is `f x` times the
   box indicator, so belongs to the pure-tensor span. A finite induction combines
   these restrictions using the pointwise identity

   ```text
   1_(A ∪ C) f = 1_A f + 1_C f - (1_C f) 1_A.
   ```

   Here `A` is the newly inserted box and `C` is the union of the previous boxes.
   The subtraction term stays in the span by step 1, because the new box
   indicator is a pure tensor. Outside the final union, `f` vanishes because the
   union covers its topological support. Thus the final restriction equals `f`.
5. `Finsupp.mem_span_range_iff_exists_finsupp` turns span membership into a
   finitely supported complex combination of pure tensors. Enumerating its
   support by `Fin (Fintype.card support)` produces the required `N`, `c`, and
   `g`. Evaluating the function equality at a row and reindexing the finite sum
   yields precisely the displayed equality.

No nonemptiness assumption or positive-dimension assumption enters any step.
For `d = 0`, the empty product is one, and the complex coefficients retain the
arbitrary value at the unique row. This also applies when `X` is empty. When
`X` is empty and `d` is positive, there are no rows and the proof still applies.
An empty finite support produces `N = 0` and the empty sum. The argument is
classical and existential; it does not claim a canonical decomposition or a
bound on the number of terms.
