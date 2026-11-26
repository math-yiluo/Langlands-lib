# Proof: one growth exponent for every real Whittaker coefficient map

Module `Langlands.Global.RankinSelberg.RealWhittakerModelUniformityProof`. The theorem

```lean
theorem Langlands.Global.RankinSelbergGlobal.realWhittakerModelUniformity :
    RealWhittakerModelUniformityStatement
```

proves `Langlands.Global.RankinSelbergGlobal.RealWhittakerModelUniformityStatement` (module
`RealWhittakerModelUniformityStatement`). Unfolded, the statement is

```lean
∀ (r : ℕ) (ds : List RealBlock), realRank ds = r + 1 → ∀ a : ℝˣ,
  realWhittakerModel r ds a ≤ realUniformWhittakerModel r ds a
```

In words: for a list `ds` of real blocks of total rank `r + 1` and a nonzero real `a`, every
function in the span of the ranges of the real Whittaker coefficient maps `B` of the
`O(r + 1)`-finite standard module `realStandardKFinite (r + 1) ds` lies in the span of the
ranges of the coefficient maps that have one polynomial growth exponent for all source vectors.
A coefficient map `B` satisfies `IsRealWhittakerIntertwiner r ds a B`, whose growth bound
`‖B f g‖ ≤ C * realMatrixHeight g ^ N` allows `C` and `N` to depend on `f`. The uniform maps
satisfy `IsRealUniformWhittakerIntertwiner r ds a B`, which in addition fixes `N` before the
source vector, while `C` may still depend on `f`.

## The Lean proof

The proof is one line:

```lean
fun r ds hRank a => (realWhittakerModels_eq r ds hRank a).le
```

The Library's theorem `realWhittakerModels_eq` (module `RealWhittakerUniformGrowth`) proves the
equality `realWhittakerModel r ds a = realUniformWhittakerModel r ds a` under exactly the
hypotheses of the statement, `realRank ds = r + 1` and `a : ℝˣ`. The theorem takes its
inequality half. The statement carries no further hypotheses, and the proof adds none.

## How the Library proves the equality

The reverse inclusion is `RealUniformWhittaker.model_le_model`. The inclusion used here comes
from `realWhittakerIntertwinerUniformGrowth` (same module). It proves
`RealWhittakerIntertwinerUniformGrowthStatement`: for `realRank ds = r + 1`, every linear map
`B` with `IsRealWhittakerIntertwiner r ds a B` satisfies `IsRealUniformWhittakerIntertwiner r
ds a B`. The range of each such `B` then lies in `realUniformWhittakerModel r ds a`, and taking
the supremum over all `B` gives the inclusion. Its proof combines two results.

1. **Finite generation.** `Archimedean.realStandardFiniteGeneration` (module
   `Langlands.Representation.Archimedean.RealStandardFiniteGeneration`) gives a
   finite-dimensional subspace `F` of `realStandardKFinite (r + 1) ds` whose span under words
   of right derivatives along real `(r + 1) × (r + 1)` matrices is the whole module. Here
   `realRank ds = r + 1` is used. For lists in Langlands order the proof uses the Library's
   Langlands quotient theorem `realLeviLanglandsQuotient`: the compact orbit of a vector
   outside the largest proper `(𝔤, K)`-submodule generates the module. For arbitrary orders it
   uses an induction over the adjacent-block filtrations.
2. **Uniform growth from finitely many generators.**
   `RealUniformWhittaker.intertwiner_of_wordSpan_eq_top` (module
   `RealWhittakerUniformFiniteGeneration`) applies to this generating subspace. Choose a basis
   `b_i` of `F`. For each `i`, `RealWhittakerEvaluation.coefficients_uniformDerivativeGrowth`
   (module `RealWhittakerEvaluation`) gives one height exponent `d_i` for every right
   derivative word applied to `B (b_i)`. Let `N` be the maximum of the `d_i`. The functions
   bounded by `C * realMatrixHeight g ^ N` for some `C ≥ 0` form a submodule. The Lie
   compatibility of `B` turns a derivative word applied to a source vector into the same word
   of right derivatives applied to its coefficient. Hence the preimage of this submodule under
   `B` contains every word applied to every vector of `F`, and so all of
   `realStandardKFinite (r + 1) ds`. This gives one exponent `N` for all source vectors.

The derivative bounds in step 2 use the Harish-Chandra reproducing-kernel argument in its
Library form. The coefficient `B (b_i)` is pulled back to the archimedean adelic group of `ℚ`
at its real place. The pullback is finite under the compact group, and finite under the centre
of the enveloping algebra because the standard module has an infinitesimal character.
`ArchimedeanGL.finiteUniformDifferentialGrowth` (module `ArchimedeanFiniteUniformGrowthProof`)
then writes such a function as a convolution with a compactly supported kernel. Every
enveloping derivative therefore keeps the exponent of the original bound. The proof restricts
these bounds back to the real group.

## Sources

The statement records a property of Whittaker functions in H. Jacquet, *Archimedean
Rankin–Selberg integrals* (2009, registered as `jacquet-2009-archimedean-rankin-selberg`),
p. 3 display (2.1) and p. 4. See the statement's Markdown. The proof follows the Library's
results named above, not Jacquet's argument through continuous Whittaker forms on
Casselman–Wallach representations. Their Markdown cites the sources of the two ingredients:
Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995), I.2.5 and I.2.17,
for the uniform derivative growth through compact convolution, and Wallach, *Real Reductive
Groups I*, §3.3.2, for the convention of finite generation over the enveloping algebra.
