# Proof: real and complex archimedean standard modules are admissible

Author: Worker 3657 (public task draft, revision 1, of Task 6999). Staged by Worker 378 after recompiling it.

Module `Langlands.Automorphic.ArchimedeanStandardAdmissibleProof` proves

```lean
theorem Langlands.Automorphic.archimedeanStandardAdmissible :
    ArchimedeanStandardAdmissibleStatement
```

The target is the published proposition
`Langlands.Automorphic.ArchimedeanStandardAdmissibleStatement` of module
`Langlands.Automorphic.CuspidalArchimedeanComponentStatement`, unchanged:

```lean
(∀ (n : ℕ) (ds : List RealBlock),
  Archimedean.IsAdmissibleGKModule (Archimedean.realStandardRep n ds)) ∧
∀ (n : ℕ) (ds : List ComplexCharacterData),
  Archimedean.IsAdmissibleGKModule (Archimedean.complexStandardRep n ds)
```

For every `n` and every list of blocks `ds`, the `O(n)`-finite functions of the real standard
module and the `U(n)`-finite functions of the complex standard module are admissible. For
every `d` and every continuous matrix representation `τ` of degree `d` of `K`, the space of
`K`-intertwiners from `τ` into them is finite-dimensional. This proof is the task of Task 6999
(`ae8500ea-b349-43af-a409-c33bbccb5317`).

The module imports the statement module,
`Langlands.Representation.Archimedean.RealStandardModuleAdmissible` (Worker 5220, published)
and the new helper `Langlands.Representation.Archimedean.PrincipalSeriesAdmissible` (paired
Markdown beside it). The theorem uses no axiom beyond `propext`, `Classical.choice` and
`Quot.sound`.

## Declarations

- `Langlands.Archimedean.finrank_gkIntertwiners_complexStandardRep_le n ds d τ`: the
  `U(n)`-intertwiners from a matrix representation `τ` of degree `d` into the `U(n)`-finite
  functions of `complexStandardModule n ds` form a space of dimension at most `d`.
- `Langlands.Archimedean.complexStandardAdmissible n ds`:
  `IsAdmissibleGKModule (complexStandardRep n ds)`.
- `Langlands.Automorphic.archimedeanStandardAdmissible`: the target.

## Proof

1. **Real conjunct.** This is `Langlands.Archimedean.realStandardAdmissible`
   (`RealStandardAdmissibleStatement`, which is
   `∀ n ds, IsAdmissibleGKModule (realStandardRep n ds)`), proved in Worker 5220's published
   module `RealStandardModuleAdmissible`.
2. **Complex conjunct.** By definition (module `PrincipalSeriesGKModule`),
   `complexStandardRep n ds` is the abbreviation `principalSeriesRep ℂ n
   (complexPositionCharacter ds)`, and `complexStandardModule n ds` (module `StandardModule`)
   is the abbreviation `principalSeries ℂ n (complexPositionCharacter ds)`. So the complex
   conjunct is the case `F = ℂ`, `χ = complexPositionCharacter ds` of the helper theorem
   `PrincipalSeries.isAdmissibleGKModule_principalSeriesRep`. The bound
   `finrank_gkIntertwiners_complexStandardRep_le` is the same case of
   `PrincipalSeries.finrank_gkIntertwiners_principalSeriesRep_le`.

The helper proves these for any `RCLike` field `F`, following the route of the task
objective. Every `g ∈ GL_n(F)` is `diag(a) · u · k` with `k ∈ K` (`U(n)` for `F = ℂ`). This
is the Iwasawa decomposition, obtained from the Library's
`TriangularUnitary.exists_upperTriangular_mul_unitary`. So a principal-series function is
determined by its restriction to `K`. For an intertwiner `T`, `(T x)(k) = (T (τ(k) x))(1)`,
so `T ↦ (x ↦ (T x)(1))` is an injective linear map into the dual of `ℂ^d`. Hence the
intertwiner space has dimension at most `d`. The helper's Markdown describes each lemma.

The complex conjunct holds for every list `ds`, with no rank condition: the complex standard
module is a principal series for every `ds`, and the helper needs nothing else. Neither the
continuity of `τ` nor the smoothness of the functions is used.

## Sources

- A. W. Knapp, *Representation Theory of Semisimple Groups: An Overview Based on Examples*,
  Princeton University Press, 1986, registered as
  `provided-40cace9c0f8c2361e7b3d7459f7908362f819b68114945405f1c16d968b21855` (SHA256
  `a8ae5776789005035f477f7ea79ee4a268ad43b2d84a607d55b4bedf763dbe75`). Proposition 8.4, p.207
  (PDF 221), and its proof and Remark (1), pp.207–208 (PDF 221–222): induced representations
  are admissible, with `[U(S, σ, ν)|_K : τ] ≤ dim τ`. The Lean proof is a direct argument for
  the Library's function models (see the helper Markdown), not an application of this result.
- J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations* (2024), registered
  as `getz-hahn-2024-automorphic-representations` (SHA256
  `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`). p.116 (PDF 131):
  admissible `(𝔤, K)`-modules. The statement Markdown
  (`CuspidalArchimedeanComponentStatement.md`, "Why the statements are true", step 1) gives
  the route followed here.
