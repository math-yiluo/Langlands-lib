# The subrepresentation form of the Langlands classification for `GL_n(ℂ)`

Module `Langlands.Representation.Archimedean.ComplexLanglandsSubrepresentationProof`, namespace
`Langlands.Archimedean`, universe `uV` for the module carrier.

## Statement

```
theorem complexLanglandsSubrepresentation : ComplexLanglandsSubrepresentationStatement.{uV}
```

`ComplexLanglandsSubrepresentationStatement` is the Library statement S1 of module
`Langlands.Representation.Archimedean.ComplexLanglandsQuotientReduction`; its conventions are
explained in `ComplexLanglandsQuotientReduction.md`. For every `n : ℕ`, every complex vector
space `V : Type uV`, every `ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V` and every
`π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V` with `IsComplexGKModule n ρ π`,
`IsIrreducibleGKModule ρ π` and `IsAdmissibleGKModule ρ`, there are

* a list `ds : List ComplexCharacterData` of length `n` whose exponents have non-decreasing real
  parts, `ds.Pairwise (fun d e => d.exponent.re ≤ e.exponent.re)`, and
* a nonzero linear map
  `B : V →ₗ[ℂ] kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)` with
  `IsComplexStandardEmbedding n ρ π ds B`: `B` carries `ρ(k)` to right translation by
  `k ∈ U(n)` and `π(1 ⊗ X)` to the right derivative along `X`.

So every irreducible admissible `(𝔤𝔩_n(ℂ), U(n))`-module embeds into the `U(n)`-finite part of a
principal series of `GL_n(ℂ)` whose exponents satisfy `Re t₁ ≤ ⋯ ≤ Re t_n`. This is the
subrepresentation form of the Langlands classification (Wallach 1979, Theorem 4.18 and
Lemmas 5.13, 5.15, specialized to `GL_n(ℂ)`; see `ComplexLanglandsQuotientReduction.md` for the
source discussion). The theorem has no hypotheses beyond those inside the statement.

## Proof

The proof is a composition of five Library theorems. It introduces no new mathematics.

1. `complexJacquetModuleFinite : ComplexJacquetModuleFiniteStatement` (module
   `ComplexJacquetModuleFiniteProof`). Casselman's theorem for the upper triangular Borel
   subgroup: for an irreducible admissible module, `V/𝔫V` is finite-dimensional and `𝔫V ≠ V`
   (Wallach 1979, 4.14–4.16). Its Library proof goes through the Bernstein–Gelfand comparison of
   Harish-Chandra bimodules with category `𝒪` for lower Verma modules of `𝔤𝔩_n(ℂ)`.
2. `complexJacquetRankOne : ComplexJacquetRankOneStatement` (module
   `ComplexJacquetRankOneProof`). The rank-one reordering: a nonzero Jacquet functional whose
   exponents are out of order at two adjacent positions `i, i + 1` can be replaced by one with
   the same total exponent at those positions and the order restored there. Its Library proof
   reduces to `GL_2(ℂ)` and uses moments of principal series functions.
3. `complexOrderedJacquetReduction : ComplexOrderedJacquetReductionStatement` (module
   `ComplexJacquetReduction`), the implication (1) → (2) →
   `ComplexOrderedJacquetFunctionalStatement`. Every irreducible admissible module has a nonzero
   Jacquet functional `ℓ` (vanishing on `𝔫V`, an eigenvector of the diagonal Cartan subalgebra
   with weight `(a, b)`) whose exponents satisfy `Re a_i + 2i ≤ Re a_j + 2j` for `i < j`. Its
   proof (described in `ComplexJacquetReduction.md`) identifies Jacquet functionals with common
   eigenvectors of the commuting diagonal operators on the dual of `V/𝔫V`. By (1) this dual is
   finite-dimensional and nonzero, so such eigenvectors exist and only finitely many weights
   `a` occur. A weight minimizing `Σ_k (n − k) Re a_k` is ordered: at an adjacent out-of-order
   pair, (2) would give a weight with a strictly smaller value.
4. `complexJacquetFrobenius : ComplexJacquetFrobeniusStatement` (module
   `ComplexJacquetFrobeniusProof`). Frobenius reciprocity: a nonzero Jacquet functional with
   exponents `(a, b)` gives characters `d j` with `2 (d j).exponent + (n - 1) - 2j = a_j` and
   `i (d j).weight = b_j`, and a nonzero embedding `B` of `V` into the `U(n)`-finite functions
   of the standard module of `List.ofFn d` (Wallach 1979, 4.16 and Lemma 4.17).
5. `complexLanglandsSubrepresentationJacquetReduction :
   ComplexLanglandsSubrepresentationJacquetReductionStatement` (module
   `ComplexJacquetFrobenius`), the implication (4) → (3) → S1. It feeds the ordered functional
   of (3) into (4) and takes `ds = List.ofFn d`. The relation `a_j = 2 t_j + (n - 1) - 2j`
   turns `Re a_i + 2i ≤ Re a_j + 2j` into `Re t_i ≤ Re t_j`, which is the `Pairwise` ordering
   of `ds`.

The Lean proof term is

```
complexLanglandsSubrepresentationJacquetReduction complexJacquetFrobenius
  (complexOrderedJacquetReduction complexJacquetModuleFinite complexJacquetRankOne)
```

All universe parameters are instantiated at the carrier universe `uV`, as fixed by the two
reduction statements. The theorem uses only the standard axioms `propext`, `Classical.choice`
and `Quot.sound`.
