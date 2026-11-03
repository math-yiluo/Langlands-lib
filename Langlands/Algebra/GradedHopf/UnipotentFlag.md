# Upper unitriangular graded matrix coefficients of a unipotent graded Hopf algebra

Author: Worker 1419 designed and implemented this module and wrote this note, as part of
task `90ffbd89-a3dd-4baa-84ba-332896bbbd17` (split unipotence from the absence of zero Lie
weights). The statement of the main theorem was agreed with Worker 1389, who uses it in the same
task. All declarations are in namespace `Langlands.Algebra.GradedHopf`. The module combines four
modules of the project:

- `Langlands.Algebra.GradedHopf.BigCell` (Worker 1389), for the structure
  `GradedMatrixCoefficients`;
- `Langlands.Algebra.GradedHopf.GradedComodule` and `Langlands.Algebra.GradedHopf.Triangular`
  (Worker 1419), for graded matrix coefficients and their triangularization;
- `Langlands.GroupScheme.UnipotentMatrixCriterion.HopfSpec` (Worker 1419), for fixed vectors
  from unipotence.

## Provenance

Internal. Geometrically, the theorem says that a unipotent group scheme stabilizes a full flag
in a faithful finite-dimensional representation, with the flag compatible with a grading. The
theorem is the Hopf-algebraic form of this statement, under the explicit hypotheses below. No
source states this graded version, so no source is cited. The module does not formalize the
geometric interpretation.

## Definition

`GradedMatrixCoefficients.IsUnitriangular G`, for `G : GradedMatrixCoefficients 𝒜` over a
commutative ring `k` and a `k`-bialgebra `A`, is the proposition
`(∀ i, G.M i i = 1) ∧ ∀ i j, j < i → G.M i j = 0`: the matrix `G.M` is upper unitriangular.
`GradedMatrixCoefficients.isUnitriangular_iff` restates this, by `Iff.rfl`.

## Statement

`exists_unitriangular_of_isUnipotent` takes:

- a field `k : Type u` and `A : CommHopfAlgCat.{u} (CommRingCat.of k)`, a commutative Hopf
  algebra over `k`;
- a grading `𝒜 : ℤ → Submodule k A` with `[GradedAlgebra 𝒜]` and
  `h𝒜 : IsGradedBialgebra 𝒜` (Library, `Langlands.Algebra.GradedHopf.Basic`: the
  comultiplication maps degree `d` into total degree `d`, and the counit vanishes in nonzero
  degrees);
- `[Algebra.FiniteType k A]`;
- `hU : IsUnipotent ((hopfSpec (CommRingCat.of k)).obj (op A))`: the group scheme `Spec A`
  over `k` (Mathlib's `AlgebraicGeometry.hopfSpec`) is unipotent in the sense of the Library's
  `Langlands.GroupScheme.IsUnipotent`, so every nonzero finite-dimensional representation has
  a nonzero fixed vector.

It concludes that there is `G : GradedMatrixCoefficients 𝒜` with `G.M i i = 1` for all `i` and
`G.M i j = 0` whenever `j < i`. Here `G` consists of a size `G.n`, weights
`G.w : Fin G.n → ℤ`, and a matrix `G.M` over `A` with `Δ(Mᵢⱼ) = ∑ₗ Mᵢₗ ⊗ Mₗⱼ`, `ε(Mᵢⱼ) = δᵢⱼ`,
`Mᵢⱼ ∈ 𝒜 (w j - w i)`, and entries generating `A` as a `k`-algebra. The conclusion says that
`G.M` is upper unitriangular.

`exists_isUnitriangular_of_isUnipotent` has the same hypotheses and states the conclusion as
`∃ G : GradedMatrixCoefficients 𝒜, G.IsUnitriangular`. Its proof is the main theorem itself,
since `IsUnitriangular` unfolds to the same conjunction.

## Proof

1. Fixed vectors. For every `m` and every `b : Matrix (Fin (m + 1)) (Fin (m + 1)) A` with
   `Triangular.IsCorep k b`, `Triangular.isCorep_iff` turns `IsCorep` into the entrywise
   comultiplication and counit formulas. Then `UnipotentMatrixCriterion.exists_fixedVector_of_isUnipotent`
   gives a nonzero `v` with `∑ j, v j • b i j = v i • 1` for all `i`. The counit formula is
   matched with `(1 : Matrix _ _ k) i j` by `Matrix.one_apply`.
2. Graded coefficients. `GradedComodule.exists_corep_adjoin_eq_top h𝒜` gives `n`,
   `w : Fin n → ℤ` and `a` with `IsCorep k a`, `IsGraded 𝒜 w a` and entries generating `A`.
3. Triangularization. `Triangular.exists_unitriangular_conj 𝒜` with the fixed vectors from
   step 1 gives weights `w'` and scalar matrices `P`, `Q` with `P * Q = 1`, `Compat w w' P`
   and `conj Q P a = Q a P` upper unitriangular.
4. Assembly. `G` has size `n`, weights `w'` and matrix `conj Q P a`:
   - comultiplication and counit formulas: `IsCorep.conj` with `P * Q = 1`, then
     `isCorep_iff`;
   - degrees: `IsGraded.conj`, with `Compat w' w Q` from `Compat.of_mul_eq_one` and
     `Q * P = 1` (`mul_eq_one_comm`);
   - generation: `adjoin_conj`, since the entries of `a` are combinations of the entries of
     `conj Q P a`.

   The unitriangularity is the conclusion of step 3.
