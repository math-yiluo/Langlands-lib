# The characteristic-zero degree statement from its two inputs

This module defines a reduction proposition and proves it.

## The proposition

`Langlands.AbelianScheme.IsogenyDegreeTateDeterminantCharZeroReductionStatement` is

`EndomorphismDegreeLinePolynomialStatement.{u} → IsogenyDegreeTateDeterminantNormStatement.{u} → IsogenyDegreeTateDeterminantCharZeroStatement.{u}`.

The three propositions are Library statements, all in `Langlands/AbelianScheme/`:

- `EndomorphismDegreeLinePolynomialStatement` (G1): there is `δ : (A ⟶ A) → ℚ`, equal to the degree on isogenies, with `n ↦ δ (n • φ + ψ)` polynomial of degree at most `2g` on natural numbers.
- `IsogenyDegreeTateDeterminantNormStatement` (G23): in characteristic zero, for every prime `p`, the degree of an isogeny and the determinant of its rational `p`-adic Tate map have the same `p`-adic norm, and that determinant is `0` for a non-isogeny.
- `IsogenyDegreeTateDeterminantCharZeroStatement` (S1₀): in characteristic zero, for every prime `p`, the degree of an endomorphism equals the determinant of its rational `p`-adic Tate map, with degree `0` for non-isogenies.

All three are used at the same universe `u`. The theorem `isogenyDegreeTateDeterminantCharZeroReduction` proves the reduction.

## Proof

Fix `k`, `A`, a prime `p` and `α : A ⟶ A`.

- `exists_hasRelativeDimension_of_field` gives `g` with `A.HasRelativeDimension g`.
- `p` is a unit of the global sections because `k` has characteristic zero (`isUnit_intCast_global` from `MumfordRosatiMixedEulerTraceReduction`). The published `geometricPrimeAdicRank` then shows that the rational `p`-adic Tate module `V` at the identity point has dimension `2g`. Let `b` be a basis indexed by `Fin (2 * g)`.
- `Vp : End A →+* Module.End ℚ_[p] V` is the existing `rationalEndAction` composed with `endToEnd0`. On an actual endomorphism it is `Tate.PrimeAdic.rationalMap (Over.mk (𝟙 _)) p` (`rationalEndAction_homToHom0`). `ρ` is `Vp` followed by `LinearMap.toMatrixAlgEquiv b`. By `LinearMap.det_toMatrix`, `det (ρ f) = LinearMap.det (rationalMap f)`.
- G1 at `g` gives `δ`. Take `iso = IsIsogeny`. The fields of `DegreeData ρ δ iso` are checked as follows.
  - `line` is the second part of G1.
  - `mul`: in `End A`, `β * γ = γ ≫ β`. For isogenies, `finrank_comp_of_isIsogeny` and `finrank_eq_of_isIsogeny` (from `MumfordRosatiMixedEulerTraceReduction`, based on the published `finiteFlatConstantRankComposition`) give rank `(rank γ) · (rank β)` at a point `y₀` of `A`.
  - `norm` and `zero` are the two clauses of G23.
- `DegreeData.det_eq` (module `Langlands/Algebra/DegreeDeterminant/DetComparison.lean`) gives `δ α = det (ρ α)`. For an isogeny `α`, `δ α` is its rank at every point by G1, which is the first clause of S1₀. The second clause of S1₀ is the second clause of G23.

## Provenance

Internal reduction between three Library propositions. It follows Milne, *Abelian Varieties* (author revision 2022), proof of Proposition 12.9, pp. 23–24: G1 is the input from Proposition 12.4, G23 is the displayed chain `|deg β|_l = |det T_l β|_l`, and the algebra (Lemmas 12.10 and 12.11) is in the modules `Langlands/Algebra/DegreeDeterminant/*`.
