# The subgroup structure of the unfolding identity

Module `Langlands.Global.EisensteinConstantTerm.UnfoldingStructureProof`, namespace
`Langlands.Global`.

## Abstract semidirect decompositions

`IsRationalSemidirect R H K A`: `K, A ≤ H`, `K` normal in `H`, `K ∩ A = 1`, `H = K A`, and the
`A`-component of an element of `H ∩ R` lies in `R`. `IsRationalSemidirect.map` transports it along
group automorphisms preserving `R`.

## From dynamic products to adelic decompositions

- `rational_mem_carrier`, `mem_adelicPoints_range_comp_innerIso_inv`,
  `map_conj_adelicPoints_range_comp_innerIso_inv`, `isClosed_adelicPoints_of_isRepresentedBy`,
  `rationalImage_le_adelicPoints_range`: rational points of a subgroup functor give adelic points;
  conjugation by `w` on adelic points of `j ≫ (G.innerIso w).inv`; closedness of adelic points of
  closed representatives; `P(F) ⊆ P(𝔸)`.
- `isRationalSemidirect_of_dynamic`: if `W = (Z(χ) ∩ M) U(χ)` on every test scheme, with
  `U(χ) ≤ W ≤ P(χ)` and rational points of `W(𝔸)` coming from `W(F)`, then
  `IsRationalSemidirect G(F) W(𝔸) U(χ)(𝔸) (Z(χ) ∩ M)(𝔸)`. Normality is the Library's
  `conj_mem_unipotent`; triviality of `Z(χ) ∩ U(χ)` is `eq_one_of_mem_centralizer_of_mem_unipotent`
  with uniqueness of limits in a separated group; rationality compares the decomposition of a
  rational point over `F` with its adelic decomposition.

## Main result

`unfoldingSubgroupStructure_of_datum`: under the hypotheses of `GeometricLemmaUnfoldingStatement`,
`UnfoldingSubgroupStructure F p iU q iV w f iU' g' iV'` holds. With the cocharacters of
`exists_dynamic_unfolding_data`:

1. if `v ∈ V(𝔸)` and `w⁻¹ v w ∈ P(F)`, then `w⁻¹ v w ∈ U(τ) ∩ P(χ) ≤ U(ψ) = U'`;
2. `A = (Z(χ) ∩ U(τ))(𝔸)` complements `U(𝔸) = U(χ)(𝔸)` in `U'(𝔸) = U(ψ)(𝔸)`, by
   `isRationalSemidirect_of_dynamic` and the product formula of `IsCommutingRefinement χ τ ψ`, and
   `w A w⁻¹ ⊆ V(𝔸)` since `U(τ) = w⁻¹ V w`;
3. `B = w (Z(τ) ∩ U(χ))(𝔸) w⁻¹` complements `V(𝔸)` in `V'(𝔸)`, by the same theorem for
   `IsCommutingRefinement τ χ θ`, transported by conjugation by `w`, and `w⁻¹ B w ⊆ U(χ)(𝔸)`.

## Provenance

In the setting of Bernstein–Lapid Lemma 6.7 (3) (journal p. 207), item 1 is the rational-point
form of `U_Q ∩ w P w⁻¹ = U_Q ∩ w U_{P_w} w⁻¹`, item 3 is the adelic form of
`U_{Q_w} = (M_Q ∩ w U_P w⁻¹) ⋉ U_Q`, and item 2 is that decomposition with the roles of `(P, w)`
and `(Q, w⁻¹)` exchanged, `U_{P_w} = (M_P ∩ w⁻¹ U_Q w) ⋉ U_P`; here `Z(χ)` plays the role of the
Levi `M_P` and `Z(τ)` that of `w⁻¹ M_Q w`.
