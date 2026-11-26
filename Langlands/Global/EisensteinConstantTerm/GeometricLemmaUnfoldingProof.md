# The integration identity of the geometric lemma (proof)

Module `Langlands.Global.EisensteinConstantTerm.GeometricLemmaUnfoldingProof`. It proves
`Langlands.Global.geometricLemmaUnfolding : GeometricLemmaUnfoldingStatement.{u}`, the statement
of module `Langlands.Global.EisensteinConstantTerm.GeometricLemmaUnfoldingStatement`, with all its
hypotheses and its universe.

## Sources

J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
Math. Soc. 37 (2024), registered as `bernstein-lapid-2024-meromorphic-continuation-eisenstein`:
proof of Lemma 6.10, journal pp. 208–209, and Lemma 6.7 (2) and (3), journal p. 207.
C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series* (1995),
registered as `moeglin-waldspurger-1995-spectral-decomposition`, II.1.7, printed p. 93, formula
(4), and formula (6), which is the special case `w ∈ W(M, M')` (where `P_w = P`) of the rational
inclusion `V(F) ∩ w P(F) w⁻¹ ⊆ w U'(𝔸) w⁻¹` below.

## Implemented proof

The proof has an algebraic and an analytic part, joined by the predicate
`UnfoldingSubgroupStructure` of `UnfoldingAdelic`.

**Algebraic part** (`UnfoldingDynamic`, `UnfoldingIdentification`, `UnfoldingStructureProof`).
The parabolics `P` and `w⁻¹ Q w` contain a common maximal split torus, so they are dynamic
parabolics `P(χ)`, `P(τ)` of commuting cocharacters, with radicals `U(χ)`, `U(τ)`. Commuting
refinements `ψ` of `χ` by `τ` and `θ` of `τ` by `χ` have
`P(ψ) = (P(χ) ∩ P(τ)) U(χ)` and `U(ψ) = (Z(χ) ∩ U(τ)) U(χ)`, and symmetrically for `θ`. The
datum fixes the rational points of `P'` and `Q'`; these agree with those of `P(ψ)` and
`w P(θ) w⁻¹`, and since all four groups are smooth and connected with dense rational points,
`P' = P(ψ)` and `Q' = w P(θ) w⁻¹`, so `U' = U(ψ)` and `V' = w U(θ) w⁻¹`
(`exists_dynamic_unfolding_data`). The product formulas then give, on adelic and rational
points, `V(F) ∩ w P(F) w⁻¹ ⊆ w U'(𝔸) w⁻¹` and the closed semidirect decompositions
`U'(𝔸) = U(𝔸) ⋊ A` with `A = (Z(χ) ∩ U(τ))(𝔸)` and `V'(𝔸) = V(𝔸) ⋊ B` with
`B = w (Z(τ) ∩ U(χ))(𝔸) w⁻¹` (`unfoldingSubgroupStructure_of_datum`).

**Analytic part** (`UnfoldingStages` to `UnfoldingAbstract`, `UnfoldingReduction`). Let
`N = V(𝔸) ∩ w U'(𝔸) w⁻¹`, so `V(F) ∩ w P(F) w⁻¹ = N ∩ G(F)`, and let `ν` be a compatible quotient
measure on `N \ V(𝔸)`. Integration in stages gives
`∫_{(V(F) ∩ wP(F)w⁻¹) \ V(𝔸)} h(w⁻¹ v y) dv = ∫_{N \ V(𝔸)} ∫_{(N ∩ G(F)) \ N} h(w⁻¹ n v y) dn dν(v)`.
The semidirect decompositions `U' = U ⋊ A` and `w⁻¹ N w = (U ∩ w⁻¹ V w) ⋊ A` show that both the
inner integral and the constant term `C_{U'} h(w⁻¹ v y)` equal the average of `h(a w⁻¹ v y)` over
`(A ∩ G(F)) \ A`. On the other side, `V' = V ⋊ B` with `B ⊆ V' ∩ w U' w⁻¹`, and conjugation by `B`
preserves the normalized Haar measures of `V` and `N`; integrating over `B` first identifies
`∫_{(V'(F) ∩ wU'(𝔸)w⁻¹) \ V'(𝔸)} C_{U'} h(w⁻¹ x y) dx` with
`∫_{N \ V(𝔸)} C_{U'} h(w⁻¹ v y) dν(v)`. All Haar measures are normalized by their rational
lattices, which for the Library's measures is the mass-one normalization on the rational
quotients of the unipotent radicals. Integrability of the right side follows from the same
computations for `|h|`.

The theorem `geometricLemmaUnfolding` applies `geometricLemmaUnfolding_of_structure` to the
structure provided by `unfoldingSubgroupStructure_of_datum`.
