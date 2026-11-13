# A nonzero map into an opposite induction comes from the identity piece

Module `Langlands.Representation.LanglandsClassification.OppositeIdentityPieceIntertwiner`.

## Purpose and provenance

Derived content for Renard VII.4.2 (ii) (Renard, *Représentations des groupes réductifs
p-adiques*, printed pp.244–246). After the parameters of two Langlands triplets are known
to agree, Renard reads `σ₁ψ₁ ≅ σ₂ψ₂` off a nonzero map
`r_{P̄} i_P(σ₁ψ₁) → σ₂ψ₂`. Only the identity piece of the geometric lemma can contribute
to such a map. This module proves that statement for an arbitrary target `ρ` whose
split component acts by a scalar character with the real part of `ψ`. The exclusion of
the nonidentity pieces repeats the argument of the published
`langlandsTripletOppositePieceSeparation`, here for a generalized character with the
real part of `ψ` rather than for an exponent of `σψ`.

## Declarations

- `Langlands.Intertwining.comp_subtypeIntertwiner_ne_zero_of_comaximal`. Let `S` be a
  subrepresentation of `ρ`, and suppose the kernel of the target action is comaximal
  with the kernel of the action on the quotient `ρ/S`. Then every nonzero intertwiner
  `Φ : ρ → τ` stays nonzero on `S`. Proof: write `1 = x + y`, with `x` killing `τ` and
  `y` killing `ρ/S`. Then `y v ∈ S` (`algebraAction_mem_of_quotientKernel`), and
  `Φ v = x Φ(v) + Φ(y v) = Φ(y v)`.
- `exists_ne_zero_intertwiningMap_of_oppositeIntertwining` (main result). Data: a
  Langlands triplet `(P = MN, σ, ψ)` for `(T, i, ν, D)`; an actual parabolic `Q = MU`
  with `lQ ≫ q = l ≫ p` and `P(k) ∩ Q(k) = M(k)`; a smooth representation `ρ` of `M(k)`
  on which `A(k)` acts through a character `c` with `normalizedRealPart c = ℜψ`. If some
  intertwining map `i_P^G(σ ⊗ ψ) → i_Q^G(ρ)` is nonzero, then so is some intertwining
  map `σ ⊗ ψ → ρ` of `M(k)`-representations.

## Proof of the main result

1. Frobenius reciprocity for `Q` gives a nonzero `Φ : r_Q i_P(τ) → ρ`, where `τ = σ ⊗ ψ`.
2. The identity support `S` (`boundarySupportImage` at the identity double coset) is
   equivalent to `τ` (`oppositeIdentitySupport`).
3. The regularity quotient `r_Q i_P(τ)/S` has a filtration whose graded pieces are the
   pieces of nonidentity double cosets (`exists_pqRegularity_pieceFiltration`, with the
   geometric-lemma data of `representedGeometricLemma`). For each such piece `E₀`:
   - its action quotient is finite (`finite_actionQuotient_piece_of_irreducible`);
   - that of `ρ` is finite, since `ρ` is scalar on `A`.

   A common generalized character `χ` would equal `c`, so `ℜχ = ℜψ`. As in the
   published separation proof, the piece displacement `δ` is nonzero and lies in the
   cone of `P` (`unramifiedPieceDisplacement_mem_nonnegCone_and_ne_zero`), and
   `U − ℜχ` lies in the cone of `P` (opposite-cone transfer of the tempered piece
   estimate). Their sum, which is `ℜψ − ℜχ`, is then nonzero
   (`add_ne_zero_of_mem_nonnegCone`), a contradiction. Hence each piece kernel is
   comaximal with the kernel of `ρ` (`sup_kernels_eq_top_iff`). So is their
   intersection, and hence the kernel of the regularity quotient
   (`PQFilteredKernels.sup_kernel_eq_top_iff_pieceKernels`).
4. By the first lemma, `Φ` is nonzero on `S`. Composing with `S ≃ τ` gives the map.
