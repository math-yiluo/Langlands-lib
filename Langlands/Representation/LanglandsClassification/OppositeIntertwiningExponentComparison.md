# Exponent comparison from a nonzero map into an opposite induction

Module `Langlands.Representation.LanglandsClassification.OppositeIntertwiningExponentComparison`.

## Purpose and provenance

Derived content supporting the proof of Renard VII.4.2 (ii) (David Renard,
*Représentations des groupes réductifs p-adiques*, registered source
`renard-2026-representations-groupes-reductifs-padiques`, printed pp.244–246 / PDF
pp.250–252). Renard compares exponents of `r_{P̄₂} i_{P₁}(σ₁ ⊗ ψ₁)` with the central
character of `σ₂ ⊗ ψ₂`. This module proves the resulting inequality in the form needed
by the two-sided inner-product argument of `DominantInvariantFormComparison`. The route
(kernel comaximality instead of Renard's direct use of exponents) is internal.

## Declarations

- `Langlands.IntertwiningMap.eq_zero_of_groupAlgebraKernel_sup_eq_top`. If the kernels
  of the group-algebra actions of `ℂ[B]` (through `φ : B → H`) on two representations
  of `H` are comaximal, every intertwining map between them is zero. Proof: write
  `1 = x + y` with `x` killing the source and `y` the target. Then
  `f v = f(x v) + f(y v) = 0 + y f(v) = 0` (`intertwining_groupAlgebra_apply`).

- `exists_weyl_sub_mem_nonnegCone_of_oppositeIntertwining` (main result). Data: two
  Langlands triplets `(P₁ = M₁U₁, σ₁, ψ₁)` and `(P₂, σ₂, ψ₂)` for the same `(T, i, ν, D)`,
  with indices `Jⱼ` and factors `fⱼ : Aⱼ → T`. Let `Q₂ = M₂V₂` be an actual parabolic
  with `lQ₂ ≫ q₂ = l₂ ≫ p₂` and `P₂(k) ∩ Q₂(k) = M₂(k)`. Let `τⱼ = σⱼ ⊗ ψⱼ`, and let
  `ŷⱼ = leviUnramifiedFullRealPart presⱼ ψⱼ` be the full real parameters on `T`, where
  `presⱼ = ⟨⟨T, i, ν, Jⱼ, fⱼ⟩, hTⱼ.1⟩`. If an intertwining map
  `t : i_{P₁}^G τ₁ → i_{Q₂}^G τ₂` is nonzero, then some relative Weyl element `w`
  satisfies

  ```
  res_{f₂}(w · ŷ₁) − res_{f₂}(ŷ₂) ∈ pres₂.nonnegCone.
  ```

  The statement installs `hG.smooth` (for the root cone) and the canonical topologies,
  like the published VII.4.1 statements. The radical of `P₂` plays no role and is not
  among the data.

## Proof of the main result

1. Frobenius reciprocity (`leviFrobeniusReciprocity` for `Q₂`) turns `t` into a nonzero
   intertwiner `Φ : r_{Q₂} i_{P₁} τ₁ → τ₂`.
2. The split component `A₂` acts on `τ₂` by a scalar character `c`
   (`normalizedTemperedTwistSplitCharacter`), whose normalized real part is
   `ℜψ₂ = leviUnramifiedRealPart ψ₂`. Hence the action quotient of `τ₂` is finite
   (`finite_actionQuotient_of_scalar`), and `c` is its only generalized character
   (`eq_of_isGeneralizedEigencharacter_of_scalar`).
3. The geometric lemma (`representedGeometricLemma` for `P₁`, `Q₂`) gives a filtration
   of `r_{Q₂} i_{P₁}` with graded pieces `E_j.pieceFunctor`. If the `A₂`-kernel `I_τ` of
   `τ₂` were comaximal with every piece kernel, then it would be comaximal with their
   intersection (`Ideal.sup_iInf_eq_top`). It would then be comaximal with the kernel of
   the whole module (`PQFilteredKernels.sup_kernel_eq_top_iff_pieceKernels`), and `Φ`
   would be zero by the first lemma. So some piece `E₀` has kernel not comaximal with
   `I_τ`.
4. The piece has a finite action quotient: `finite_actionQuotient_piece`, with the
   Jacquet module along `P'` admissible (`arbitraryParabolicJacquetAdmissibility`) and
   finitely generated (`leviJacquetFiniteType`). By `sup_kernels_eq_top_iff`, the piece
   and `τ₂` then share a generalized character `χ`, and `χ = c`.
5. Cone estimate for the piece: `normalizedRealPart_sub_unramifiedPieceRealPart_mem_nonnegCone`
   gives `ℜχ − U ∈ presQ.nonnegCone`, where `U` is the unramified piece parameter and
   `presQ` is a presentation of `Q₂` (`parabolicRootPresentationExistence`).
   `neg_mem_nonnegCone_of_opposite` moves this to `U − ℜχ ∈ pres₂.nonnegCone`.
6. The cross-Levi Weyl parameter (`exists_normalizedRealPart_piece_eq_weyl_crossLevi`,
   with `iL = pres₂.leviTorusHom`) gives `U = res_{f₂}(w ŷ₁)`. Also
   `ℜχ = ℜψ₂ = res_{f₂} ŷ₂` (`restrict_leviUnramifiedFullRealPart`).
