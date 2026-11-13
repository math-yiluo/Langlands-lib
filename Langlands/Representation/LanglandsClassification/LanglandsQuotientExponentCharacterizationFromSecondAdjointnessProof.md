# The exponent characterization of the Langlands quotient: proof from second adjointness

Author: Worker 168, Task 5653 (`1df73c68-230c-4ced-8325-dc9c910df8d8`). Module
`Langlands.Representation.LanglandsClassification.LanglandsQuotientExponentCharacterizationFromSecondAdjointnessProof`.

The entry theorem is
`Langlands.Aubert.General.RepresentedParabolic.langlandsQuotientExponentCharacterizationFromSecondAdjointness`.
It proves `LanglandsQuotientExponentCharacterizationFromSecondAdjointnessStatement.{u, v}`,
which is the implication

```
LeviSecondAdjointnessStatement.{u, v} →
  LanglandsQuotientExponentCharacterizationStatement.{u, v}
```

So the module proves Renard 2026, VII.4.2, the remark after the proof of (i), from second
adjointness (VI.9.6, (VI.9.6.1)). It does not prove second adjointness, and it does not
prove `LanglandsQuotientExponentCharacterizationStatement` without that premise. The
theorem uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

The proof follows the argument Renard points to ("on voit d'après ce qui précède",
printed p.243 / PDF p.249). The only premise is second adjointness. The other inputs are
proved Library results.

## Declarations

### Two lemmas about intertwiners (namespace `Langlands.Classification`)

These lemmas hold for arbitrary groups `G`, monoids `B` and complex representations.

- `exists_ne_zero_of_quotientKernel_action`. Let `τ` be irreducible, let `S ⊆ ρ` be a
  subrepresentation with an equivalence `e : S ≃ τ`, let `a : B →* G`, and let `c ∈ ℂ[B]`
  act by zero on `ρ / S` through `a` (`c ∈ groupAlgebraKernel (ρ.quotient S) a`). Let
  `incl : ξ → ρ` be an injective intertwiner, `κ : ξ → ηr` a surjective one, and suppose
  that `c` acts nonzero on `ηr` through `a`. Then there is a nonzero intertwiner `τ → ηr`.

  *Proof.* Pick `y` with `c·y ≠ 0`, write `y = κ x`, and put `x' = c·x`. Then
  `κ x' = c·y ≠ 0`. Also `incl x' = c·(incl x)` lies in `S`, because `c` kills `ρ / S`
  (`Intertwining.algebraAction_mem_of_quotientKernel`). Let `T = incl⁻¹(S)`, a
  subrepresentation of `ξ`. The composite `T → S → τ` is injective. It is nonzero because
  `x' ∈ T` and `x' ≠ 0`. Since `τ` is irreducible, the composite is surjective, hence an
  equivalence `E : T ≃ τ`. The required map is `κ ∘ (T ↪ ξ) ∘ E⁻¹`. It sends `E x'` to
  `κ x' ≠ 0`.
- `isGeneralizedEigencharacter_of_ne_zero_of_scalar`. If `a` acts on `τ` by a scalar
  character `ω` and `j : τ → ηr` is a nonzero intertwiner, then `ω` is a generalized
  eigencharacter of `ηr ∘ a`. *Proof.* For `j v ≠ 0`, `j v` is an eigenvector of `ηr ∘ a`
  with character `ω`, by the intertwining property.

### Comaximality with a character kernel (namespace `Langlands`)

`sup_characterKernel_eq_top_of_not_isGeneralizedEigencharacter`. Let `B` be a commutative
group, and let `ρ` be a representation of `B` whose action quotient
`ℂ[B] / groupAlgebraKernel ρ` is finite-dimensional. If `χ : B →* ℂˣ` is not a generalized
eigencharacter of `ρ`, then `ker χ̂ ⊔ groupAlgebraKernel ρ (id) = ⊤`, where
`χ̂ = PQKernelCharacters.characterAlgebraHom χ : ℂ[B] → ℂ`.

*Proof.* `χ̂` is surjective, so `ker χ̂` is maximal. If the supremum were proper, it would
equal `ker χ̂`. Then `χ̂` would factor through the action quotient, and
`PQFiniteActionRegularity.generalizedCharacter_of_actionQuotient` would make `χ` a
generalized eigencharacter of `ρ`. This is a contradiction.

### Real-part separation of the nonidentity pieces

`langlandsTripletOppositePiece_realPart_ne`. Take the data of a Langlands triplet
`(P = MU, σ, ψ)` with split component `a`, and an opposite parabolic `P̄` (same Levi
embedding, `P(F) ∩ P̄(F) = M(F)`). Take representatives `z` of the double cosets
`P(F)\G(F)/P̄(F)` and, for each `w` strictly below the identity coset in the Bruhat order,
a geometric-lemma intersection datum `E w h`. Let `τ = σ ⊗ ψ`. If `χ` is a generalized
eigencharacter of `A(F)` on the piece `(E w h).pieceFunctor.obj τ`, then the normalized
real part of `χ` is not `leviUnramifiedRealPart l hl a ha ψ`.

The proof is that of the published `langlandsTripletOppositePieceSeparation`
(`LanglandsTripletOppositePieceSeparation.lean`), with the inequality written out
directly. Let `x` be the offset `temperedPieceRealPartOffset` of `χ` from the piece's
unramified parameter, and let `δ` be the displacement `unramifiedPieceDisplacement` of
`ℜ(ψ)` from that parameter.

- `unramifiedPieceDisplacement_mem_nonnegCone_and_ne_zero`: `δ` is a nonzero vector of
  the cone of `P`, because `w` is not the identity coset.
- `normalizedRealPart_sub_unramifiedPieceRealPart_mem_nonnegCone`: `x` lies in the cone
  of `P̄`, because `σ` is tempered and the Jacquet module is admissible
  (`arbitraryParabolicJacquetAdmissibility`).
- `neg_mem_nonnegCone_of_opposite`: `-x` lies in the cone of `P`.
- `add_ne_zero_of_mem_nonnegCone`: `-x + δ ≠ 0`.

If `ℜ(χ) = ℜ(ψ)`, unfolding the two definitions gives `-x + δ = 0` (`abel`), a
contradiction.

### The conditional theorem

`langlandsQuotientExponentCharacterization_of_secondAdjointness (hAdj :
LeviSecondAdjointnessStatement.{u, v}) : LanglandsQuotientExponentCharacterizationStatement.{u, v}`.
The entry theorem `langlandsQuotientExponentCharacterizationFromSecondAdjointness` is this
theorem, viewed as a proof of the conditional statement.

Fix the data of the target statement and an irreducible subquotient `π` of
`I = i_P^G(τ)`, where `τ = σ ⊗ ψ`. The twist `τ` is irreducible and admissible
(`SmoothRep.isIrreducible_twist_iff`, `SmoothRep.isAdmissible_twist_iff`). `hAdj` applied
to `(P, P̄)` gives an adjunction `adj : i_P^G ⊣ r_{P̄}^G` on carriers in `Type (max u v)`.
By `isNormalizedJacquetExponent_iff_leviEigencharacter`, a normalized exponent `χ` of
`r_{P̄}^G(π)` along `A` is the same as a generalized eigencharacter of `A(F)` on the Levi
Jacquet module `r_{P̄}^G(π)` (`leviJacquetFunctor`) through `rationalPoints.map a`.

**(⇒)** Let `t : I → π` be surjective. `π` is nontrivial because it is irreducible, so
`t ≠ 0`. The Library lemma `exists_nonzero_oppositeJacquetMap` uses `adj` to give a
nonzero intertwiner `j : τ → r_{P̄}^G(π)`. Let
`ω = normalizedTemperedTwistSplitCharacter … σ … ψ`. Since `σ` is irreducible and
tempered, `A(F)` acts on `τ` by the scalar character `ω`, and the normalized real part of
`ω` is `ℜ(ψ)`. By `isGeneralizedEigencharacter_of_ne_zero_of_scalar`, `ω` is a
generalized eigencharacter of `r_{P̄}^G(π)`. So `ω` is a normalized exponent with real
part `ℜ(ψ)`.

**(⇐)** Let `χ` be a normalized exponent of `r_{P̄}^G(π)` with `ℜ(χ) = ℜ(ψ)`.

1. *Comaximality.* `representedGeometricLemma` gives representatives `z` and
   intersection data `E`. `exists_pqRegularity_pieceFiltration` gives a finite filtration
   of the regularity quotient `r_{P̄}^G(I) / F^{<1̄}` whose grades are the pieces at the
   strict predecessors of the identity coset. For each piece, the action quotient is
   finite-dimensional (`finite_actionQuotient_piece_of_irreducible`), and `χ` is not a
   generalized eigencharacter (the separation lemma above). The comaximality lemma gives
   `ker χ̂ ⊔ groupAlgebraKernel(piece) = ⊤` for each piece. `Ideal.sup_iInf_eq_top`
   extends this to the infimum over the pieces, and
   `PQFilteredKernels.sup_kernel_eq_top_iff_pieceKernels` turns it into
   `ker χ̂ ⊔ pqRegularityKernel … τ = ⊤`. Write `1 = x + c` with `x ∈ ker χ̂` and
   `c ∈ pqRegularityKernel`. Then `χ̂(c) = 1`.
2. *`c` acts nonzero on `r_{P̄}^G(π)`.* Otherwise `c` lies in the action kernel of
   `r_{P̄}^G(π)`. That kernel is contained in `ker χ̂` because `χ` occurs
   (`PQKernelCharacters.kernel_le_characterKernel`). This contradicts `χ̂(c) = 1`.
3. *A nonzero map `τ → r_{P̄}^G(π)`.* Write `π ≅ S₁ / S₂` with `S₂ ⊆ S₁ ⊆ I`. The
   Jacquet functor maps `S₁ ↪ I` to an injective map
   (`leviJacquetFunctor_map_injective`) and `S₁ ↠ π` to a surjective map
   (`leviJacquet_map_surjective`). `oppositeIdentitySupport` identifies the identity
   support image `S ⊆ r_{P̄}^G(I)` with `τ`. The element `c` kills
   `r_{P̄}^G(I) / S`, since this is the definition of `pqRegularityKernel`. Now
   `exists_ne_zero_of_quotientKernel_action`, with `ρ = r_{P̄}^G(I)`,
   `ξ = r_{P̄}^G(S₁)` and `ηr = r_{P̄}^G(π)`, gives a nonzero intertwiner
   `jj : τ → r_{P̄}^G(π)`.
4. *Back to `I → π`.* `τ` has carrier in `Type v`, but `adj` lives on `Type (max u v)`.
   Let `τ' = SmoothRep.universeLift.{u} τ` with its equivalence `eτ : τ ≃ τ'`
   (`SmoothRep.universeLiftEquiv`). Then `jj ∘ eτ⁻¹ : τ' → r_{P̄}^G(π)` is nonzero.
   `exists_surjective_leviInduction_of_nonzero_jacquetMap` (universes `u, max u v`) uses
   `adj` to give a surjection `t' : i_P^G(τ') → π`. The compatibility of induction with
   equivalences, `leviInductionEquivOfEquiv … τ τ' eτ`, gives `i_P^G(τ) ≃ i_P^G(τ')`. The
   composite `I → π` is surjective, so `π` is an irreducible quotient of `I`.

No universe is identified with another, and no hypothesis is added beyond the premise of
the conditional statement. The statement modules and their imports are unchanged.

## Imports

| Module | Used for |
| --- | --- |
| `…LanglandsClassification.LanglandsQuotientExponentCharacterizationFromSecondAdjointnessStatement` | the conditional statement (and, through it, the target and second adjointness statements) |
| `…LanglandsClassification.LanglandsTripletRegularityProof` | `finite_actionQuotient_piece_of_irreducible`, and through its imports the geometric lemma, the piece filtration, the identity support and the piece separation lemmas |
| `…LanglandsClassification.OppositeJacquetInductionQuotient` | `exists_surjective_leviInduction_of_nonzero_jacquetMap` |
| `…LanglandsClassification.RegularOppositeLanglandsHead` | `exists_nonzero_oppositeJacquetMap`, `leviJacquet_map_surjective`, `leviInductionEquivOfEquiv` |
| `…Exponents.NestedLeviJacquetExponents` | `isNormalizedJacquetExponent_iff_leviEigencharacter`, `leviJacquetFunctor_map_injective` |
| `…Exponents.NormalizedTemperedTwistExponent` | `normalizedTemperedTwistSplitCharacter` |
