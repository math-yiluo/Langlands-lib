# The opposite-Jacquet pairing from explicit structure statements

Author: Worker 1754.

`Langlands/Representation/Exponents/LeviJacquetOppositePairingStructure.lean` proves
`LeviJacquetOppositePairingStatement` (Renard 2026, VI.9.6, Proposition, printed p.202 /
PDF p.208) from five explicit structural statements:

* `ParabolicDynamicStatement` (parabolic subgroups are dynamic parabolics `P(χ)`);
* `RationalPointFamily.UniformCompressionStabilizationStatement` (Renard VI.9.1 uniform
  stabilization);
* `RelativeRootReflectionExistenceStatement` and `CentralSplitTorusCharacterStatement`
  (which give the reciprocity of the Haar characters of `N` and `N̄` on `M`);
* `PresentationConeContractionStatement` (Renard V.5.2 (iii): elements of `C_A^+(ε)`
  conjugate a compact subset of `N(F)` into any neighbourhood of `1` once `ε` is small).

## The statement

`LeviJacquetOppositePairingStructureStatement : Prop` is the implication

```
ParabolicDynamicStatement → UniformCompressionStabilizationStatement →
  RelativeRootReflectionExistenceStatement → CentralSplitTorusCharacterStatement →
    PresentationConeContractionStatement → LeviJacquetOppositePairingStatement
```

at field universe `u` and carrier universe `v` (the antecedents that only involve the field
are taken at `u`). Its conclusion is the unchanged published VI.9.6 Proposition, with all
of its quantifiers. It is an internal reduction, not a statement from the literature.

The theorem `leviJacquetOppositePairing_of_structure` proves this implication. It is
conditional on the five propositions and does not prove any of them, so it is not an
unconditional proof of the VI.9.6 Proposition. `oppositeDynamicParabolicUniqueness` is used
from the Library, where it is proved.

## Two lemmas

* `exists_pow_mem_CAepsilon`: if `Δ` is finite, `t ∈ C_A^{++}` (every `|α(t)| < 1`) and
  `ε > 0`, then `t^j ∈ C_A^+(ε)` for all large `j`. The norm of `α` at `t^j` is
  `|α(t)|^j`, which tends to `0`; finiteness of `Δ` makes the bound uniform in `α`, and `C_A`
  is a subgroup.
* `splitComponent_point_comm`: for a compatible root presentation of `P` with split
  component `a : A → M`, the image in `G(F)` of a point of `A` commutes with every element of
  the Levi image `M(F)`. A split component is a central split torus, so its points are
  central in `M(F)`, and the point map of `m ≫ p` is a homomorphism.

## Proof of `leviJacquetOppositePairing_of_structure`

Fix `P = MN`, `P̄ = M N̄` with `mbar ≫ pbar = m ≫ p` and `P(F) ∩ P̄(F) = M(F)`, and a smooth
representation `π` of `G(F)`. Write `U = N̄(F)`, `M(F)` and `O = N(F)` for the point images.

1. *Dynamic description.* `DynamicLeviConjugacy.exists_cocharacter_parabolic_levi` gives a
   cocharacter `χ` with `P = P(χ)` and `M = M(χ)`. Then `pointImage_radical_eq_dynamic`
   gives `O = N(χ)`, and `pointImage_opposite_radical_eq_dynamic` (with the proved
   opposite-parabolic uniqueness) gives `U = N(χ⁻¹)`.
2. *Reciprocity.* `RationalPointFamily.dynamicOppositeHaarReciprocity_of_reflection_centralSplitTorus`
   gives `δ_U(m) δ_O(m) = 1` for the Haar scaling characters on `M(F)`. Then
   `closedInverseHalfCharacter_mul_eq_one_of_closedRestrictCharacter` gives
   `χ_U(m) χ_O(m) = 1` for the inverse half characters.
3. *The duality.* `RationalPointFamily.exists_isStableLiftDuality_of_dynamic` gives an
   element `g` with an opposite Iwahori contraction basis for `(U, M(F), O)` and a natural
   isomorphism `Ψ : r_U(π~) ≅ (r_O π)~` with `IsStableLiftDuality` for `g`.
4. *The isomorphism `E`.* `exists_pullback_iso_smoothDualPairing_eq` is applied to the two
   names `pointImage (mbar ≫ pbar) = pointImage (m ≫ p)` of the Levi image and the
   identifications `leviPointsEquiv pbar mbar` and `leviPointsEquiv p m`. It gives
   `E : r_{P̄}^G(π~) ≅ (r_P^G π)~` on `M(F)`; by definition of `leviJacquetFunctor` these
   are the two functors of the statement. Its pairing on classes is
   `⟨E(j_{N̄} ℓ), j_N w⟩ = stableLiftDualityPairing … Ψ π ℓ w`. `E` is chosen before the
   split component, presentation and vectors, as the statement requires.
5. *The identity on `C_A^+(ε)`.* Fix `A`, `a`, a presentation, `x` and `ℓ`.
   `exists_compact_forall_stableLiftDualityPairing_translate_eq` gives a compact
   `C ⊆ N(F)`. An open subgroup `L` of `G(F)` fixes `ℓ`, since `ℓ` is smooth.
   `PresentationConeContractionStatement` for `C` and `L` gives `ε > 0` such that
   `t c t⁻¹ ∈ L` for all `t ∈ C_A^+(ε)` and `c ∈ C`. Here `t` acts through `a ≫ m ≫ p`, which
   agrees with the statement's `incG t` by functoriality of point maps. For such `t`, the
   point `incG t` lies in `M(F)`, commutes with `M(F)` (second lemma) and conjugates `C`
   into the stabilizer of `ℓ`. So the pairing of `ℓ` with `π(incG t) x` is `ℓ(π(incG t) x)`.
   Finally `r_P^G(π)(incM t) j_N(x) = δ(incM t) · j_N(π(incG t) x)` holds by definition of
   the normalized Jacquet action. Linearity of the pairing then gives (VI.9.6.5).
6. *(VI.9.6.4).* `Δ` is finite (`ParabolicRootPresentation.finite_simpleRoots`; `G` is
   smooth, hence locally of finite type). For `t ∈ C_A^{++}`, the first lemma puts `t^j` in
   `C_A^+(ε)` for all large `j`, with the `ε` of step 5 for `x` and `ℓ`.

## Provenance

Derived. Renard proves (VI.9.6.4) and (VI.9.6.5) with the decomposition
`V^K = V^K_0 ⊕ V^K_*`, the sections `s^K_P` and VI.9.1 Remark 3 (printed p.205 / PDF
p.211). This proof replaces that route with the stable-lift duality, the derived
asymptotic evaluation of `StableLiftDualityPairing` and `StableLiftAsymptotics`, and
Renard V.5.2 (iii) (printed p.123 / PDF p.129) in the form
`PresentationConeContractionStatement`. The two lemmas are elementary supporting facts.
