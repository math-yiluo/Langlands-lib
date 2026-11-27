# Proof of the reduction of the Levi transfer to the normalized congruence

Module `Langlands.Global.AdelicLeviCenterTransferReduction`. The main results are

- `Langlands.Global.leviRestrictionCenterTransfer_of_congruence :
  LeviRestrictionCenterCongruenceStatement.{u} → LeviRestrictionCenterTransferStatement.{u}`,
- `Langlands.Global.leviRestrictionCenterTransferReduction :
  LeviRestrictionCenterTransferReductionStatement.{u}`, the same theorem stated through the
  proposition of module `AdelicLeviCenterTransferReductionStatement`.

No new axioms are used. Write `R_G(u)` for `plotSmoothEnvelopingAction F G hsmooth hcalc u`,
the Library's right differentiation on `InfinitePlotSmoothFunctions F G`: on a real
generator, `R_G(X) f (x) = mvfderiv (h ↦ f(x h)) 1 X`.

## Algebra

`Langlands.Algebra.UniversalEnveloping.intertwine_of_ι`: if a linear map `Φ` satisfies
`Φ ∘ ρ₁(ι x) = ρ₂(ι x) ∘ Φ` for two algebra maps `ρ₁, ρ₂` from an enveloping algebra to
endomorphism algebras and every generator `x`, then `Φ ∘ ρ₁(u) = ρ₂(u) ∘ Φ` for every `u`. The
proof lifts `u` to the tensor algebra and inducts over scalars, generators, products and sums.

## Operators on plot-smooth functions (namespace `Langlands.Global.InfiniteAdelicGroupPoints`)

- `plotSmoothPullback j`: `f ↦ f ∘ ι_j` for the archimedean point map `ι_j` of a morphism
  `j : H ⟶ G`. Plot-smoothness is preserved because coordinate-smooth families are preserved
  by postcomposition with a morphism of schemes.
- `plotSmoothRightTranslation g`: `f ↦ f(· g)` (coordinate smoothness of products).
- `plotSmoothMul χ hχ`: multiplication by a plot-smooth function `χ`.

## Four intertwining identities

1. `plotSmoothPullback_envelopingAction`:
   `ι_j^* ∘ R_G(pointEnvelopingMap j u) = R_H(u) ∘ ι_j^*`. On a generator `z ⊗ X` both sides
   are `z` times an orbit derivative, and `groupDirectionalValue_comp_hom` (module
   `SmoothGroupHomLie`) identifies them, using smoothness of `ι_j`
   (`contMDiff_affinePointsTarget`).
2. `plotSmoothRightTranslation_envelopingAction`:
   `ρ_g ∘ R_G(u) = R_G(Ad(g) u) ∘ ρ_g`, with `Ad(g) = adelicEnvelopingConjugation F G hsmooth g`.
   On generators this is `groupDirectionalValue_rightTranslation` (module
   `SmoothGroupConjugation`).
3. `plotSmoothMul_envelopingAction`: for a smooth multiplicative `χ`,
   `χ · R_H(τ_χ u) = R_H(u) ∘ (χ ·)`, where `τ_χ = envelopingCharacterShift` sends `Y` to
   `Y + dχ(Y)`. On a generator, the product rule for `mvfderiv` and
   `groupDirectionalValue_character` (`D_X χ (m) = χ(m) dχ(X)`) give
   `D_X(χ f) = χ (D_X f + dχ(X) f)`.
4. `envelopingAction_apply_eq_zero_of_mem_curveRightIdeal`: if `f` is left invariant under a
   subset `S` of `G(F_∞)` and `x₀ S x₀⁻¹ ⊆ S`, every `w` in `curveRightIdeal F hsmooth S`
   satisfies `(R_G(w) f)(x₀) = 0`. By span induction it suffices to take
   `w = ι(1 ⊗ X) · b` with `X = c'(0)` for a smooth curve `c` through `1` in `S`. The function
   `φ = R_G(b) f` is again left `S`-invariant, because enveloping derivatives commute with left
   translations (`plotSmoothEnvelopingAction_leftTranslate`). Then
   `R_G(w) f (x₀) = d/dt φ(x₀ c(t))` at `t = 0` by the chain rule, and
   `φ(x₀ c(t)) = φ((x₀ c(t) x₀⁻¹) x₀) = φ(x₀)` is constant.

## One clause

`affinePointsTarget_conj_mem_range`: if the image of `iW : W ⟶ R` is normal in `R` (pointwise
on every test scheme, `SubgroupFunctor.IsNormal`), then for `k : H ⟶ R` and `r : R ⟶ G` the
point `(k ≫ r)(m)` of `G(F_∞)` normalizes the image of `W(F_∞)` under `iW ≫ r`. The point
`k(m)` of `R(F_∞)` conjugates the image of `W(F_∞)` into itself, and `r` is a homomorphism of
point groups.

`levi_clause_of_congruence` proves one clause of `LeviRestrictionCenterTransferStatement` from
one congruence. Let `F₀ = f`, `F_g = ρ_g F₀` and `ψ = ι^* F_g`, so that the restricted function
is `χ ψ`. Then

- `R_H(y)(χ ψ) = χ · R_H(τ_χ y) ψ` by (3);
- `R_H(τ_χ y) ψ = ι^* (R_G(j(τ_χ y)) F_g)` by (1);
- `R_G(j(τ_χ y)) F_g = R_G(z) F_g - R_G(z - j(τ_χ y)) F_g`, and the second term vanishes at
  `ι(m)` by (4), since `F_g` is left invariant under the image of `W(F_∞)` and `ι(m)`
  normalizes it;
- `R_G(z) F_g = ρ_g (R_G(z) F₀)` by (2), because `Ad(g) z = z` for central `z` and connected
  reductive `G` (`adelicEnvelopingCenterConjugation`).

## The normalizing factors

`contMDiff_parameterPower_map_ofInfinite`: for `j : G ⟶ H` and `λ ∈ ℂ ⊗ X^*(H)`,
`m ↦ j(m)^λ` is smooth on `G(F_∞)`. By `characterLog_map` the logarithm pulls back to
characters of `G`; on points with trivial finite components each character logarithm is
`archimedeanLogRegular` of a regular function with nonvanishing values
(`characterLog_apply_ofInfinite`, `characterUnits_val_eq_evaluation`), which is smooth by
`contMDiffAt_archimedeanLogRegular`. Induction over `λ` gives exponentials and their products.
`parameterPower_map_ofInfinite_mul` gives multiplicativity through `parameterCharacter`.

## Assembly

`leviRestrictionCenterTransfer_of_congruence` introduces the data of
`LeviRestrictionCenterTransferStatement`. The factors `δQ`, `δP` are smooth and multiplicative,
so their derivatives at the identity vanish on brackets (`mvfderiv_character_lie`). The premise
gives `y` with both congruences. Clause 1 is `levi_clause_of_congruence` with `R = Q`, `W = V`,
`k = l'`, `r = q`; clause 2 with `R = P`, `W = U`, `k = c ≫ l`, `r = p`, using
`c ≫ l ≫ p = (c ≫ l) ≫ p`. Normality of the images of `V` and `U` is the field `isNormal` of
`LeviSubgroup.IsGeometricUnipotentRadical`.
