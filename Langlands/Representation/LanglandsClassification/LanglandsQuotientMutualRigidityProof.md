# Two-sided opposite intertwining rigidity of Langlands triplets: proof

Module `Langlands.Representation.LanglandsClassification.LanglandsQuotientMutualRigidityProof`,
namespace `Langlands.Aubert.General.RepresentedParabolic`.

## Result

`langlandsTripletMutualOppositeIntertwiningRigidity` has exactly the published type
`LanglandsTripletMutualOppositeIntertwiningRigidityStatement.{u, v}` (module
`LanglandsQuotientMutualRigidityReduction`). It adds no hypothesis. The statement is the
part of the proof of Renard VII.4.2 (ii) after the diagram (VII.4.2.1), in two-sided form
(David Renard, *Représentations des groupes réductifs p-adiques*, registered source
`renard-2026-representations-groupes-reductifs-padiques`, printed pp.244–246 / PDF
pp.250–252). The implemented proof does not follow Renard's route through V.3.18. It uses
the two inequalities and an invariant inner product instead (see
`DominantInvariantFormComparison`).

The corollary `langlandsQuotientInjective_of_secondAdjointness (hAdj)` proves
`LanglandsQuotientInjectiveStatement` (Renard VII.4.2 (ii)) from
`LeviSecondAdjointnessStatement` alone. It applies the published reduction
`langlandsQuotientInjective_of_mutualRigidity` to `hAdj`, the published
`langlandsTripletOppositeKernel` and the theorem of this module.

## Auxiliary declarations

- `Langlands.normEqSubgroup χ₁ χ₂`: the subgroup of points where two characters
  `G → ℂˣ` have equal norms.
- `Langlands.norm_eq_of_le_normEqSubgroup`. If a subgroup `H` of finite index lies in
  `normEqSubgroup χ₁ χ₂`, the norms agree everywhere. By pigeonhole on `g^n H`, some
  `g^d` with `d ≠ 0` lies in `H`, so `‖χ₁ g‖^d = ‖χ₂ g‖^d`, and `zpow_left_inj₀`
  concludes.
- `normalizedRealPart_comp_factor_leviTorusHom`. For a presentation `r` and a split
  torus map `g : B → T`, the real part of `ψ ∘ (g ≫ r.leviTorusHom)` is
  `res_g (leviUnramifiedFullRealPart r ψ)`. This is the computation of the published
  `restrict_leviUnramifiedFullRealPart`, for an arbitrary `g`.

## Proof of the main theorem

Let the data be as in the statement, with `τⱼ = σⱼ ⊗ ψⱼ`, nonzero
`t₁ : i_{P₁} τ₁ → i_{Q₂} τ₂` and `t₂ : i_{P₂} τ₂ → i_{Q₁} τ₁`.

1. **Parameters.** `exists_weyl_sub_mem_nonnegCone_of_oppositeIntertwining`, applied to
   `t₁` (triplets in order 1, 2, parabolic `Q₂`) and to `t₂` (order 2, 1, parabolic
   `Q₁`), gives the two cone inequalities.
   `fullRealPart_eq_and_index_eq_of_mutual_mem_nonnegCone` then gives `ŷ₁ = ŷ₂` and
   `J₁ = J₂`. Here `ŷⱼ` is the full real parameter of `ψⱼ` on `T`.
2. **Common Levi.** With `J₁ = J₂`, `commonStandardLevi_pointImage_eq` gives
   `pointImage (l₁ ≫ p₁) = pointImage (l₂ ≫ p₂)`. Let `e = commonLeviIso : M₁ ≅ M₂`,
   with `e.hom ≫ l₂ ≫ p₂ = l₁ ≫ p₁`, and let `ePts = commonLeviPointsEquiv`. Its value
   is `map e.hom` (`commonStandardLeviPointsEquiv_eq_map`). The torus factors satisfy
   `pres₁.leviTorusHom ≫ e.hom = pres₂.leviTorusHom` (cancel the monomorphism
   `l₂ ≫ p₂`). Hence `a₁ ≫ e.hom = f₁ ≫ pres₂.leviTorusHom`, and therefore (`hre`)

   ```
   normalizedRealPart (ψ₂ ∘ (a₁ ≫ e.hom)) = res_{f₁} ŷ₂ = res_{f₁} ŷ₁ = ℜψ₁.
   ```

3. **Reparametrized opposite parabolic.** Let `lQ' = e.hom ≫ lQ₂ : M₁ → Q₂`. It is a
   rational Levi (`IsRationalLeviSubgroup.iso_comp`) with isomorphic multiplication
   (`isIso_subgroupMultiplication_iso_comp`), and `lQ' ≫ q₂ = l₁ ≫ p₁`. The
   `parabolic_eq` fields and `J₁ = J₂` give `pointImage p₁ = pointImage p₂`, so
   `P₁(k) ∩ Q₂(k) = M₁(k)`. `leviInductionFunctor_obj_pullback_eq` identifies
   `i_{Q₂, lQ'}(ePts^* τ₂)` with `i_{Q₂, lQ₂} τ₂`, so `t₁` becomes a nonzero map
   `i_{P₁} τ₁ → i_{Q₂, lQ'}(ePts^* τ₂)`.
4. **Identity piece.** `A₁` acts on `ePts^* τ₂` through the scalar character `c` of `τ₂`
   on the split component `a₁ ≫ e.hom` (`normalizedTemperedTwistSplitCharacter`), whose
   real part is `ℜψ₁` by `hre`. `exists_ne_zero_intertwiningMap_of_oppositeIntertwining`
   gives a nonzero `M₁(k)`-intertwiner `F : τ₁ → ePts^* τ₂`. For Levi points with
   `map (l₁ ≫ p₁) m₁ = map (l₂ ≫ p₂) m₂` we have `ePts m₁ = m₂`
   (`commonLeviPointsEquiv_eq_iff`). So `F` satisfies the common-point equivariance,
   and `exists_commonLeviEquiv_of_nonzero` (both `τⱼ` irreducible) gives the linear
   equivalence in the third conjunct. `J₁ = J₂` is the first conjunct.
5. **Norms.** By `commonLeviPoints_norm_iff` it suffices to show
   `‖ψ₁ m‖ = ‖ψ₂ (e m)‖` for `m ∈ M₁(k)`. Apply `norm_eq_of_le_normEqSubgroup` with
   `H = ⁰M₁ · A₁(k)`, the join of `rationalCommonNormKernel M₁` and the image of `a₁`.
   It has finite index by `finite_rationalCentralQuotient` and the published
   `splitComponentLattice`. On `⁰M₁` both characters are trivial: `ψ₁` by definition,
   `ψ₂ ∘ e` because `rationalUnramifiedCharacterRestrict e.hom ψ₂` is unramified. On
   `A₁(k)` the norms are `q^{-⟨ℜ, val t⟩}` (`norm_eq_rpow_normalizedRealPart`), and the
   two real parts agree by `hre`.
