# Bounds for the logarithms of Levi components on the opposite chart

Lean module: `Langlands.Representation.Plancherel.ParabolicLeviLogarithmBounds`,
namespace `Langlands.Plancherel`.

## Purpose and provenance

Provenance: internal. Waldspurger's proof of the convergence of the standard intertwining
integrals (*La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra* (2003),
IV.1.1, printed pp. 277–281) writes a point `x` of `Ū(F) ∩ U'(F)` in Iwasawa form `x = m u κ`.
It then controls the Levi component `m` through finitely many quantities: the half modulus
`δ_P^{1/2}(m)`, the absolute values at `m` of rational characters of `M`, and the height of
`x`. This module proves the facts about these quantities that the character decay needs:

1. the half modulus is an unramified character of `M(F)`, that is, it is trivial on the common
   norm kernel of `M` (`rationalCommonNormKernel_le_ker_parabolicLeviHalfModulus`);
2. rational characters of `G` have absolute value one at `m`
   (`abs_rationalCharacterEval_projection_eq_one`);
3. for every cocharacter `mu` of `A` admissible for the pair of parabolics, some rational
   character of `M` restricting on `A` to the positive-weight character of `mu` is bounded below
   at `m` (`exists_positiveWeightLine_le_abs`);
4. the height of `x` is bounded by a power of `max 1 |ξ(m)|⁻¹` for one rational character `ξ`
   of the parabolic (`exists_parabolicLineCharacter_rationalMatrixNorm_le`).

The statements are derived from Library results (the Haar determinant formula, Chevalley line
stabilizers, the adjoint-determinant Iwasawa bound and the opposite-intersection root
inclusions). They are not transcribed from the source.

## Setting and notation

- `F` is a nonarchimedean local field with normalized absolute value
  `|·| = LocalField.residueNormalizedAbsoluteValue F`. For an affine group scheme `G` over
  `Spec F`, `G(F) = rationalPoints G` carries the topology `rationalPointTopology F G.X`.
- `rationalCharacterEval ξ : G(F) →* Fˣ` evaluates a rational character `ξ` at rational points.
  `characterRestrict f` restricts rational characters along a homomorphism `f`.
- For a cocharacter `χ : Gm ⟶ G`, `Dynamic.parabolic χ`, `Dynamic.centralizer χ` and
  `Dynamic.unipotent χ` are the dynamic subgroup functors `P(χ)`, `Z(χ)` and `U(χ)`, and
  `Dynamic.oppositeCocharacter χ` is `t ↦ χ(t⁻¹)`. `Dynamic.Affine.parabolicScheme χ`, with
  inclusion `Dynamic.Affine.parabolicHom χ`, is the Library's affine scheme representing `P(χ)`.
- In the host section, `r : ParabolicRootPresentation p l a` presents a parabolic `p : P ⟶ G`
  with rational Levi `l : M ⟶ P` and split component `a : A ⟶ M`. `n : U ⟶ P` is a geometric
  unipotent radical. `λ = r.splitComponentCocharacter` is the presentation's split-component
  cocharacter, `Upt = U_P(F)` is given by `hUpt`, and
  `h : IsSemidirectDecomposition Ppt (parabolicLeviPointSubgroup p l) Upt` gives the Levi
  projection `h.projection : Ppt → M_P(F)`. `parabolicLeviPointHomeomorph r : M(F) ≃ₜ* M_P(F)`
  is the point homeomorphism of `l ≫ p`.

## Declarations

### Local field and point lemmas

- `distribHaarChar_eq_one_of_abs_eq_one x hx`: if `|x| = 1` for `x ∈ Fˣ`, then
  `distribHaarChar F x = 1`, that is, multiplication by `x` preserves additive Haar measure.
- `abs_rationalCharacterEval_eq_one_of_isCompact χ hK hκ`: if `K ≤ G(F)` is a compact subgroup
  and `κ ∈ K`, then `|χ(κ)| = 1` for every rational character `χ` of `G`.
- `rationalCharacterEval_eq_one_of_mem_unipotent χ lam hx`: if `G` is affine and locally of
  finite type and `x ∈ U(lam)(F)` for a cocharacter `lam`, then `χ(x) = 1` for every rational
  character `χ`.
- `rationalMatrix_map_mulVec_coordinateLine i ρ j hline q`: let `i : P ⟶ G` and let `ρ` be a
  matrix representation of `G` whose restriction to `P` stabilizes the coordinate line
  `F e_j` on every test scheme (`hline`). Then for `q ∈ P(F)`,
  `ρ(i(q)) e_j = ξ(q) e_j`, where
  `ξ = MatrixRepresentation.coordinateLineRationalCharacter (ρ.restrict i) j hline`.
- `exists_parabolicLineCharacter_rationalMatrixNorm_le χ ρ₀ hρ₀ hK`: let `G` be affine and
  locally of finite type, `χ` a cocharacter, `ρ₀` a closed representation and `K ⊆ G(F)`
  compact. There are a rational character `ξ` of `Dynamic.Affine.parabolicScheme χ`, a real
  `C > 0` and `D : ℕ` such that

  `‖x‖_{ρ₀} ≤ C · max 1 |ξ(q)|⁻¹ ^ D`

  whenever `x ∈ U(χ⁻¹)(F)`, `u ∈ U(χ)(F)`, `κ ∈ K`, `x = m u κ`, and `q ∈ P(χ)(F)` maps to
  `m`. Here `‖·‖_{ρ₀}` is `MatrixRepresentation.rationalMatrixNorm F ρ₀`, and the Lean statement
  writes the bound as `max 1 (|ξ(q)|)⁻¹ ^ D`, that is, `(max 1 |ξ(q)|⁻¹) ^ D`.

### Host lemmas

- `parabolicLeviHalfModulus r h hU : M(F) →* ℂˣ` (definition): the closed half character
  `HaarModulus.closedHalfCharacter Upt hU (parabolicLeviPointSubgroup p l) h.levi_le_normalizer`
  of the closed radical points (`hU : IsClosed Upt`), composed with
  `parabolicLeviPointHomeomorph r`. Its value at `m` is the complex number
  `δ_P(m)^{1/2}`, where `δ_P` is the modulus of conjugation on `U_P(F)`.
  `parabolicLeviHalfModulus_apply` records this unfolding.
- `rationalCommonNormKernel_le_ker_parabolicLeviHalfModulus r hn hUpt hG h hU`: if `G` is
  connected reductive, then `rationalCommonNormKernel M` is contained in the kernel of
  `parabolicLeviHalfModulus r h hU`.
- `abs_rationalCharacterEval_projection_eq_one r hn hUpt h hK ξ ψ hx pp hκ hxp`: let
  `K ≤ G(F)` be a compact subgroup, `ξ` a rational character of `G` and `ψ` a cocharacter. If
  `x ∈ U(ψ)(F)`, `pp ∈ Ppt`, `κ ∈ K` and `x = pp κ`, then `|ξ(m)| = 1` for the Levi component
  `m = h.projection pp`.
- `exists_positiveWeightLine_le_abs r hn hUpt h hK eta mu hle hadm`: let `K ⊆ G(F)` be compact
  and `eta`, `mu` cocharacters of `A`. Assume `Z(eta ∘ a ∘ l ∘ p) ≤ Z(λ ∘ a ∘ l ∘ p)` (`hle`)
  and that `mu` is admissible for `(λ, eta)` (`hadm`), that is,
  `⟨α, mu⟩ ≥ 0` for every relative root `α` of `a ≫ l ≫ p` with `⟨α, λ⟩ < 0 < ⟨α, eta⟩`. Then
  there are a rational character `ξ` of `M` and `C > 0` such that
  - `characterRestrict a ξ = positiveWeightCharacter (a ≫ l ≫ p) mu`, and
  - `C ≤ |ξ(m')|` with `m' = (parabolicLeviPointHomeomorph r).symm (h.projection pp)`,
    whenever `x ∈ U((λ ∘ a ∘ l ∘ p)⁻¹)(F)`, `x ∈ U(eta ∘ a ∘ l ∘ p)(F)`, `κ ∈ K` and
    `x = pp κ` with `pp ∈ Ppt`.

  The character `ξ` is the restriction to `M` of the adjoint determinant on `Lie U(mu)`.

## Proof outline

- *Haar measure.* Take the closed unit ball `s = {y : |y| ≤ 1}` of `F`. It is compact and
  contains the open ball `{|y| < 1}`, so its additive Haar measure is finite and positive.
  Since `|x| = 1`, `x • s = s`, and `distribHaarChar_eq_of_measure_smul_eq_mul` gives the value
  `1`. Regularity of Haar measure on `F` is the Library's
  `HarmonicAnalysis.GeneralLocalField.haarMeasure_regular`.
- *Compact subgroups.* `g ↦ |χ(g)|` is continuous and multiplicative, so it is bounded on the
  compact `K`. If `|χ(g)| > 1` for some `g ∈ K`, its powers are unbounded, which is impossible.
  So `|χ| ≤ 1` on `K`, and applying this to `κ⁻¹` gives equality.
- *Unipotent points.* For a unit `t` with `t^k → 0`, the Library's
  `mem_unipotent_iff_tendsto_conj` gives `lam(t)^k x lam(t)^{-k} → 1`. Each of these
  conjugates has `χ`-value `χ(x)`, so `χ(x) = χ(1) = 1` by continuity of `χ`.
- *Coordinate line.* The Library's `coordinateLineCharacter_action` gives
  `ρ(i(q)) e_j = ξ(q) e_j` over `Γ(Spec F)`. Apply the isomorphism `Γ(Spec F) ≅ F` entrywise.
- *Height bound.* `Chevalley.exists_line_stabilizer` for the affine representative
  `Dynamic.Affine.parabolicHom χ` gives `ρ` and `j` such that `P(χ)` is exactly the stabilizer
  of the line `F e_j` on every test scheme. So `ρ.restrict` stabilizes the line, and the
  previous lemma shows that `e_j` is an eigenvector of `P(χ)(F)` with eigenvalue `ξ`, read
  through `Dynamic.adjointDeterminantPointValue`. The Library's
  `exists_rationalMatrixNorm_le_of_weightVector` bounds `‖y‖_{ρ₀}` for `y ∈ U(χ⁻¹)(F)` by
  `C · max 1 ‖ρ(y) e_j‖ ^ D`. The fixed-point hypothesis it needs follows from
  `Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_parabolic`. Apply this bound to `y = x⁻¹`.
  Then `‖x⁻¹‖_{ρ₀} = ‖x‖_{ρ₀}`, and `x⁻¹ = κ⁻¹ u⁻¹ m⁻¹` gives
  `ρ(x⁻¹) e_j = ξ(q)⁻¹ ρ(κ⁻¹) e_j`, because `u⁻¹` fixes `e_j` by
  `eigenvalue_eq_one_of_mem_unipotent`. Finally, `‖ρ(κ⁻¹) e_j‖ ≤ B` on `K` by
  `exists_rationalVectorNorm_mulVec_inv_le`, and
  `max 1 (B |ξ(q)|⁻¹) ≤ max 1 B · max 1 |ξ(q)|⁻¹`.
- *Half modulus.* Let `χ = λ ∘ a ∘ l ∘ p`. Rewrite `Upt` as `U(χ)(F)` by `r.range_comp_radical_eq`.
  The image of `l ≫ p` lies in `Z(χ)` by `r.levi_eq_splitComponentCocharacter`, so the Library's
  `RationalPointFamily.centralizingUnipotentHaarDeterminant`, applied to the affine
  representative of `U(χ)` with its Lie coordinates, gives
  `δ_P(m) = distribHaarChar F (det(m))`, where `det` is the determinant character of the
  conjugation action of `M` on `Lie U(χ)`. For `m` in the common norm kernel, `|det(m)| = 1`,
  so `δ_P(m) = 1` by the Haar lemma, and the square root is `1`.
- *Characters of `G`.* With `m = h.projection pp`, `u = m⁻¹ pp ∈ Upt = U(λ ∘ a ∘ l ∘ p)(F)` and
  `x = m u κ`. Both `ξ(x)` and `ξ(u)` equal `1` by the unipotent lemma, and `|ξ(κ)| = 1` by the
  compact-subgroup lemma, so `|ξ(m)| = 1`.
- *Positive-weight lines.* Let `ψ = mu ∘ a ∘ l ∘ p`. The Library's
  `exists_unipotent_inf_le_and_parabolic_le` (with `hle` and `hadm`) gives `N` and
  `θ = (N mu − λ) ∘ a ∘ l ∘ p` with `U(−λ) ∩ U(eta) ≤ U(θ)` and `P(θ) ≤ P(ψ)`. Since `a` is
  central in `M`, `Z(mu ∘ a) = M`, and `Dynamic.centralizer_le_comap` gives
  `range(l ≫ p) ≤ Z(ψ) ≤ P(ψ)`. So `l ≫ p` factors as `g` through the affine representative of
  `P(ψ)` and as `f` through that of `Z(ψ)`. Put
  `ξ = characterRestrict g (adjointDeterminantCharacter hP hU cU)`. The Library's
  `exists_le_abs_adjointDeterminant` with `χ₀ = λ ∘ a ∘ l ∘ p`, `θ` and `ψ` gives `C > 0` with
  `C ≤ |det(q)|` for `q = g(m')`, because `x = m (m⁻¹ pp) κ` with `x ∈ U(θ)(F)`; the
  membership `x ∈ U(−λ)` uses `groupHom_neg_comp_eq_oppositeCocharacter`. For the restriction:
  `a ≫ g = a ≫ f ≫ centralizerToParabolic` (both compose to `a ≫ l ≫ p` with the
  monomorphism into `G`). `adjointDeterminantCentralizerRestriction` identifies the
  restriction of the parabolic determinant to `Z(ψ)` with the centralizer determinant, and
  `characterRestrict_centralizerAdjointDeterminant` (along `a ≫ f`) computes its restriction
  to `A` as `positiveWeightCharacter (a ≫ l ≫ p) mu`.
