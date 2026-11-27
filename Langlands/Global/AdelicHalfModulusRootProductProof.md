# The half modulus of a standard parabolic as a product over positive roots

Module `Langlands.Global.AdelicHalfModulusRootProductProof`, namespace `Langlands.Global`.
It proves `halfModulusRootProduct : HalfModulusRootProductStatement`, the proposition of
`Langlands.Global.AdelicHalfModulusRootProductStatement`: for a standard parabolic family `𝓕`,
a standard index `J` and a positive real point `s` of the split component `A_J`, with image `a`
in `P_J(𝔸)`,

`‖𝓕.halfModulus J a‖² = ∏ᶠ_{β ∈ Φ⁺} |β(s)|^{m_β}`,

where `Φ⁺ = positiveRelativeRoots 𝓕.i 𝓕.ν`, `|β(s)| = PositiveRealTorus.normCharacter F (𝓕.A J)
(𝓕.f J ≫ β) s` and `m_β = Module.finrank F (weightSpace 𝓕.i β)`.

## Declarations

- `StandardParabolicFamily.positiveRootSum 𝓕 J : characterLattice (𝓕.A J)` (definition): the
  character `∑ᶠ_{β ∈ Φ⁺} m_β • (𝓕.f J ≫ β)` of `A_J`, the sum of the restrictions along
  `A_J → T` of the positive relative roots, each counted with the dimension of its weight space
  on the Lie algebra of `G`.
- `StandardParabolicFamily.characterRestrict_adjointDeterminantCharacter_splitComponent`: the
  restriction of the adjoint determinant character `Lie.adjointDeterminantCharacter (𝓕.P J)`
  along `𝓕.a J ≫ 𝓕.l J : A_J → M_J → P_J` equals `𝓕.positiveRootSum J`. In the notation of the
  sources this is `2ρ_{P_J}|_{A_J} = ∑_{β ∈ Φ⁺} m_β β|_{A_J}`.
- `PositiveRealTorus.coe_normCharacter_nsmul`, `PositiveRealTorus.coe_normCharacter_sum`,
  `PositiveRealTorus.coe_normCharacter_finsum_mem`: the real value of the normalized idele norm
  `normCharacter F T χ s` turns `n • χ` into the `n`-th power, a finite sum `∑_b n_b • g_b` into
  the product `∏_b |g_b(s)|^{n_b}`, and likewise for `∑ᶠ`/`∏ᶠ` over a finite set. They follow by
  induction from the Library's `PositiveRealTorus.normCharacter_add` and `normCharacter_zero`.
- `halfModulusRootProduct`: the main theorem.

## Proof of the character identity

Fix `𝓕` and `J`, and write `T = 𝓕.T`, `i = 𝓕.i`, `P = P_J`, `M = M_J`, `A = A_J`, `f = 𝓕.f J`.

1. **A dynamic presentation of `P_J`.** The compatibility data `𝓕.isCompatible J` contain a
   standard cocharacter `ζ` of `T` for `J` (`IsStandardCocharacter`: `⟨α, ζ⟩ = 0` for `α ∈ J`
   and `⟨α, ζ⟩ > 0` for the other simple roots) such that, with `χ = ζ ≫ i`, the image of `P` is
   the dynamic parabolic `P_G(χ)` and the image of `M` is the dynamic centralizer `Z_G(χ)` (the
   field `realization` of `ParabolicRootPresentationData.IsCompatible`). Both inclusions are
   closed immersions, so `𝓕.p J` represents `P_G(χ)` and `𝓕.l J ≫ 𝓕.p J` represents `Z_G(χ)`.
   The dynamic unipotent subgroup `U_G(χ)` is represented by the Library's
   `Dynamic.Affine.unipotentScheme χ`, an affine group of finite type with Lie coordinates
   `Lie.finiteCoordinates`. The Library's inclusion `Dynamic.centralizerToParabolic` of the
   centralizer into the parabolic equals `𝓕.l J`, since both become `𝓕.l J ≫ 𝓕.p J` after the
   monomorphism `𝓕.p J` (`Dynamic.centralizerToParabolic_comp`).
2. **Levi restriction.** By the Library's
   `Dynamic.characterRestrict_adjointDeterminantCharacter_parabolic`, the restriction of
   `det(Ad | Lie P)` to `M` is the determinant character of the conjugation action of `M` on
   `Lie U_G(χ)` plus `det(Ad | Lie M)`.
3. **The central part vanishes.** The split component `𝓕.a J : A → M` is central
   (`IsSplitComponent`), so `det(Ad | Lie M)` restricts to zero on `A`
   (`Lie.adjointDeterminantCharacter_restrict_eq_zero_of_isCentral`).
4. **The unipotent part.** Because `f ≫ i = 𝓕.a J ≫ 𝓕.l J ≫ 𝓕.p J` and
   `𝓕.torus J ≫ 𝓕.l J ≫ 𝓕.p J = i`, the map `𝓕.a J` is `f` followed by `𝓕.torus J : T → M`. The
   Library's `characterRestrict_centralizerAdjointDeterminant` computes the restriction of the
   determinant of `M` on `Lie U_G(χ)` along `𝓕.torus J` as `positiveWeightCharacter i ζ`, the
   character `∑_{⟨α, ζ⟩ > 0} m_α • α` of `T`. Hence the restriction of `det(Ad | Lie P)` to `A`
   is the restriction along `f` of `positiveWeightCharacter i ζ`, that is
   `∑ᶠ_α c_α • (f ≫ α)` with `c_α = m_α` if `⟨α, ζ⟩ > 0` and `c_α = 0` otherwise. The sum has
   finite support (`IsSplitTorus.finite_weightSupport`), so restriction passes inside it.
5. **Comparison of the summands.** It remains to compare, for every character `α` of `T`, the
   summand `c_α • (f ≫ α)` with the summand of `positiveRootSum`, which is `m_α • (f ≫ α)` for
   `α ∈ Φ⁺` and `0` otherwise.
   - If `⟨α, ζ⟩ > 0` and `m_α ≠ 0`, then `α ≠ 0` and its weight space is nonzero, so `α` is a
     relative root. It is positive: `⟨α, ν⟩ ≠ 0` because `ν` is generic, and if `⟨α, ν⟩ < 0`
     then `-α` is a positive root (relative roots are stable under negation, by the Library's
     `relativeRootSystem` and `HasRelativeRootSystem.neg_mem_relativeRoots`), so
     `⟨-α, ζ⟩ ≥ 0` (`IsStandardCocharacter.pairing_nonneg_of_positive`), a contradiction. Both
     summands equal `m_α • (f ≫ α)`.
   - If `⟨α, ζ⟩ > 0` and `m_α = 0`, both summands are `0`.
   - If `⟨α, ζ⟩ ≤ 0` and `α ∈ Φ⁺`, then `⟨α, ζ⟩ ≥ 0`, so `⟨α, ζ⟩ = 0`. A positive root
     orthogonal to the standard cocharacter `ζ` is a sum of simple roots in `J`
     (`IsStandardCocharacter.pairing_eq_zero_iff_mem_closure`), and such sums restrict to `0`
     on the split component (`ParabolicRootPresentation.restrict_eq_zero_of_mem_closure`). So
     `f ≫ α = 0` and both summands are `0`.
   - If `⟨α, ζ⟩ ≤ 0` and `α ∉ Φ⁺`, both summands are `0`.

## Proof of the main theorem

By `StandardParabolicFamily.halfModulus_eq_sqrt`, `𝓕.halfModulus J a` is the real square root of
the normalized idele norm of `det(Ad(a) | Lie P_J)`, so its squared absolute value is that norm.
Since `a` is the image of `s` under `𝓕.a J ≫ 𝓕.l J`, the norm is the norm at `s` of the
restricted character (`characterNorm_comp`). The character identity rewrites the restricted
character as `positiveRootSum J`, and `coe_normCharacter_finsum_mem`, applied to the finite set
`Φ⁺` (`IsSplitTorus.finite_positiveRelativeRoots`), turns its norm into
`∏ᶠ_{β ∈ Φ⁺} |β(s)|^{m_β}`.

## Provenance

The identity `δ_{P}(a) = |det(Ad(a) | Lie P)| = ∏_{β} |β(a)|^{m_β}`, with `β` running over the
roots of the split component on `Lie U_P`, is the standard description of the modulus of a
parabolic (Mœglin–Waldspurger, *Spectral decomposition and Eisenstein series* (1995), I.1.13,
printed p.18, and I.2.17, printed p.37; Delorme, *On the spectral theorem of Langlands*, Adv.
Math. 426 (2023), §2, p.6). The Lean proof follows the weight-space argument recorded under "Why
it is true" in the statement's Markdown, assembled from the Library's results on dynamic
parabolics and adjoint determinant characters listed above. It follows no specific textbook
proof.
