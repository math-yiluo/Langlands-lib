# Height and `H₀` on the full minimal Levi

This internal supporting unit supplies the height comparison needed to apply the
published positive-part decay engine to actual rational points in Waldspurger
(2003), Lemma VI.2.3, printed pp.299–301. The registered source is
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
The proof is derived from the current Library's actual Cartan covering, heights
and character-normalized valuation. It does not follow the source's analytic
recurrence proof and does not prove the final orbit-decay theorem.

For a connected reductive group over a nonarchimedean local field, a maximal
split torus `i : S → G`, a generic cocharacter `ν`, a positive-definite seminorm
`N` on the full real cocharacter space, and a finite matrix representation `ρ`,
`HasMinimalLeviHeightComparison hG hi hν N ρ` means

`∃ C > 0, ∀ m : M₀(F), 1 + rationalHeight ρ m ≤ C * (1 + N(H₀(m)))`.

Here `M₀(F)` is literally `standardLeviPoints i ν ∅`, and `H₀` is the existing
`rationalMinimalH0`. Every point of this group is covered, including those
outside the maximal split torus. The norm and matrix representation are
arbitrary. No injectivity or closed-embedding condition on `ρ` is required.

`hasMinimalLeviHeightComparison_of_cartanCovering` proves this property from
compactness of the supplied subgroup `K₀` and the already existing structural
premise `StandardLeviCartanCovering F i ν ∅ K₀`. It also retains the ambient
`IsAffineHom` and `LocallyOfFiniteType` instances, connected reductivity,
maximal splitness, genericity and positive definiteness of `N`. The full target
already assumes the standard-Levi covering for every standard index, so its
empty-index case supplies this premise. The unit constructs no special compact,
Cartan covering or structural existence data.

The implemented proof proceeds as follows.

1. `exists_abs_apply_le_seminorm` makes the supplied positive-definite seminorm
   into a norm on a finite-dimensional real vector space. A linear form is
   continuous by finite dimensionality, and its operator norm bounds its
   absolute value. There is no preassigned norm or topology in this helper's
   premises.
2. `minimalLeviUniformizer y` reads the actual torus point `y(ϖ)` in the actual
   minimal Levi through `Standard.leviTorusHom` and `Standard.leviPointsEquiv`.
   Its ambient value is the published `uniformizerPowers i y`. The identity
   `rationalMinimalH0_minimalLeviUniformizer` gives `H₀(y(ϖ)) = 1 ⊗ y`, with
   the original positive-order sign convention. This is precisely the published
   `RenardCartan.centralizerValuation_uniformizerSection` formula transported
   to the minimal Levi.
3. `rationalMinimalH0_eq_zero_of_mem_compact` pulls `K₀` back along the closed
   minimal-Levi inclusion. The published `compact_comap_le_normKernel` puts
   this compact subgroup in the Levi scheme's actual common norm kernel.
   `centralizerValuation_ker` therefore makes its `H₀` zero.
4. `exists_rationalHeight_uniformizerPowers_le_seminorm` combines the published
   `exists_rationalHeight_uniformizerPowers_le_sum` with the linear-form
   bound. Thus `σ(y(ϖ)) ≤ C₁ N(1 ⊗ y)` for a nonnegative constant `C₁`.
5. The empty-index Levi covering writes every `m` as `k₁ f y(ϖ) k₂`, with
   `k₁,k₂ ∈ K₀ ∩ M₀(F)` and `f` from a fixed finite set of actual centralizer
   points. The identification `M₀(F) = Z_G(S)(F)` reads each such `f` as a
   minimal-Levi point. Compact factors have zero `H₀`, so additivity gives
   `H₀(m) = H₀(f) + 1 ⊗ y`. The seminorm triangle inequality bounds
   `N(1 ⊗ y)` by `N(H₀(m))` plus a fixed finite correction. Continuity bounds
   `σ` on `K₀`; finiteness bounds `σ(f)` and `N(H₀(f))`. Subadditivity of
   `σ` then gives `σ(m) ≤ c₀ + C₁ N(H₀(m))`. Enlarging the constant yields
   the displayed positive-constant comparison.

The proof does not shrink the closed chamber: it proves the comparison on all
of `M₀(F)`. In particular it requires no chamber restriction, lattice-section
replacement, preassigned height comparison, norm-kernel compactness assertion
for all of `M₀`, or closedness hypothesis for `ρ`.
