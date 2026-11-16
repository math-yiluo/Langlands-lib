# Heights of rational matrices and archimedean entry bounds

Module `Langlands.Global.RankinSelberg.WhittakerExpansionCore.WhittakerHeights`, namespace
`Langlands.Global.RankinSelbergGlobal.Unfolding`. These are helper lemmas for half (S) of the
Whittaker expansion (see `Interface`). The induction of half (S) bounds `W_f(ρ x)` uniformly
over rational matrices `ρ` of bounded height and points `x` of a fixed compact set. This module
defines that height and proves the elementary entry bounds the induction needs. The notion of
height used here (a pair: a bound `T` on entries and a common denominator `e`) is this project's
own bookkeeping device, not a definition from the literature.

## Section `RationalPoint`

* `ratPoint F ρ` is the adelic point of a rational matrix `ρ ∈ GL_n(F)`: the image of
  `AdelicGL.rational F n ρ` under the inverse of `GeneralLinearGroupPoints.adelicEquiv`.
* `ratPoint_mul`, `ratPoint_one`, `ratPoint_inv`: `ratPoint` is multiplicative, because both maps
  in its definition are group homomorphisms.
* `padRational_eq_ratPoint`: `padRational F hk g = ratPoint F (padGL hk g)`, from
  `padGL_rational`.
* `ratPoint_eq_rational`: `ratPoint F ρ` is the rational point of the group scheme attached to
  `ρ` through `GeneralLinearGroupPoints.rationalEquiv`. Proof: apply the injective map
  `adelicEquiv` and use `adelicEquiv_rational`.
* `ratPoint_mem_rationalSubgroup` and `detNorm_ratPoint` (the determinant norm of `ratPoint F ρ`
  is `1`) follow from `ratPoint_eq_rational` and `detNorm_rational`.
* `archCoord_mul`, `archCoord_inv`: the archimedean coordinates (`archCoord`, from
  `WhittakerCharDeriv`) are multiplicative.
* `archCoord_ratPoint_apply`: the `(a, b)` entry of the archimedean coordinates of `ratPoint F ρ`
  is `mixedEmbedding F (ρ a b)`. Proof: unfold the definitions and use
  `InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp`.
* `continuous_archCoord`: `archCoord` is continuous, as a composite of
  `archimedeanGLCoordinates`, `AdelicGL.infinite` and `adelicHomeomorph`.

## Section `Norms`

* `norm_mixedEmbedding_le_iff`: `‖mixedEmbedding F x‖ ≤ t` if and only if `w x ≤ t` for every
  infinite place `w`. The norm on the mixed space is the supremum of the norms at the places
  (`mixedEmbedding.norm_eq_sup'_normAtPlace`).
* `le_norm_mixedEmbedding` (each `w x` is at most the mixed norm) and
  `norm_mixedEmbedding_one_le` (the mixed norm of `1` is at most `1`) are consequences.
* `norm_matrix_mul_apply_le`: over a normed ring, if the entries of `A` and `B` have norm at most
  `α` and `β`, then the entries of `A B` have norm at most `n α β`. Proof: the triangle
  inequality and `norm_mul_le`.

## Section `Heights`

* `EntryHeightLE F T e M`: every entry `M a b` satisfies `‖mixedEmbedding F (M a b)‖ ≤ T`, and
  `e · M a b` is integral over `ℤ`.
* `HeightLE F T e ρ`: both `ρ` and `ρ⁻¹` satisfy `EntryHeightLE F T e`.
* `EntryHeightLE.mul`: if `M` has entry height `(T₁, e₁)` and `N` has entry height `(T₂, e₂)`,
  then `M N` has entry height `(n T₁ T₂, e₁ e₂)`. The norm bound is `norm_matrix_mul_apply_le`
  applied to the entrywise mixed embeddings. Integrality: `e₁ e₂ (M N)_{ab}` is the sum over `c`
  of the products `(e₁ M_{ac})(e₂ N_{cb})` of integral elements.
* `HeightLE.mul`: the same for `HeightLE`, using `(g ρ)⁻¹ = ρ⁻¹ g⁻¹`.
* `EntryHeightLE.one`, `HeightLE.one`: the identity has height `(1, e)` for every `e`.
* `EntryHeightLE.pad`, `HeightLE.pad`: if `T ≥ 1`, padding `g ↦ diag(g, I)` (`padGL`) preserves
  height `(T, e)`. The new entries are those of the identity, and `padGL` commutes with
  inversion because it is a group homomorphism.

## Section `Entries`

* `norm_archCoord_ratPoint_mul_apply_le`: if `ρ` has height `(T, e)` and the archimedean
  coordinates of `x` and their inverse have entries of norm at most `B`, then the archimedean
  coordinates of `ρ x` and their inverse have entries of norm at most `n T B`. Proof:
  multiplicativity of `archCoord`, `archCoord_ratPoint_apply`, and `norm_matrix_mul_apply_le`.
* `exists_archCoord_bound`: on a compact set `C` of points there is a constant `B ≥ 0` bounding
  the entries of the archimedean coordinates and of their inverse. The map from a point to the
  family of these entry pairs is continuous, so it is bounded on `C`
  (`IsCompact.exists_bound_of_continuousOn`).
* `norm_colConj_apply_le`: if the entries of the archimedean coordinates of `y` and of their
  inverse have norm at most `τ`, and the column direction `w` has entries of norm at most `ω`,
  then the conjugated column direction `colConj F j y w = y_∞⁻¹ colMatrix(w) y_∞` (from
  `WhittakerCharDeriv`) has entries of norm at most `(r + 1)((r + 1) τ ω) τ`. Proof: apply
  `norm_matrix_mul_apply_le` twice; the entries of `colMatrix j w` are entries of `w` or zero.
