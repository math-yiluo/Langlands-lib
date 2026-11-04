# The modulus of the positive torus on the standard unipotent subgroup

Author: Worker 1179. Part of task 40747bb3 (finite volume of `G(F) \ G(𝔸_F)¹`), with
Worker 235.

This module proves `positiveTorusUnipotentModulus_of_coordinates`: the Library proposition
`PositiveTorusTriangularCoordinatesStatement`
(`Langlands/GroupScheme/Rational/PositiveTorusTriangularCoordinates.lean`) implies the Library
proposition `PositiveTorusUnipotentModulusStatement`
(`Langlands/Global/AdelicSiegelMeasureReduction.lean`). The input proposition is a hypothesis
and is not proved here, so the modulus formula remains conditional on it.

## The two propositions

`PositiveTorusUnipotentModulusStatement` concerns a number field `F`, a connected reductive
`G` over `F` (affine and locally of finite type), and an algebraic Siegel setup
`IsSiegelAlgebraicSetup F G T i ν T₀ j`. Here `i : T → G` is a maximal split torus, `ν` is a
generic cocharacter, and `j : T₀ → T`. Let `N(𝔸_F) = standardUnipotentImage F G T i ν` be the
closed image in `G(𝔸_F)` of the adelic points of the standard unipotent subgroup
`N = Standard.unipotentScheme i ν ∅`. For every point `x` of the intrinsic positive torus
`A_{T₀}`, the proposition says that conjugation by `a = positiveMap x = i(j(x))` on `N(𝔸_F)`
has Haar modulus

`closedNormalizerCharacter N(𝔸_F) a = ∏ᶠ_{β ∈ Φ⁺} |β(j(x))|_𝔸 ^ dim 𝔤_β`.

The product runs over the positive relative roots `Φ⁺ = positiveRelativeRoots i ν`. The
factor `|β(j(x))|_𝔸` is `PositiveRealTorus.normCharacter F T₀ (j ≫ β) x`, and `dim 𝔤_β` is
`Module.finrank F (weightSpace i β)`. The modulus is `mulEquivHaarChar` of `h ↦ a h a⁻¹` on
`N(𝔸_F)` (Library `HaarModulus.normalizerConj`). So conjugation scales a Haar measure `μ` by
`μ(a S a⁻¹) = modulus · μ(S)`.

`PositiveTorusTriangularCoordinatesStatement` gives the following data on `N`: global functions
`t_0, …, t_{d-1}`, polynomials `P_k`, and characters `w_k` of `T`. They satisfy:

1. `aeval t` is a bijection from `F[X_0, …, X_{d-1}]` onto the coordinate ring of `N`;
2. each `P_k` involves only variables of index `< k`;
3. `t_k(x y) = t_k(x) + t_k(y) + P_k(t(x), t(y))` on `A`-points, for every `F`-algebra `A`;
4. if `ι(y) = i(s) ι(x) i(s)⁻¹` in `G(A)`, then `t_k(y) = w_k(s) t_k(x)`;
5. every `w_k` is a positive relative root;
6. each `β ∈ Φ⁺` equals `w_k` for exactly `dim 𝔤_β` indices `k`.

## Declarations

- `Langlands.GroupScheme.exists_affinePoint_evaluation`: let `U` be an affine group scheme over
  a field `F`, and let `t : Fin d → Γ(U)` be such that `aeval t` is bijective. Then for every
  `F`-algebra `A` and every `c : Fin d → A`, some `A`-point `x` has `t_k(x) = c_k` for all `k`.
  This generalizes the Library's `exists_rationalPoint_evaluation` from `A = F` to every `A`,
  with the same proof. The algebra map `Γ(U) → A` is `aeval c` composed with the inverse of
  `aeval t`.
- `Langlands.Global.AdelicGroupPoints.coordinateHomeomorph U ht`: under the same hypotheses, with
  `F` a number field, the evaluation map `x ↦ (t_k(x))_k` is a homeomorphism
  `U(𝔸_F) ≃ₜ 𝔸_F^d`. `coordinateHomeomorph_apply` records the formula. Continuity and the
  embedding property come from the Library's `isEmbedding_affinePointFiniteEvaluation`, because
  the `t_k` generate the coordinate ring. Surjectivity is the previous lemma.
- `Langlands.HaarModulus.closedNormalizerCharacter_eq_prod_of_triangular` states
  `mulEquivHaarChar_eq_prod_of_triangular` (`Langlands/HarmonicAnalysis/TriangularHaarModulus.md`)
  for the Library's `closedNormalizerCharacter`. Let `U` be a closed subgroup of a locally
  compact group, and `g` an element of its normalizer. Suppose coordinates
  `Φ : U ≃ₜ (Fin d → A)` make left translations triangular shears and conjugation by `g`
  act on coordinate `k` by `s k`, with `r k • (s k)_* ν = ν`. Then the closed normalizer
  character of `g` is `∏ k, r k`. The proof gives `U` its Borel σ-algebra and the local
  compactness of a closed subgroup, which is how the Library defines the character.
- `Langlands.Global.AdelicSiegelFactors.positiveTorusUnipotentModulus_of_coordinates`: the main
  theorem.

## Proof of the main theorem

Fix the data of `PositiveTorusUnipotentModulusStatement` and a point `x` of `A_{T₀}`. The
maximal split torus and generic cocharacter hypotheses are the first two components of
`IsSiegelAlgebraicSetup`. Apply the input proposition to obtain `t`, `P`, and `w` satisfying
(1)–(6). Give `𝔸_F` its Borel σ-algebra. It is locally compact and second countable (Library
`adeles_locallyCompactSpace`, `adeles_secondCountableTopology`).

1. **Coordinates on `N(𝔸_F)`.** Let `Φ₀ = coordinateHomeomorph N ht : N(𝔸_F) ≃ₜ 𝔸_F^d`. The
   adelic map `f = map F N G ι` is a closed embedding (Library
   `isClosedEmbedding_map_of_isClosedSubgroup`) with image `N(𝔸_F)`. So
   `v ↦ f(Φ₀⁻¹ v)`, viewed in the subgroup `N(𝔸_F)`, is a continuous bijective embedding,
   hence a homeomorphism. Its inverse `Φ` has the following property: if `f u = h`, then
   `Φ h = Φ₀ u`.
2. **Left translations are triangular.** Let `g = f(u_g)` and `v ∈ 𝔸_F^d`. By (3), the `k`-th
   coordinate of `g Φ⁻¹(v)` is `t_k(u_g) + v_k + P_k(t(u_g), v)`. The correction
   `t_k(u_g) + P_k(t(u_g), v)` depends on `v` only through the coordinates `v_l` with `l < k`,
   by (2). (The Library's `aeval_eq_of_forall_mem_vars` compares the two evaluations.)
3. **Conjugation is diagonal.** Let `s = j(x) ∈ T(𝔸_F)`, so `a = i(s)`. For `h = f(u)`,
   write `a h a⁻¹ = f(y)`. Then `ι(y) = i(s) ι(u) i(s)⁻¹`, and (4) gives
   `t_k(y) = w_k(s) t_k(u)`. Since `x` lies in the intrinsic positive torus, each value
   `w_k(s) = (j ≫ w_k)(x)` (Library `Lie.characterValue_comp`) is a positive real idele
   `full F σ_k` (Library `mem_intrinsicSubgroup_iff`). So conjugation by `a` multiplies
   coordinate `k` by `full F σ_k`.
4. **Coordinate moduli.** Let `μ` be an additive Haar measure on `𝔸_F`, made regular by
   `regular_of_isAddLeftInvariant`. By Mathlib's `addEquivAddHaarChar_smul_map` and
   `addEquivAddHaarChar_mulLeft_full` (`Langlands/Global/AdelicScalarHaarChar.md`),
   `σ_k ^ [F:ℚ] • (full F σ_k · _)_* μ = μ`. By
   `closedNormalizerCharacter_eq_prod_of_triangular`, the modulus of `a` on `N(𝔸_F)` is
   `∏_k σ_k ^ [F:ℚ]`.
5. **Regrouping by roots.** By the Library's `absoluteValue_full`, `|full F σ_k|_𝔸 = σ_k^[F:ℚ]`.
   So `σ_k^[F:ℚ] = |w_k(s)|_𝔸 = normCharacter F T₀ (j ≫ w_k) x`. Grouping the indices `k` by
   the value of `w_k` (`Finset.prod_comp`) gives
   `∏_{β ∈ image w} |β(j(x))|^{#{k : w_k = β}}`. By (5), the image of `w` lies in `Φ⁺`. By
   (6), the fiber sizes are the weight-space dimensions, and a root of `Φ⁺` outside the image
   has dimension `0`, so its factor is `1`. Mathlib's `finprod_mem_eq_prod_of_subset` then
   identifies the finite product with the `finprod` over `Φ⁺` in the statement.

## Provenance

This module is internal. It reduces the modulus statement, an instance of the formula
`δ_P(a) = |det Ad(a)|_{Lie N}|`, to the algebraic coordinate statement. The analytic input is
in `TriangularHaarModulus` and `AdelicScalarHaarChar`. The Lean argument follows no specific
textbook proof.
