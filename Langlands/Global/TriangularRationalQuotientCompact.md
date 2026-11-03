# Compactness of `U(F) \ U(𝔸_F)` for groups with triangular coordinates

## Statements

Let `F` be a number field and `U : GroupScheme (Spec (CommRingCat.of F))` an affine group
scheme over `F`. `AdelicGroupPoints F U` is the group `U(𝔸_F)` of points over the actual
adele ring `AdeleRing (𝓞 F) F`, with the Library's coordinate-evaluation topology.
`rationalSubgroup F U` is the image of `U(F)` under the principal map `rational F U`, which
is induced by the diagonal algebra map `F → 𝔸_F`. `RationalQuotient F U` is the left coset
space `U(F) \ U(𝔸_F)` (`LeftCosetSpace (rationalSubgroup F U)`) with the quotient topology.

- `TriangularRationalQuotientCompactStatement` is the proposition that, for every number
  field `F` in universe `u` and every affine group scheme `U` over `F` with
  `HasTriangularCoordinates U` (from `Langlands.GroupScheme.TriangularCoordinates`),
  `RationalQuotient F U` is a compact space. The theorem
  `triangularRationalQuotientCompact` proves it.
- `UnipotentRationalQuotientCompactStatement` is the proposition that, for every number
  field `F` in universe `u` and every affine group scheme `U` over `F` that is locally of
  finite type, smooth, connected and unipotent (`IsUnipotent U`), `RationalQuotient F U` is
  a compact space. The module does not prove it outright. The theorem
  `unipotentRationalQuotientCompact_of_triangularCoordinates` derives it from
  `UnipotentTriangularCoordinatesStatement`, which applies because number fields have
  characteristic zero.

The module also proves the following results.

- `exists_isCompact_algebraMap_add_mem F`: there is a compact set `D ⊆ 𝔸_F` with
  `F + D = 𝔸_F`. Every adele `a` has some `f ∈ F` with `f + a ∈ D`.
- `aeval_eq_of_forall_mem_vars`: a multivariate polynomial takes the same value at two
  points that agree on its variables.
- `exists_triangular_translate P hP hD a`: let `A` be an `F`-algebra and `D ⊆ A` a set
  with `F + D = A`. Suppose each `P i` involves only variables of index `< i`. Then for
  every `a : Fin d → A` there is `c : Fin d → F` such that, for all `i`,
  `c_i + a_i + P_i(c, a) ∈ D`. Here `P_i` is evaluated with `Sum.inl j ↦ c_j` and
  `Sum.inr j ↦ a_j`.
- `exists_rationalPoint_evaluation U ht c`: if `MvPolynomial.aeval t` is bijective onto the
  coordinate ring, then every `c : Fin d → F` is the coordinate vector `(t_i(γ))_i` of a
  rational point `γ ∈ U(F)`.
- `affinePointEvaluation_rational U γ a`: a global function `a` takes, at the adelic point
  `rational F U γ`, the principal adele of its value at `γ`.
- `exists_isCompact_rational_mul_mem U hU`: if `U` has triangular coordinates, then there is
  a compact `K ⊆ U(𝔸_F)` such that every `x ∈ U(𝔸_F)` has some
  `γ ∈ rationalSubgroup F U` with `γ * x ∈ K`.
- `compactSpace_rationalQuotient_of_hasTriangularCoordinates U hU`: the compactness of
  `RationalQuotient F U` under the same hypothesis.
- `exists_isCompact_rational_mul_mem_of_isUnipotent h F U hs hc hu`: assuming
  `h : UnipotentTriangularCoordinatesStatement`, the covering form above holds for every
  smooth connected unipotent `U` that is affine and locally of finite type.

## Source and provenance

The compactness of `U(F) \ U(𝔸_F)` for unipotent `U` is a special case of
J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations* (GTM 300,
Springer, 2024), registered source `getz-hahn-2024-automorphic-representations`, SHA256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`, Theorem 2.6.3,
printed page 69 (PDF page 86). Assume `G` is smooth and connected. The theorem states that
`G(F) \ G(𝔸_F)¹` is compact if and only if every `F`-split torus `T ≤ G` satisfies
`T_{F̄} ≤ R(G_{F̄})`. Here `G(𝔸_F)¹` is the common kernel (2.19) of the absolute values of all
characters of `G`.

A unipotent group has no nontrivial characters: a character is a one-dimensional
representation, which must be trivial. So for unipotent `U` we have
`U(𝔸_F)¹ = U(𝔸_F)`. A unipotent group also contains no nontrivial torus, so the torus
condition holds. The unipotent statement here is therefore a derived special case of
Theorem 2.6.3, stated with the full adelic points.

`TriangularRationalQuotientCompactStatement`, the reduction from triangular coordinates
and the proof are internal. The algebraic input `UnipotentTriangularCoordinatesStatement`
is derived from Milne, *Algebraic Groups*, §14.d; see
`Langlands/GroupScheme/TriangularCoordinates.md`.

## Proof

1. **`𝔸_F = F + compact`.** Let `D = archimedeanFundamentalSet F ×ˢ integralFiniteAdeles F`;
   it is compact by `isCompact_archimedeanFundamentalSet` and
   `isCompact_integralFiniteAdeles`. Given an adele `a = (a_∞, a_f)`, the published lemma
   `exists_sub_mem_integralFiniteAdeles` gives `x ∈ F` with `a_f - x` integral. Then
   `exists_sub_integer_mem_archimedeanFundamentalSet` gives an integer `y ∈ 𝓞 F` with
   `a_∞ - x - y` in the archimedean fundamental set. Since `y` is integral at every finite
   place, `-(x + y) + a ∈ D`.

2. **Triangular solving.** `exists_triangular_translate` is proved by induction on the
   number `k` of indices already handled. Given `c` that works for all `i < k`, choose
   `f ∈ F` with `f + (a_k + P_k(c, a)) ∈ D` and replace `c_k` by `f`. Since `P_i` involves
   only coordinates of index `< i`, this does not change `P_i(c, a)` for any `i ≤ k`
   (`aeval_eq_of_forall_mem_vars`). The conditions for `i < k` therefore persist, and the
   condition for `i = k` holds.

3. **Rational points with prescribed coordinates.** In `exists_rationalPoint_evaluation`,
   evaluation at `c` composed with the inverse of the bijection `aeval t` is an
   `F`-algebra map from the coordinate ring to `F`. The published comparison `affineSchemePointEquiv`
   turns it into a rational point `γ` (`affineSchemePointEquiv_evaluation`). `γ` has
   coordinates `t_i(γ) = c_i`.

4. **Compact covering set.** Let `Φ : U(𝔸_F) → 𝔸_F^d` be `x ↦ (t_i(x))_i`. Because the
   `t_i` generate the coordinate ring, `Φ` is a closed embedding
   (`isClosedEmbedding_affinePointFiniteEvaluation`, using that `𝔸_F` is Hausdorff). So
   `K = Φ⁻¹(D^d)` is compact. Given `x`, step 2 with `a = Φ(x)` gives `c ∈ F^d`. Step 3
   gives `γ ∈ U(F)` with `t(γ) = c`, and `affinePointEvaluation_rational` shows that its
   principal image has coordinates `c` in `𝔸_F`. The triangular group law then gives
   `t_i(rational γ * x) = c_i + t_i(x) + P_i(c, t(x)) ∈ D` for every `i`, so
   `rational γ * x ∈ K`.

5. **Compact quotient.** The image of `K` under the continuous quotient map
   `LeftCosetSpace.mk` is compact. It is the whole space, because each class `U(F)x`
   contains `rational γ * x ∈ K` (`LeftCosetSpace.mk_subgroup_mul`). Hence
   `RationalQuotient F U` is compact. The two theorems on unipotent groups only apply the
   hypothesis `UnipotentTriangularCoordinatesStatement` to `U`.
