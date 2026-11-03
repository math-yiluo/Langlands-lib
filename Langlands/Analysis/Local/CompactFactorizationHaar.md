# Haar measure on a group factored as `G = Q K` with `K` compact

Author: Worker 235.

This module is a helper for task 40747bb3, which proves
`Langlands.Global.AdelicGroupPoints.NormOneRationalQuotientFiniteVolumeStatement`. The module
itself contains no adelic or algebraic-group content, and it proves no adelic factorization: the
factorization `G = Q K` is a hypothesis of its theorems.

The intended later specialization is as follows. The ambient group is `G(𝔸)¹`. The closed
subgroup is the intersection `Q = P(𝔸) ∩ G(𝔸)¹`, where `P` is a parabolic subgroup. This `Q` is
in general larger than the norm-one group `P(𝔸)¹` of `P`, which is cut out by all characters of
`P` (Getz–Hahn 2024, equation (2.19), printed p. 68). The compact subgroup `K` satisfies
`G(𝔸) = P(𝔸) K`. For reductive `G` such a `K` exists by the Iwasawa decomposition, Getz–Hahn
2024, Theorem 2.7.1, equation (2.24), printed p. 71. Every positive continuous character is
trivial on the compact group `K`, so `K ≤ G(𝔸)¹`. Then `G(𝔸)¹ = Q K`: if `g ∈ G(𝔸)¹` and
`g = p k` with `p ∈ P(𝔸)`, `k ∈ K`, then `p = g k⁻¹` lies in `G(𝔸)¹`. That specialization, with
its reductive hypotheses and the Iwasawa decomposition, is a separate input and is not part of
this module. Once it is supplied, the second theorem below reduces the Haar volume of a right
`K`-saturated set, such as a Siegel set, to a left Haar volume on `Q`.

The identity `G(𝔸)¹ = P(𝔸)¹ K` with the norm-one group `P(𝔸)¹` of `P` is false in general. For
`F = ℚ`, `G = GL₂` and `P` the upper triangular Borel subgroup, the element with real component
`diag(2, 1/2)` and trivial finite components lies in `G(𝔸)¹` and in `P(𝔸)`. The positive
character `χ(p) = |p₁₁|` of `P(𝔸)` takes the value 2 on it. Suppose it equals `p k` with
`p ∈ P(𝔸)¹` and `k` in a compact subgroup `K`. Then `k` lies in the compact group `P(𝔸) ∩ K`,
where `χ` is trivial, and `χ(p) = 1`, which is a contradiction.

All declarations are in the namespace `Langlands.CompactFactorization`. This namespace is shared
with the published modules `CompactFactorizationIntegral` and `CompactFactorizationBochner`, and
no names clash.

## Provenance

The content is internal. It is the standard formula for Haar measure on a locally compact group
that factors as `G = Q K`, with `Q` a closed subgroup and `K` a compact subgroup. Up to a positive
constant, `dg` is the image of `dq dk` under `(q, k) ↦ q k`. No modulus correction appears,
because the modular function of `G` is trivial on the compact subgroup `K`. The Lean formulation
and the proof below are internal. The proof goes through the coset space of the diagonal
subgroup and the Library's comparison theorem
`Langlands.QuotientIntegration.exists_pos_smul_eq_of_rightInvariant_quotient`. It does not
follow a particular textbook proof.

## Declarations

### Right invariance on compact subgroups

Let `G` be a locally compact Hausdorff topological group with its Borel σ-algebra.

- `map_mul_right_eq_self_of_mem μ K hK hk`: let `μ` be a regular left Haar measure on `G`, `K` a
  subgroup with compact carrier and `k ∈ K`. Then `Measure.map (· * k) μ = μ`.
- `isMulRightInvariant_of_compactSpace μ`: on a compact group, every Haar measure is right
  invariant.

### The diagonal coset space

For subgroups `Q` and `K` of a group `G`:

- `diagonalSubgroup Q K : Subgroup (Q × K)` is the set of pairs `(q, k)` with `(q : G) = k`. This
  is the diagonal copy of `Q ∩ K`. Membership is `mem_diagonalSubgroup`.
- `factorMap Q K : LeftQuotient (diagonalSubgroup Q K) → G` is the map induced on right cosets
  `H (q, k)` by `(q, k) ↦ q⁻¹ k`. Here `LeftQuotient H` is the Library's quotient `H\(Q × K)` by
  the relation `QuotientGroup.rightRel H`. The map is well defined because
  `(h q)⁻¹ (h k) = q⁻¹ k` for `h ∈ Q ∩ K`. Its value on a class is `factorMap_mk`.
- `factorMap_injective`: if `q⁻¹ k = q'⁻¹ k'`, then `q' q⁻¹ = k' k⁻¹`. This element lies in
  `Q ∩ K`, so the two pairs lie in the same coset.
- `factorMap_surjective`: if every `g` is `q k` with `q ∈ Q` and `k ∈ K`, then `g` is the image of
  the class of `(q⁻¹, k)`.
- `factorMap_rightTranslate`: right translation of the coset space by `p = (q, k)` corresponds on
  `G` to the twisted translation `g ↦ q⁻¹ g k`.

### The homeomorphism

Assume in addition that `G` is locally compact, Hausdorff and second countable. Assume also that
`Q` is closed, that `K` has compact carrier, and that `G = Q K`.

- `isClosed_diagonalSubgroup`: the diagonal subgroup is closed in `Q × K`.
- `continuous_factorMap`: `factorMap` is continuous, since it is the quotient lift of the
  continuous map `(q, k) ↦ q⁻¹ k`.
- `isOpenMap_factorMap hQ hK hQK`: `factorMap` is open. Inside the proof, `Q × K` acts on `G` by
  `(q, k) • g = q g k⁻¹`. This action is continuous. It is transitive because `G = Q K`: the pair
  `(q' q⁻¹, k'⁻¹ k)` sends `q k` to `q' k'`. The group `Q × K` is σ-compact, since it is second
  countable and locally compact. The group `G` is a Baire space, since it is locally compact and
  Hausdorff. Mathlib's open mapping theorem `isOpenMap_smul_of_sigmaCompact` therefore shows that
  the orbit map `p ↦ p • 1` is open. The image of an open set `U` of the coset space under
  `factorMap` is the image under the orbit map of the open set `{p | ⟦p⁻¹⟧ ∈ U}`, because
  `p • 1 = factorMap ⟦p⁻¹⟧`.
- `factorHomeomorph hQ hK hQK : LeftQuotient (diagonalSubgroup Q K) ≃ₜ G` is the continuous open
  bijection `factorMap` as a homeomorphism. `factorHomeomorph_apply` gives its value.

### Haar measure

Let `G` also carry its Borel σ-algebra.

- `exists_pos_eq_smul_map_mul_prod μ Q hQ K hK hQK μQ μK` (**Haar measure on `G = Q K`**): for
  every Haar measure `μ` on `G`, every Haar measure `μQ` on `Q` and every Haar measure `μK` on `K`,
  there is a real `c > 0` (an `ℝ≥0`) with

  ```text
  μ = c • Measure.map (fun p : Q × K => (p.1 : G) * p.2) (μQ.prod μK).
  ```

- `exists_pos_measure_eq_of_mul_mem μ Q hQ K hK hQK μQ` (**right `K`-saturated sets**): for every
  Haar measure `μ` on `G` and every Haar measure `μQ` on `Q` there is `c > 0` such that, for every
  measurable `A ⊆ G` with `a k ∈ A` whenever `a ∈ A` and `k ∈ K`,

  ```text
  μ A = c * μQ (Subtype.val ⁻¹' A).
  ```

  The constant does not depend on `A`.

The subgroups `Q` and `K` carry their subspace topologies and subtype σ-algebras. Their second
countability and Borel property are derived inside the proofs.

## Proofs

**`map_mul_right_eq_self_of_mem`.** The measure `map (· * k) μ` is a regular left Haar measure.
Mathlib's `isMulLeftInvariant_eq_smul_of_regular` therefore makes it `c • μ` with
`c = haarScalarFactor`. Take a compact neighbourhood `V` of `1`. The set `V K` is compact,
contains a neighbourhood of `1`, and satisfies `(V K) k⁻¹ = V K`. So its measure is positive and
finite, and both measures give it the same value. Hence `c = 1`.

**`exists_pos_eq_smul_map_mul_prod`.** Write `H = diagonalSubgroup Q K` and
`e = factorHomeomorph`. Let `ν` be the image of `μQ.prod μK` under `Ψ(q, k) = q k`.

1. `H` is compact. It is closed and contained in `(Q ∩ K) × K`, which is compact because `Q` is
   closed and `K` is compact. Its Haar measure `μH` is right invariant
   (`isMulRightInvariant_of_compactSpace`), and so is `μK`.
2. `μ` is invariant under every twisted translation `g ↦ q⁻¹ g k` with `q ∈ Q` and `k ∈ K`. This
   uses left invariance and `map_mul_right_eq_self_of_mem`.
3. `ν` is invariant under the same maps. Indeed `q₀⁻¹ (q k) k₀ = Ψ(q₀⁻¹ q, k k₀)`, and the map
   `(q, k) ↦ (q₀⁻¹ q, k k₀)` preserves `μQ.prod μK` (`Measure.map_prod_map`, left invariance of
   `μQ` and right invariance of `μK`).
4. `ν` is finite on compact sets. For compact `C`, the preimage `Ψ⁻¹(C)` lies in
   `(Q ∩ C K) × K`, which is compact, and `Measure.prod_prod` bounds its measure. Also `ν ≠ 0`,
   since `ν G = μQ(Q) μK(K)` and both factors are nonzero.
5. By step 2 and `factorMap_rightTranslate`, every right translation of the coset space preserves
   `map e.symm μ`. By step 3 the same holds for `map e.symm ν`. Both measures are regular, being
   images of regular measures under a homeomorphism, and both are nonzero.
   `exists_pos_smul_eq_of_rightInvariant_quotient`, applied to `H`, `μH` and these two measures,
   gives a real `C > 0` with `map e.symm μ = ENNReal.ofReal C • map e.symm ν`.
6. Push this equality forward by `e`. Then `μ = C • ν`, and `c = C.toNNReal` is positive.

**`exists_pos_measure_eq_of_mul_mem`.** Take `μK` to be the Haar measure on the compact group `K`,
and let `c₀` be the constant of the previous theorem. Set `c = c₀ · μK(K)`. This is positive and
finite. Let `A` be measurable and right `K`-saturated. For each `k ∈ K`, the slice
`{q | q k ∈ A}` equals `Q ∩ A`, since `A k = A`. By `Measure.prod_apply_symm`, the
`μQ.prod μK`-measure of `Ψ⁻¹(A)` is `∫ μQ(Q ∩ A) dμK = μK(K) μQ(Q ∩ A)`. Multiplying by `c₀`
gives the claim.

## Scope

`G` need not be unimodular. `Q` need not be normal, and `Q ∩ K` need not be trivial. The theorem
uses Haar measures on `Q` and on `K` (left invariant, finite on compacts, positive on opens). It
does not compute the constant. Second countability of `G` is used for the open mapping theorem
and for Borel measurability of products.
