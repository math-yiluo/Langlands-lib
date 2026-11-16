# Bases through a rank-two subsystem

This module proves that two linearly independent roots of a finite reduced root datum on
`ℤ^I` lie in the cone of two simple roots of a suitable base. It also proves that the Weyl
group is transitive on bases, in the form of words in simple reflections. Together these
move any two independent roots into a standard rank-two subsystem. It is pure root-system
combinatorics. It imports `Langlands.GroupScheme.Reductive.LocalSplitRootPairCommutator`,
which provides bases with prescribed positive roots and the positivity criterion
`isPos_iff_of_pos_simple`. It contains no `Prop`-valued
statement.

## Results (namespace `Langlands.LinearAlgebra`)

`x ⬝ᵥ y = ∑ j, x j * y j` is the dot product of integer vectors (Mathlib's
`Matrix.dotProduct`).

- `exists_dotProduct_perp`: let `β`, `ε` be linearly independent vectors of `ℤ^I`, with `I`
  finite. Let `x` satisfy: `n • x = p • β + q • ε` with `n, p, q ∈ ℤ` forces `n = 0`. Then some
  `w ∈ ℤ^I` has `w ⬝ᵥ β = 0`, `w ⬝ᵥ ε = 0` and `w ⬝ᵥ x ≠ 0`.
- `not_three_mem_plane`: let `P : RootDatum J (ℤ^I) (ℤ^I)` with decidable equality on `J`, and
  `b` a base. Three distinct simple roots `t₁, t₂, t₃` of `b` cannot all satisfy
  `k • P.root t = p • P.root β + q • P.root ε` with `k ≠ 0` (for given roots `β`, `ε`).
- `exists_base_rankTwo`: let `P` be reduced with finite index type `J`, and let `β`, `ε` be
  roots whose root vectors are linearly independent over `ℤ`. Then there are a base `b` in
  which `β` itself is simple, a simple root `c ≠ β` of `b`, and natural numbers `p`, `q` with
  `P.root ε = p • P.root β + q • P.root c`.

- `wordPerm P l j`: the index obtained from `j` by the reflection permutations of the letters
  of `l`, the last letter first. `root_wordPerm`: its root is `wordReflect P l (P.root j)`,
  where `wordReflect` (imported from `LocalSplitWeylFamily`) applies the reflections of `l`,
  the last letter first.
- `reflection_wordPerm_wordReflect`: `s_{w t} (w x) = w (s_t x)` for `w = wordReflect P l`.
- `isPos_map_reflection`: for the base `b.map (Equiv.reflection P s)` (Mathlib's push forward
  of `b` along the reflection automorphism `s_s`), a root `α` is positive exactly when
  `s_s α` is positive for `b`.
- `exists_word_of_base`: for two bases `b`, `b'` of a finite reduced `P`, some word `l` with
  letters in `b.support` satisfies: every simple root `s'` of `b'` has
  `P.root s' = wordReflect P l (P.root s)` for a simple root `s` of `b`.
- `wordReflect_combo`: `wordReflect P l` is `ℤ`-linear on combinations `p • x + q • y`.
- `exists_word_rankTwo`: for a base `b` and linearly independent roots `β`, `ε` of a finite
  reduced `P`, there are a word `l` with letters in `b.support`, distinct simple roots `s₁`,
  `s₂` of `b`, and natural numbers `p`, `q` with `P.root β = wordReflect P l (P.root s₁)` and
  `P.root ε = wordReflect P l (p s₁ + q s₂)`.

## Proof

**The perpendicular vector.** Put `A = β ⬝ᵥ β`, `B = β ⬝ᵥ ε`, `C = ε ⬝ᵥ ε` and
`Δ = A C - B²`. Then `Δ ≠ 0`: the vector `C β - B ε` has squared length `C Δ`. If `Δ = 0`,
this vector vanishes (Mathlib's `dotProduct_self_eq_zero`), and independence forces `C = 0`,
which is impossible since `ε ≠ 0`. The vector
`w = Δ x - (C (x ⬝ᵥ β) - B (x ⬝ᵥ ε)) β - (A (x ⬝ᵥ ε) - B (x ⬝ᵥ β)) ε` is orthogonal to `β` and
`ε` by direct expansion. Hence `w ⬝ᵥ w = Δ (w ⬝ᵥ x)`. If `w ⬝ᵥ x = 0`, then `w = 0`, so
`Δ x` lies in the span of `β`, `ε`, against the hypothesis on `x`.

**Three simple roots.** Write `kᵢ tᵢ = pᵢ β + qᵢ ε`. The cross product
`(p₂ q₃ - p₃ q₂, p₃ q₁ - p₁ q₃, p₁ q₂ - p₂ q₁)` gives a relation
`∑ cᵢ kᵢ tᵢ = 0`. Linear independence of the simple roots (`Base.linearIndepOn_root`) makes
every `cᵢ kᵢ` vanish, so `p₁ q₂ = p₂ q₁`. Then `p₂ k₁ t₁ - p₁ k₂ t₂` and `q₂ k₁ t₁ - q₁ k₂ t₂`
vanish, and independence of `t₁`, `t₂` (`Base.linearIndependent_pair_of_ne`) gives
`p₁ = q₁ = 0`. So `k₁ t₁ = 0`, and `t₁ = 0` is not a root.

**The base.** Call a root *planar* when some nonzero multiple of it lies in
`ℤ β + ℤ ε`.

- *A functional vanishing on the plane.* For each non-planar root `x`,
  `exists_dotProduct_perp` gives a functional on `ℤ^I / (ℤ β + ℤ ε)` nonzero at `x`. The
  imported `exists_dual_forall_ne_zero` combines them into one functional. Composed with the
  quotient map, it gives `h'` with `h'(β) = h'(ε) = 0`, `h'` zero on planar roots and nonzero
  on all others.
- *A functional on the plane.* Put `A = β ⬝ᵥ β`, `B = β ⬝ᵥ ε`, `C = ε ⬝ᵥ ε` and
  `Δ = A C - B²`, which is positive (the vector `C β - B ε` has squared length `C Δ`, and
  `Δ ≠ 0` by independence). The vectors `w_β = C β - B ε` and `w_ε = A ε - B β` satisfy
  `β ⬝ᵥ w_β = ε ⬝ᵥ w_ε = Δ` and `ε ⬝ᵥ w_β = β ⬝ᵥ w_ε = 0`. Let `f₀(v) = v ⬝ᵥ (w_β + N w_ε)`.
  Then `f₀(β) = Δ` and `f₀(ε) = N Δ`. For each planar root fix a relation
  `k γ = p β + q ε` with `k ≠ 0`, and choose `N` larger than every `|k| + |p|`. If `γ ≠ ±β`,
  then `q ≠ 0`, by Mathlib's `IsReduced.linearIndependent`. Hence `k f₀(γ) = Δ (p + q N)`
  has `|f₀(γ)| > Δ`. So `f₀` is nonzero on every planar root, and `β` has the smallest
  positive value among them.
- *The combination.* Put `f = M h' + f₀` with `M = 1 + ∑ |f₀(root)|`. Then `f` is nonzero on
  every root. It equals `f₀` on planar roots. On non-planar roots it has the sign of `h'`.
  In particular `β` and `ε` have `f > 0`.
- *Its base.* `g = f ∘ P.flip.Polarization` is a functional on the coroots with the same
  signs as `f` on the roots, by the imported `dual_polarization_root_pos_iff` and
  `dual_polarization_root_ne_zero` applied to the flipped datum. The imported
  `exists_base_isPos_iff` gives a base `b` whose positive roots are those where `f > 0`.

**The decomposition.** `β` and `ε` are positive for `b`. Mathlib's
`Base.exists_root_eq_sum_nat_or_neg` writes each as `∑ nⱼ sⱼ` over the simple roots `sⱼ`,
with `nⱼ ∈ ℕ`; the negative case would give `f ≤ 0`. Each simple root has `f > 0`, so
`h' ≥ 0` on it, with `h' = 0` only on planar ones. Applying `h'` gives `∑ nⱼ h'(sⱼ) = 0`, so
only planar simple roots occur. If `β` were not simple, a simple root `s ≠ β` would occur in
`β`. It is planar, not `-β` (since `f(s) > 0`), so `f(s) = f₀(s) > Δ = f(β)`; but
`f(β) = ∑ nⱼ f(sⱼ) ≥ f(s)`, which is impossible. So `β` is simple. A second simple root
`c ≠ β` occurs in `ε`, since otherwise `ε` would be a multiple of `β`. By
`not_three_mem_plane`, no third simple root occurs in `ε`.

**Transitivity.** Induct on the number `N(b')` of roots that are positive for `b` but not
for `b'`.

- *`N(b') = 0`.* Then `b` and `b'` have the same positive roots (a root or its negative is
  positive, Mathlib's `IsPos.neg_iff_not`). A simple root `s'` of `b'` is then simple for
  `b`. Otherwise Mathlib's `IsPos.exists_mem_support_pos_pairingIn` and
  `root_sub_root_mem_of_pairingIn_pos` write `s' = k + j` with `j` simple and `k` positive
  for `b` (`IsPos.sub`). This gives `s'` height at least `2` for `b'`, against
  `height_one_of_mem_support`. The empty word works.
- *`N(b') > 0`.* Some simple root `s'` of `b'` is negative for `b`. Otherwise every positive
  root of `b'` would be positive for `b`, by Mathlib's `IsPos.induction_on_add` and
  `IsPos.add`.
- *The reflected base.* Let `b''` be `b'` reflected by `s_{s'}`. Its positivity is described
  by `isPos_map_reflection`, proved with `isPos_iff_of_pos_simple` (imported from
  `LocalSplitRootPairCommutator`) applied to the height functional of
  `exists_coPairing_eq_height` composed with `s_{s'}`. Mathlib's `IsPos.reflectionPerm` shows
  that `s_{s'}` permutes the positive roots of `b'` other than `s'`. Hence `N(b'') < N(b')`:
  the root `-s'` is counted for `b'` and not for `b''`.
- *The word.* Induction gives a word `l` for `b''`. In particular `-s' = w_l(t)` for a
  simple root `t` of `b`. Then `s_{s'} = s_{-s'} = w_l s_t w_l⁻¹`, by
  `reflection_wordPerm_wordReflect`, which iterates Mathlib's `reflection_reflectionPerm`.
  So `l ++ [t]` works for `b'`.

`exists_word_rankTwo` combines `exists_base_rankTwo` with `exists_word_of_base` and the
linearity of `wordReflect`.

## Provenance and scope

This is internal derived content toward the Isomorphism Theorem over an arbitrary local
ring. It plays the role of SGA 3, Exp. XXI, Proposition 3.5.4, which finds a system of simple
roots containing a given root `α` and a root `β` with `γ ∈ ℕ α + ℕ β`, using a lexicographic
order. That proposition is used in SGA 3, Exp. XXIII, proof of Lemma 2.1.4 to reduce
commutation relations to rank-two subsystems. Transitivity of the Weyl group on bases is SGA 3,
Exp. XXI, Corollary 5.5; the induction on the number of positive roots made negative is the
usual argument for it. The present statements are the forms needed here. The construction via a
functional vanishing on the plane and a functional on the plane minimal at `β` is this module's
own argument.
