# Blocks of distinct even paths commute

Provenance: internal helper for the even-chain Galois data proof (Task 5375).
That target is derived from Robert Steinberg, *Regular elements of semi-simple
algebraic groups*, Publ. Math. IHÉS 25 (1965), 49–80 (source
`steinberg-1965-regular-elements-semisimple-groups`); the Markdown of the
target `EvenChainGaloisDataStatement` gives the full source account.
Steinberg's 9.4 (printed pp.72–73) excludes components of type `A_n` with `n`
even. There the roots in one Galois orbit of simple roots are orthogonal, so
the factors of an orbit commute. In a component of type `A_{2m}`, the notation
before Theorem 9.11 (printed p.74) modifies only the factors of the middle pair
`α_m`, `α_{m+1}`, using the root `α_m + α_{m+1}`. The rationality of the
modified product is proved in the last paragraph of printed p.77 (proof of
9.7 e)), where the `k_1`, `Γ_1` argument of 9.4 reduces the proof to one
component. The implemented proof treats all components at once instead. This
module proves, as an internal derived result, that the factor blocks attached
to the middle pairs of different paths commute, so that the Galois action may
permute them.

Throughout, `k` is a field, `G` an affine group scheme over `Spec k`, and
`p : SplitPinning G`. Rational points are those over `Over.mk (𝟙 _)`, and
`U(χ)` denotes the subgroup functor `RelativeRoot.subgroup p.inclusion χ`.

## Root combinatorics

- `mixed_sum_ne_zero_not_root`: let `d` assign an integer to each simple root.
  If `d s > 0` and `d t < 0` for some simple roots `s, t`, then
  `∑ d_j • root j` is neither zero nor a root of `p.inclusion`.
- `two_mixed_ne_zero_not_root`: for four pairwise distinct simple roots
  `a, b, a', b'`, and natural numbers with `n₁ + n₂ > 0` and `m₁ + m₂ > 0`,
  `(n₁ a + n₂ b) - (m₁ a' + m₂ b')` is neither zero nor a root.
- `ne_zero_not_root_of_reflection`: if the image of a character `x` under a
  root reflection is neither zero nor a root, the same holds for `x`.
  `neg_ne_zero_not_root`: the same for `-x`.
- `pos_add_ne_zero_not_root`: let `a, b, a', b'` be pairwise distinct simple
  roots with `a, b` orthogonal to `a', b'` and `⟨b', a'^∨⟩ = -1`. Let
  `n₁ + n₂ > 0` and `m > 0`, and let `v` be `a'`, `b'` or `a' + b'`. Then
  `(n₁ a + n₂ b) + m v` is neither zero nor a root.
- `exists_nsmul_eq_of_pos`: a positive multiple of `a`, `b` or `a + b` is
  `n₁ a + n₂ b` with `n₁ + n₂ > 0`.
- `MiddleChar a b χ`: `χ` is one of `a`, `b`, `a + b`, `-(a + b)`.
- `middleChar_ne_zero_not_root`: under the hypotheses of
  `pos_add_ne_zero_not_root`, for `MiddleChar a b χ`, `MiddleChar a' b' ψ` and
  `n, m > 0`, the character `n χ + m ψ` is neither zero nor a root.

## Group statements

- `SteinbergModifiedData.blockSubgroup D`: for merged data `D` on the simple
  roots `D.a, D.b` with merged root `D.alpha`, the subgroup
  `(U(a)(k) ⊔ U(b)(k)) ⊔ p.rootSup D.alpha` of rational points.
  `p.rootSup α` is the published subgroup `U(α)(k) ⊔ U(-α)(k)`.
- `SteinbergModifiedData.middleChar_of_eq`, `middleChar_ne_zero`: the
  characters `a, b, ±α` are middle characters of `a, b` and are nonzero.
- `SteinbergModifiedData.commute_of_mem_blockSubgroup`: let `D, D'` be merged
  data whose simple roots are pairwise distinct, with `D.a, D.b` orthogonal to
  `D'.a, D'.b` and `⟨D'.b, D'.a^∨⟩ = -1`. Then every element of
  `D.blockSubgroup` commutes with every element of `D'.blockSubgroup`.
- For `C : p.EvenChainData J` and normalized simple-root parametrizations `x`:
  - `EvenChainData.block_mem`: every block `C.block x c ε s t` lies in
    `(C.modified c).blockSubgroup`.
  - `modified_a_mem`, `modified_b_mem`: the merged roots of `c` lie on
    `C.path c`.
  - `ne_of_mem_path`, `isOrthogonal_of_mem_path`: simple roots on the paths of
    distinct indices `c ≠ c'` are distinct and orthogonal.
  - `pairing_modified_b_a`: `⟨b, a^∨⟩ = -1` for the merged data of each path.
  - `commute_of_mem_blockSubgroup`: for `c ≠ c'`, elements of the two block
    subgroups commute.
  - `commute_block`: for `c ≠ c'`, any block of `c` commutes with any block of
    `c'`, for all pattern values, coordinates and units.

## Implemented proof

`mixed_sum_ne_zero_not_root` uses linear independence of the simple roots
(`p.base.linearIndepOn_root`) over `ℤ`. A zero sum would force `d s = 0`. A
root is a nonnegative or nonpositive combination of simple roots
(`p.base.root_mem_or_neg_mem`, with `AddSubmonoid.exists_of_mem_closure_range`).
Comparing coefficients with `Fintype.linearIndependent_iffₛ` then contradicts
`d t < 0` or `d s > 0`. `two_mixed_ne_zero_not_root` applies this to
`d = single a n₁ + single b n₂ - single a' m₁ - single b' m₂`.

`pos_add_ne_zero_not_root` moves `v` to the negative side with Weyl
reflections, which fix `a` and `b` by orthogonality. The reflection in `a'`
sends `n₁ a + n₂ b + m a'` to `n₁ a + n₂ b - m a'`, and the reflection in `b'`
does the same for `b'`. For `v = a' + b'`, the reflection in `a'` gives `b'`
(since `⟨b', a'^∨⟩ = -1`), and then the reflection in `b'` gives `-b'`. In each case
`two_mixed_ne_zero_not_root` applies to the image, and
`ne_zero_not_root_of_reflection` pulls the conclusion back. Reflections preserve
zero and preserve the set of roots (`reflection_apply_root`).

`middleChar_ne_zero_not_root` splits into four cases by the signs of `χ` and
`ψ`. If both are positive (`a`, `b` or `a + b`), `pos_add_ne_zero_not_root`
applies. If exactly one is `-(a + b)` or `-(a' + b')`, the combination is a
two-sided mixed sum and `two_mixed_ne_zero_not_root` applies (with the pairs
exchanged in one case). If both are negative, the combination is the negative
of a positive one, and `neg_ne_zero_not_root` applies.

`commute_of_mem_blockSubgroup` applies the published
`SplitPinning.commute_of_no_strict_root_combinations` (from
`OrthogonalSimpleRootCommutation`) to each pair of generating root subgroups,
using `middleChar_ne_zero_not_root` and the identity `root alpha = a + b`. It
then passes to the joins with `Subgroup.le_centralizer_iff` and `sup_le`.

`block_mem` unfolds the block. The points `u_a`, `u_b` lie in `U(a)`, `U(b)` by
`RootParametrization.mem_rootSubgroup_iff`, and `x_α(s)` lies in `U(α)`. The
representative `n_α` lies in `rootSup α` by the field `nAlpha_mem` of
`EvenChainData`, and the coroot point lies in `rootSup α` by the published
`corootRationalPoint_mem_rootSup`. For distinct indices, the path data give
distinctness (`C.disjoint`) and orthogonality (`isOrthogonal` of
`C.isPathComponent c'`). The pairing `⟨b, a^∨⟩ = -1` comes from the field
`pairing_b_a` via `RootPairing.root_coroot_eq_pairing`. Then `commute_block`
follows from `block_mem` and `commute_of_mem_blockSubgroup`.
