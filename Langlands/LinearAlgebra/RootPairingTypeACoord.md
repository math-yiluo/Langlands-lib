# Weight coordinates of integral type `A` root pairings

Module `Langlands.LinearAlgebra.RootPairingTypeACoord`, namespace
`Langlands.LinearAlgebra.RootPairingTypeA`. This is pure linear algebra about
Mathlib `RootPairing`s over `ℤ`. It is a helper for the proof of
`Langlands.GroupScheme.SpecialLinearTorusAutomorphismStatement`.

## The coordinate structure

`TypeACoord P n` is a structure on an integral root pairing
`P : RootPairing ι ℤ M N`. It holds weights `ε : Fin (n + 1) → M` with these properties:

- `exists_eq_sum`: every weight is a `ℤ`-combination `∑ c y • ε y`.
- `sum_eq_zero`: `ε 0 + ⋯ + ε n = 0`.
- `eq_of_sum_eq_zero`: if `∑ c y • ε y = 0` then `c` is constant. So the only
  relation is the sum relation.
- `exists_root_eq`: every root is `ε a - ε b` for some `a ≠ b`.
- `exists_eq_root`: every `ε a - ε b` with `a ≠ b` is a root.
- `coroot'_apply`: if `root j = ε a - ε b`, then
  `coroot' j (ε y) = [y = a] - [y = b]`.

These are the standard coordinates `ε_i` of the root system `A_n`, read on the character lattice of
the diagonal torus of `SL_{n+1}`. There the weight lattice is `ℤ^{n+1}` modulo the
diagonal. Compare Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6* (Springer, 2002), registered as `bourbaki-lie-iv-vi-2002-scribd-original-text` (retained HTML, SHA-256 `b9f6932507d4da5351eb45a68387ad76dfa58dd118c0da97f01501293f97546c`), Plate I (p.265), item (I): roots `εᵢ - εⱼ`
in the hyperplane of coordinate sum zero. Provenance: **internal**. This structure is an interface designed for
the proof. It is not a definition taken from a source. It holds data and makes
no claim that coordinates exist; the companion module
`Langlands.GroupScheme.Reductive.SpecialLinearTypeACoord` builds an instance for
the diagonal torus.

## Results

For `C : TypeACoord P n`:

- `coroot'_sum`, `coroot'_sub`: evaluation of a coroot `ε a - ε b` on
  combinations of coordinates.
- `ε_injective`; `ε_ne_zero` (for `1 ≤ n`).
- `linearMap_ext`: linear maps out of `M` are determined on the `ε y`.
- `coroot'_ε_bounds`: coroots pair with each `ε a` in `{-1, 0, 1}`.
- `eq_of_coroot'_ε_eq_one`: if `coroot' j (ε a) = 1` then `root j = ε a - ε q`
  for some `q ≠ a`.
- `exists_weightEquiv_ε_eq` (for `1 ≤ n`): for an automorphism `δ : P.Aut`,
  `δ.weightEquiv (ε a) = ± ε y` for some `y`. Proof: write
  `δ.weightEquiv (ε a) = ∑ c y • ε y`. Pull roots back along `δ.indexEquiv`, so every
  difference `c y - c z` is a pairing of a coroot with `ε a`, hence in
  `{-1, 0, 1}`. So `c` takes two adjacent values (it is not constant, since
  `ε a ≠ 0`). Suppose both values are taken at least twice, at `y₁ ≠ y₂` (top) and
  `z₁ ≠ z₂` (bottom). Pull back the roots `ε yᵢ - ε zᵢ` to `j₁, j₂`; their coroots
  pair with `ε a` as `1`, so their roots are `ε a - ε qᵢ`. The Mathlib
  pairing-invariance of the automorphism (`δ.toHom.pairing`) then compares
  `pairing j₁ j₂` before and after `δ`: one side is
  `1 + [q₁ = q₂]` and the other is `0`, a contradiction. So the top or bottom
  value is taken exactly once, which gives `+ε y` or `−ε y`.
- `ε_add_ε_ne` (for `2 ≤ n`): `ε y + ε z` is never `ε p - ε q`. The relation
  would be a combination with coefficient sum `2`, so it would be a constant
  multiple of the sum relation with `(n+1) ∣ 2`.
- `exists_perm`: a map `σ` with `δ.weightEquiv (ε a) = ε (σ a)` for all `a`, or
  `= -ε (σ a)` for all `a`, with one uniform sign. For `n = 0` all `ε a = 0`.
  For `n = 1`, `-ε y` is again a coordinate. For `n ≥ 2` a mixed sign at `a ≠ b`
  would make the image of the root `ε a - ε b`, which is `± (ε σa + ε σb)`, a root,
  contradicting `ε_add_ε_ne`. Mixed sign at `a = b` gives `2 ε σa = 0`, which is
  ruled out in the same way.
- `exists_weyl_perm`: every permutation `π` of the coordinates is realized by
  some `w ∈ P.weylGroup`, with `w.weightEquiv (ε y) = ε (π y)`. The proof is by
  `Equiv.Perm.swap_induction_on`: the reflection in the root `ε x - ε y` swaps
  `ε x` and `ε y` and fixes the other coordinates.
- **`mem_weylGroup_or_exists_neg`**: every `δ : P.Aut` satisfies
  `δ ∈ P.weylGroup`, or there is `w ∈ P.weylGroup` with
  `w.weightEquiv x = -δ.weightEquiv x` for all `x`. That is, `Aut(P) = ±W` on
  weights. The `σ` from `exists_perm` is injective, so it is a permutation. Take the
  Weyl element realizing it and compare on coordinates. In the positive case,
  `weightHom_injective` gives `w = δ`.
- `transport` (with `transport_ε`): transport of `TypeACoord` along a root
  pairing equivalence `P.Equiv Q`, mapping `ε y ↦ e.weightEquiv (ε y)`.
- `span_coroot_eq_top_of_equiv`: the property "coroots span the coweight lattice
  over `ℤ`" transports along `P.Equiv Q`.
- `eq_one_of_indexEquiv_eq`: an automorphism `θ` that fixes every index of a set
  `s` whose coroots span the coweight lattice is `1`. This follows from
  `coweightHom_injective` and `LinearMap.ext_on`.

The classical fact behind the main result is in the same source, Plate I. Item (X)
identifies `W` with the permutations of the `εᵢ`. Item (XI) gives `A(R) = W(R)` for
`l = 1` and `A(R) = W(R) × {1, -1}` for `l ≥ 2`. The Lean proof above is
self-contained. It does not use a Dynkin diagram classification, and it states
only the weaker dichotomy, with no claim that the two cases are exclusive.
