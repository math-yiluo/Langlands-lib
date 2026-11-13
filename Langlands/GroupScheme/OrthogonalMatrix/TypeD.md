# The type `D` root datum of the split orthogonal group and almost simplicity

This internal module proves that, over an algebraically closed field `k` and for an index
type `l` with at least three elements, the identity component of the split orthogonal group
`OrthogonalMatrix.groupScheme l k` (the orthogonal group `O_{2l}` of the hyperbolic form) is
almost simple once it is known to be semisimple and nontrivial. The two facts used are
standard for the root system of type `D_l` (`±e_a ± e_b`, `a ≠ b`; Bourbaki, *Lie Groups and
Lie Algebras*, Ch. VI, Plate IV): the coroot of `±e_a ± e_b` is `±e_a^∨ ± e_b^∨`, and any two
roots are joined by a chain of roots with nonzero pairing. Both are proved here directly. The
almost-simplicity criterion itself is the published `isAlmostSimple_of_rootsLinked`.

Throughout, an index `x : l ⊕ l` has weight `w(x)`: `w(inl a) = e_a` and `w(inr a) = -e_a`.
`swap` exchanges `inl a` and `inr a`, so `w(swap x) = -w(x)`.

## Abstract type `D` linking

These results are stated for any group `G` over a field with a torus `t : T → G`.

- `reflTransGen_rootsLinked_of_typeD w hroots hlink hl`: let `w : l ⊕ l → X(T)` satisfy
  three conditions. First, every root of `t` is `w x + w y` with `x ≠ y` and `x ≠ swap y`
  (`hroots`). Second, `w (swap x) + w z` is linked to `w x + w y` whenever `z` differs from
  `x`, `y` and their swaps (`hlink`). Third, such a `z` exists for all `x, y` (`hl`). Then
  any two roots are joined by a chain of linked roots (`Relation.ReflTransGen (RootsLinked t)`).
  The proof builds chains in three steps:
  - *flip*: `w x + w y` reaches `w x + w (swap y)` through `w (swap x) + w z`, for a `z`
    avoiding `x`, `y` and their swaps.
  - *same first index*: `w x + w y` reaches `w x + w y'`. If `y' = y` there is nothing to
    do, and if `y' = swap y` this is the flip. Otherwise the chain is
    `w y + w x`, `w (swap y) + w y'`, `w (swap y') + w x`, followed by a flip.
  - *general case*: from `w x + w y` to `w x' + w y'`, pick `z` avoiding `x`, `x'` and their
    swaps. Then go `w x + w y → w x + w z → w z + w x' → w x' + w y'`, each step changing
    only the second index.
- `isAlmostSimple_of_typeD`: over an algebraically closed field `k`, let `G` be
  semisimple and nontrivial, with a split maximal torus `t` of a split torus `T`. Let
  `w : l ⊕ l → X(T)` and `ω : l ⊕ l → X_*(T)` satisfy `⟨w u, ω x⟩ = 1` if `u = x`, `-1` if
  `u = swap x` and `0` otherwise. Suppose the roots of `t` are exactly the characters
  `w x + w y` with `x ≠ y` and `x ≠ swap y`. Suppose a root datum `P` of `t` has coroot
  `ω x + ω y` at the root `w x + w y`, and `z` as above always exists. Then `G` is almost
  simple. To link `β = w (swap x) + w z` with `β' = w x + w y`, use the coordinate
  `g = ⟨·, ω x + ω y⟩`. It gives `g β = ⟨β, β'^∨⟩ = -1` and `g β' = 2`. Also `g ≥ -2` on all
  roots, since each `w u` pairs with `ω x + ω y` to `-1`, `0` or `1`. The published
  `strict_combinations_of_coordinate` and `rootsLinked_of_pairing_eq_neg_one` then show
  that `β` and `β'` are linked (`k` is infinite). The published
  `isAlmostSimple_of_rootsLinked` concludes.

## Signs, weight characters and cocharacters

- `sgn x`: `1` for `inl a` and `-1` for `inr a` (`sgn_inl`, `sgn_inr`, `sgn_eq`). Also
  `weightCoord_eq_single`: `w(x)` in coordinates is `sgn x` at `index x` and `0` elsewhere
  (`weightCoord_apply_index`, `weightCoord_apply_of_ne`). `sum_weightCoord_mul`:
  `Σ_c w(x)_c ν_c = sgn x · ν_{index x}`.
- `weightChar l k x`, `weightCochar l k x`: `w(x)` as a character, and `w(x)^∨` as a
  cocharacter, of the diagonal torus `splitTorus (ULift l)`. Both come from the published
  coordinate isomorphisms `GeneralLinear.characterCoordEquiv` and
  `GeneralLinear.cocharacterCoordEquiv` (`characterCoordEquiv_weightChar`,
  `cocharacterCoordEquiv_weightCochar`).
- `latticePairing_weightChar`: `⟨w(x), ν⟩ = sgn x · ν_{index x}`.
- `latticePairing_weightChar_weightCochar`: `⟨w(u), w(x)^∨⟩` is `1` if `u = x`, `-1` if
  `u = swap x` and `0` otherwise.
- `exists_eq_weightChar_add_of_mem_roots`, `weightChar_add_mem_roots`: the roots of the
  diagonal torus are exactly the characters `w(x) + w(y)` with `x ≠ y` and `x ≠ swap y`.
  This restates `mem_roots_iff` (module `OrthogonalMatrix.Roots`), which describes the
  roots as `w(x) - w(y)` with `index x ≠ index y`, using `w(swap y) = -w(y)`.
- `coord_eq_zero_of_mem_roots`: a root has at most two nonzero coordinates. Of any three
  distinct indices `c, a, b`, the root has a zero coordinate at one of them.

## The coroots

Let `P` be any root datum of the diagonal torus `identityTorus l k` of the identity component
(`IsRootDatumOf`), and let `P.root r = w(x) + w(y)` with `index x ≠ index y`. Write `ν` for
the coordinates of the coroot `P.coroot r`.

- `coroot_constraint`: let `c` be a third index and `p` an index with `index p = index x`.
  Then `β = e_c + w(p)` is a root, and `n = ⟨β, P.coroot r⟩ = ν_c + sgn p · ν_{index x}`. The
  reflection of `β` along `r` is the root `β - n (w(x) + w(y))`. Its coordinates at `c`,
  `index x` and `index y` are `1`, `sgn p - n · sgn x` and `-n · sgn y`, and one of them is
  zero. Hence `n = 0` or `sgn p = n · sgn x`.
- `coroot_eq_weightCochar_add`: if `l` has at least three elements, then
  `P.coroot r = w(x)^∨ + w(y)^∨`. From `⟨α, α^∨⟩ = 2` (`RootPairing.pairing_same`),
  `sgn x · ν_{index x} + sgn y · ν_{index y} = 2`. Pick a third index `c₀`. Apply
  `coroot_constraint` with `p = inl (index x)` and `p = inr (index x)`, and again with `x`
  and `y` exchanged. These four constraints, combined with the equation above, force
  `ν_{index x} = sgn x` and `ν_{index y} = sgn y`. The same four constraints at any other
  index `d` then force `ν_d = 0`. The result follows by injectivity of
  `GeneralLinear.cocharacterCoordEquiv`.

## Almost simplicity

- `exists_ne_swap`: if `l` has at least three elements, then for any `x, y : l ⊕ l` some
  `z = inl c`, with `c` different from `index x` and `index y`, differs from `x`, `y` and
  their swaps.
- `isAlmostSimple_identityComponent l k hl hG hnt`: over an algebraically closed field
  `k`, suppose `l` has at least three elements and the identity component of
  `groupScheme l k` is semisimple (`hG`) and nontrivial (`hnt`). Then it is almost
  simple. The published `rootDatumExistence` gives a root datum `P` of the maximal torus
  `identityTorus l k` (`isMaximalTorus_identityTorus`, `isSplitSubtorus_identityTorus`,
  `SymplecticMatrix.isSplitTorus_diagonalTorus`). Its roots are those of the diagonal torus
  (`roots_identityTorus`), and `isAlmostSimple_of_typeD` applies with `w = weightChar`,
  `ω = weightCochar`, the coroots from `coroot_eq_weightCochar_add`, and `exists_ne_swap`.
