# The full-flag locus of a quotient Grassmannian

Author: Worker 1399. Internal helper module for the proof of
`Langlands.GroupScheme.GeneralLinearSolvableStabilizerStatement`. It realizes full flags of
`K^n` as the points of one Library quotient Grassmannian that satisfy a linear stability
condition. The construction (several copies of `K^n` with multiplicities `(n + 1)^j` and a
base-`(n + 1)` digit argument) is internal; it replaces the textbook flag variety, a closed
subscheme of a product of Grassmannians cut out by incidence conditions (Milne, *Algebraic
Groups* (2017), 7.29–7.30), because the Library has single Grassmannians and their
projective embeddings.

Namespace `Langlands.Grassmannian.FlagLocus`. The notation `G(k, V; A)` is the Library's
`Module.Grassmannian A V k`: submodules `P` of the `A`-module `V` whose quotient is finite
projective of constant rank `k`.

## The ambient module

- `Copy n := Σ j : Fin (n + 1), Fin ((n + 1) ^ j)`. These are copies of `R^n`: level `j` (the
  first component) has `(n + 1)^j` copies. `Idx n := Copy n × Fin n` indexes the coordinates
  of the ambient free module `Idx n → R`.
- `rank n := ∑ j : Fin (n + 1), (n + 1)^j * (n - j)`: the quotient rank of the points used.
  For a full flag with subspace of dimension `j` in every level-`j` copy, the quotient has
  this dimension.
- `firstCopy n j`: the copy `⟨j, 0⟩`.

## Coordinate maps (section `Coordinates`, any commutative ring `A`)

- `shift A a b`: copies block `b` into block `a` and is zero on the other blocks
  (`shift_apply`).
- `place A c w`: the vector `w : Fin n → A` put in block `c` (`place_apply`).
- `colAct A g`: the square matrix `g` acting on every block,
  `colAct A g v (c, i) = ∑ j, g i j * v (c, j)`. Lemmas: `colAct_one`, `colAct_mul`;
  `shift_colAct` (the action commutes with `shift`); `colAct_place`
  (`colAct g (place c w) = place c (g *ᵥ w)`); `shift_place`; `shift_self`
  (`shift c c v` is `place c` of the `c`-block of `v`); `sum_place` (a vector is the sum of its
  placed blocks); `map_colAct` (compatibility with ring maps).
- `colActEquiv A g`: for `g : GL (Fin n) A`, `colAct A g` as a linear equivalence.

## Tensor coordinates (section `Tensor`)

- `coord R A : A ⊗[R] (Idx n → R) ≃ₗ[A] (Idx n → A)` is Mathlib's `piScalarRight`, with
  `coord_tmul`. Then `coord_baseChange_shift` (base change of `shift R a b` becomes
  `shift A a b`), `coord_rTensor` (along `φ : A →ₐ[R] B`, coordinates map by `φ`), and
  `rTensor_baseChange_shift`.
- `actEquiv R A g := coord⁻¹ ∘ colActEquiv A g ∘ coord`: the action of `g : GL (Fin n) A`
  on `A ⊗[R] (Idx n → R)`. Lemmas: `coord_actEquiv`, `actEquiv_one`, `actEquiv_mul`,
  `baseChange_shift_actEquiv` (the action commutes with the base-changed shifts),
  `rTensor_actEquiv` (along `φ`, the action of `g` becomes the action of
  `GeneralLinearGroup.map φ g`).

## Grassmannian points (section `Points`)

- `transport σ P`: the image of a Grassmannian point under a linear equivalence `σ` of the
  ambient modules; the quotient is transported by `Submodule.Quotient.equiv`.
- `smul R g P := transport (actEquiv R A g) P`: the action of `GL_n(A)` on
  `G(k, A ⊗[R] (Idx n → R); A)`, with `smul_toSubmodule`, `one_smul`, `mul_smul`.
- `map_smul_point`: the action commutes with the Library base change
  `Module.Grassmannian.map φ`. Proof: `map_toSubmodule_eq_span` (from
  `Langlands.RingTheory.Grassmannian.BaseChangeMembership`) on both sides and
  `rTensor_actEquiv`.
- `Stable R P` (the flag condition): for all copies `a, b` with `level b ≤ level a` and every
  `z ∈ P`, the base change of `shift R a b` sends `z` into `P`.
- `Stable.smul`: the action preserves `Stable`, by `baseChange_shift_actEquiv`.
- `exists_ideal_stable_map_iff`: for every point `P` over `A` there is an ideal `𝔞` of `A`
  such that for all `R`-algebras `B` and `φ : A →ₐ[R] B`,
  `Stable R (map φ P) ↔ ∀ a ∈ 𝔞, φ a = 0`. Proof: apply
  `exists_ideal_forall_rTensor_mem_map_iff` to the family of all vectors
  `(shift R a b).baseChange A z` with `level b ≤ level a` and `z ∈ P`. Since `map φ P` is the
  span of the image of `P` (`map_toSubmodule_eq_span`), stability of `map φ P` is equivalent
  to membership of the images of these vectors (span induction for the converse).
- `Stable.map`: stability is preserved by base change (same span induction).

## Digits

- `digits_eq`: base-`b` expansions with all digits below `b` are unique: if
  `∑ j < m, b^j * x j = ∑ j < m, b^j * y j` with all `x j, y j < b`, then `x = y`. Induction on
  `m`, comparing remainders modulo `b` and dividing by `b`.

## Points over a field (section `Field`)

Let `K` be a field with an `R`-algebra structure.

- `coords R P`: the subspace of `Idx n → K` corresponding to `P` under `coord`.
- `block R P c`: the vectors `w : Fin n → K` with `place K c w ∈ coords R P`.
- `Stable.shift_mem`: for stable `P`, `coords R P` is preserved by `shift K a b` when
  `level b ≤ level a`.
- `Stable.block_mono`: `block R P b ≤ block R P a` when `level b ≤ level a`
  (`shift_place`). Hence blocks of equal level are equal.
- `Stable.mem_coords_iff`: for stable `P`, `v ∈ coords R P` exactly when every block of `v`
  lies in the corresponding `block R P c` (`shift_self` and `sum_place`), and
  `Stable.coordsEquiv` identifies `coords R P` with `∀ c, block R P c`.
- `finrank_quotient_coords`: for `P` in `G(rank n, …; K)`, the quotient
  `(Idx n → K) ⧸ coords R P` has dimension `rank n` (the rank at the generic stalk).
- `Stable.finrank_block`: for stable `P` in `G(rank n, …; K)` and every level `j`,
  `finrank (block R P (firstCopy n j)) = j`. Proof: let `d j` be the dimension of the
  level-`j` blocks (all equal), so `d j ≤ n`. Counting dimensions, the quotient has dimension
  `∑ j, (n + 1)^j * (n - d j)`, and it also equals `rank n = ∑ j, (n + 1)^j * (n - j)`. Both
  digit families are at most `n < n + 1`, so `digits_eq` gives `n - d j = n - j`, hence
  `d j = j`.
- `mulVec_mem_block`: if `smul R g P = P` for `g : GL (Fin n) K`, then `g *ᵥ w ∈ block R P c`
  for every `w ∈ block R P c` (`colAct_place`).
- `exists_fullFlag`: a stable point `P` of `G(rank n, K ⊗[R] (Idx n → R); K)` gives a monotone
  family `F : Fin (n + 1) → Submodule K (Fin n → K)` with `finrank (F j) = j` for all `j`,
  such that every `g : GL (Fin n) K` with `smul R g P = P` satisfies `g *ᵥ v ∈ F j` for all
  `v ∈ F j`. Take `F j := block R P (firstCopy n j)`.

## The standard point

- `StdIdx n`: the coordinates `(c, i)` with `level c ≤ i`; `stdIdxEquiv` identifies it with
  `Σ c, Fin (n - level c)`, so `card_stdIdx : card (StdIdx n) = rank n`.
- `stdCoords K`: the vectors vanishing at all coordinates of `StdIdx n`; `mem_stdCoords`.
  Its level-`j` blocks are the vectors supported on the first `j` coordinates.
- `stdSub n R K`: the preimage of `stdCoords K` under `coord`; `map_stdSub`;
  `stdQuotEquiv`: the quotient by `stdSub` is isomorphic to `StdIdx n → K`.
- `stdPoint n R K : G(rank n, K ⊗[R] (Idx n → R); K)`: the point with submodule `stdSub`.
  Its quotient is free of rank `card (StdIdx n) = rank n`. `coords_stdPoint` and
  `stable_stdPoint` (shifting from a block of lower or equal level keeps the vanishing
  conditions) show that it is stable. It is used for nonemptiness of the flag scheme.
