# A simply connected split pinning of type `C_n` of the symplectic group

Author: Worker 31, for Task 5986 (`8494af77-9d10-4c2f-b1cd-60dc371fb195`). This is an internal
helper module (namespace `Langlands.GroupScheme.SymplecticMatrix`). It builds a split pinning
of the split symplectic group `SymplecticMatrix.groupScheme (Fin n) k` over any field `k`,
for every `n`. The coroots of the pinning span the cocharacter lattice, and its simple roots
are numbered by `Fin n` so that their pairings are the entries of Mathlib's Cartan matrix
`CartanMatrix.C n`. This is the type-`C` analogue of the Library's
`specialLinearSimplyConnectedPinning` (module `Reductive/SpecialLinearPinningProof`), and the
proof follows the same plan. All results are at universe parameter `u`. The main theorems use
only the axioms `propext`, `Classical.choice` and `Quot.sound`.

Notation: `𝔻` is the split torus `splitTorus.commGroupScheme (Spec k) (ULift l)`, the source of
the diagonal torus `diagonalTorus l k` of `Sp_{2l}` (module `SymplecticMatrix.Torus`).
Characters and cocharacters have integer coordinates under
`GeneralLinear.characterCoordEquiv` and `GeneralLinear.cocharacterCoordEquiv`. The weights of
the diagonal torus are `w(inl a) = e_a` and `w(inr a) = -e_a` (`weightCoord`). The Library
gives the roots: by `mem_roots_iff`, they are the weight differences `w(x) - w(y)` with
`x ≠ y`.

## Short coroots (any finite index type `l`)

- `sum_mul_single_sub_single`: `∑_c f(c) (e_p - e_q)(c) = f(p) - f(q)`.
- `characterCoordEquiv_longRoot_sub_diffRoot`: the coordinates of `2e_c - m (e_a - e_b)`.
- `cocharacterCoordEquiv_coroot_of_root_eq_diffRoot` (**short coroots**). Let `P` be a root
  datum of the diagonal torus and `j` an index with `P.root j = e_a - e_b`, `a ≠ b`. Then the
  coroot `P.coroot j` has coordinates `e_a - e_b`. Write `ν` for its coordinates.
  `⟨e_a - e_b, ν⟩ = 2` gives `ν_a - ν_b = 2`. For every `c`, the long root `2e_c` is a root
  (`longRoot_mem_roots`), and its pairing with `P.coroot j` is `2ν_c`
  (`latticePairing_longRoot`). So its reflection `2e_c - 2ν_c (e_a - e_b)` is again a root.
  Every coordinate of a root lies in `[-2, 2]` (`coord_mem_Icc_of_mem_roots`). For `c = a`,
  the coordinate at `b` gives `ν_a ≤ 1`. For `c = b`, the coordinate at `a` gives
  `ν_b ≥ -1`. With `ν_a - ν_b = 2`, this gives `ν_a = 1` and `ν_b = -1`. For `c ∉ {a, b}`,
  the reflection has coordinate `2` at `c`, so it is `2e_c` (`eq_single_two_of_mem_roots`).
  Its coordinate at `a`, which is `-2ν_c`, must vanish, so `ν_c = 0`.

The Library already has the long coroots (`cocharacterCoordEquiv_coroot_of_root_eq_longRoot`).

## Simple roots (`l = Fin n`, namespace `TypeCPinning`)

- `wHeight x` is the value of the regular cocharacter `ρ` with coordinates `c ↦ n - c` on the
  weight `w(x)`: `n - a` for `x = inl a` and `a - n` for `x = inr a`. These values are pairwise
  distinct (`wHeight_injective`), and `⟨w(x) - w(y), ρ⟩ = wHeight x - wHeight y`
  (`sum_weightCoord_mul`, `latticePairing_regularCochar`). So `ρ` is regular: no root
  vanishes on it (`root'_regularCochar_ne_zero`).
- `simpleSnd i` is `inl (i + 1)` if `i + 1 < n` and `inr i` otherwise. The `i`-th simple root
  is `w(inl i) - w(simpleSnd i)`, that is `e_i - e_{i+1}` for `i + 1 < n` and `2e_{n-1}` for
  `i = n - 1`. Its value on `ρ` is `1` and `2` respectively (`wHeight_simple`). The simple
  roots are pairwise distinct (`simple_injective`).
- `mem_baseOf_iff` (**simple roots**): an index `j` is an indecomposable positive root for `ρ`
  (Mathlib's `IsAddIndecomposable.baseOf`) exactly when `P.root j` is one of these simple
  roots. Forward: write `P.root j = w(x) - w(y)` with `wHeight y < wHeight x`. If some `z` had
  `wHeight y < wHeight z < wHeight x`, then `w(x) - w(z)` and `w(z) - w(y)` would be positive
  roots with sum `P.root j`, which is excluded (`exists_root_of_ne`). A case analysis on
  `x, y` then shows that `(x, y)` is `(inl a, inl (a + 1))`, `(inl (n-1), inr (n-1))` or
  `(inr (b + 1), inr b)`. The last case gives `e_b - e_{b+1}`, the same character as the first
  case for `a = b`. Backward: a simple root has value `1` or `2` on `ρ`. If it were a sum of
  two positive roots, each would have value at least `1`. For value `1` this is impossible.
  For the long simple root `2e_{n-1}` both summands would have value `1`. A root of value `1`
  has nonpositive coordinate at `n - 1` (`coord_last_nonpos`), so the coordinate of the sum
  at `n - 1` would not be `2`.
- `pairing_simple`: the pairing of the `i`-th and `i'`-th simple roots is
  `CartanMatrix.C n i i'`. If `i' + 1 < n`, the coroot of `e_{i'} - e_{i'+1}` has coordinates
  `e_{i'} - e_{i'+1}` (short coroots), and the pairing is the difference of two coordinates of
  the `i`-th simple root. If `i' = n - 1`, the pairing with the long coroot is the coordinate
  at `n - 1` (`pairing_eq_coord_of_root_eq_longRoot`). A case analysis compares both with the
  definition of `CartanMatrix.C n`: `2` on the diagonal, `-1` for `i + 1 = i'`, and for
  `i' + 1 = i` the entry `-2` if `i = n - 1` and `-1` otherwise.

## The pinning

- `exists_coordinateRootDatum n k`: there are a finite index type `J`, a reduced root datum
  `P` of the diagonal torus (`exists_rootDatum`), a base `B`, and a bijection
  `e : B.support ≃ Fin n`, such that `P.corootSpan ℤ = ⊤` (`corootSpan_eq_top`) and
  `P.pairing a b = CartanMatrix.C n (e a) (e b)` for simple `a, b`. The base is the
  Library's `RootDatumCoweightFace.exists_base_support` for the regular cocharacter `ρ`. Its
  support is the set of indecomposable positive roots, described by `mem_baseOf_iff`. The
  bijection sends a simple index to the number of its simple root.
- `exists_splitPinning n k` (**main result**): the split symplectic group
  `groupScheme (Fin n) (CommRingCat.of k)` has a `SplitPinning` `p` with
  `p.rootDatum.corootSpan ℤ = ⊤` and a bijection `e : p.base.support ≃ Fin n` with
  `p.rootDatum.pairing a b = CartanMatrix.C n (e a) (e b)`. The pinning uses the diagonal
  torus (split by `isSplitTorus_diagonalTorus`, maximal by `isMaximalTorus_diagonalTorus`),
  connected reductivity `isConnectedReductive`, the root datum and base above, and the Lie
  trivializations `RootPinning.ofSplitMaximalTorus`.

## Provenance

Internal module. These are the standard simple roots `e_1 - e_2, …, e_{n-1} - e_n, 2e_n` and
simple coroots of `Sp_{2n}` (Milne, *Algebraic Groups* (2017), Summary 21.98, printed p.460,
registered as `milne-2017-algebraic-groups`). The numbering puts the long simple root last,
as in Bourbaki and in Tits's Table I, and matches Mathlib's `CartanMatrix.C n`.
