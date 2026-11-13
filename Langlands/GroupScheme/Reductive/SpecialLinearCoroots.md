# Coroots of the diagonal torus of the special linear group

Helper module for the proof of
`Langlands.GroupScheme.SpecialLinearSimplyConnectedPinningStatement`. Author: Worker 61
(Task 5703). Let `P` be any root datum attached to the diagonal torus of `SL_{n+1}` over a
field `k`, in the Library's sense
`IsRootDatumOf (diagonalTorus n (CommRingCat.of k)) P`. This module computes the coroots of
`P` and shows that they span the cocharacter lattice. The root datum itself is not
constructed here. All declarations are in namespace `Langlands.GroupScheme.SpecialLinear.FinSucc`.

Notation: `𝔻` is the split torus `splitTorus.commGroupScheme (Spec k) (ULift (Fin n))`,
`w(p)` is `weightCoord n p`, and `rootChar n k p q` is the character with coordinates
`w(p) - w(q)` (module `Reductive.SpecialLinearRoots`).

## Integer coordinates

- `delta p q : Fin (n + 1) → ℤ` is the function `y ↦ [y = p] - [y = q]`. `sum_delta`:
  its values sum to `0`.
- `sum_weightCoord_eq_zero`: `∑_p w(p) = 0`.
- `sum_weightCoord_mul`: `∑_c w(x)_c · h(c.castSucc) = h(x) - [x = last] · ∑_y h(y)` for any
  `h : Fin (n + 1) → ℤ`. `sum_weightCoord_mul_of_sum_eq_zero`: when `∑_y h(y) = 0`, the
  sum equals `h(x)`.
- `sum_weightCoord_sub`: `∑_p (w(c.castSucc) - w(p)) = (n + 1) e_c`.
- `weightCoord_sub_delta_smul`: the reflection identity
  `w(x) - delta p q x · (w(p) - w(q)) = w(σ x)`, where `σ = Equiv.swap p q`.

## Characters and cocharacters over a field

- `rootChar_self`: `rootChar n k p p = 0`.
- `rootChar_add_rootChar`: `rootChar x y + rootChar y z = rootChar x z`.
- `rootChar_sub_smul_rootChar`: the reflection formula
  `rootChar x y - (delta p q x - delta p q y) • rootChar p q = rootChar (σ x) (σ y)` with
  `σ = Equiv.swap p q`.
- `cochar n k h : cocharacterLattice 𝔻` is the cocharacter with coordinates
  `c ↦ h(c.castSucc)` in the Library's `GeneralLinear.cocharacterCoordEquiv (Fin n) k`.
  `cocharacterCoordEquiv_cochar` records this.
- `latticePairing_rootChar_cochar`: if `∑_z h(z) = 0`, the Library's
  `latticePairing 𝔻 (rootChar n k x y) (cochar n k h)` equals `h(x) - h(y)`. The pairing in
  coordinates is the dot product (`GeneralLinear.latticePairing_coord`), and
  `sum_weightCoord_mul_of_sum_eq_zero` evaluates it.
- `corootChar n k p q = cochar n k (delta p q)`. This is the cocharacter
  `t ↦ diag(…, t at p, …, t⁻¹ at q, …)`.
  - `latticePairing_rootChar_corootChar`: it pairs with `rootChar n k x y` to
    `delta p q x - delta p q y`.
  - `cocharacterCoordEquiv_corootChar_last`: `corootChar n k a.castSucc last` has
    coordinates `e_a`.

## Coroots of a root datum of the diagonal torus

In this section `J` is a type with `[Finite J]` where needed, and
`P : RootDatum J (characterLattice 𝔻) (cocharacterLattice 𝔻)` satisfies
`hP : IsRootDatumOf (diagonalTorus n (CommRingCat.of k)) P`. The proofs use two parts of
`hP`: the pairing of `P` is `latticePairing 𝔻`, and the range of `P.root` is the set of
roots of the torus.

- `mem_range_root_iff hP χ`: `χ` is a root of `P` if and only if `χ = rootChar n k p q` for
  some `p ≠ q`. This is `mem_roots_iff` of `Reductive.SpecialLinearRoots`.
- `smul_mem_span_root hP χ`: `(n + 1) • χ` lies in the `ℤ`-span of the roots, for every
  character `χ`. In coordinates `(n + 1) • χ = ∑_c χ_c ∑_p rootChar (c.castSucc) p`
  (`sum_weightCoord_sub`).
- `coroot_eq_corootChar hP hj`: **coroots.** If `P.root j = rootChar n k p q`, then
  `P.coroot j = corootChar n k p q`. Let `g` be the linear form `⟨-, corootChar n k p q⟩`.
  - `g` takes the value `2` on the root, and its reflection `χ ↦ χ - g(χ) • P.root j` maps
    roots to roots by `rootChar_sub_smul_rootChar`. The coroot `P.coroot j` has the same
    two properties.
  - Mathlib's uniqueness lemma `Module.Dual.eq_of_preReflection_mapsTo'` (for the finite
    set of roots) then shows that the two linear forms agree on the span of the roots.
  - By `smul_mem_span_root` they agree on `(n + 1) • χ` for every `χ`. Cancelling
    `n + 1` gives agreement on all characters. The perfect pairing then identifies
    `P.coroot j` with `corootChar n k p q`.
- `corootSpan_eq_top hP`: **coroot span.** `P.corootSpan ℤ = ⊤`. The coroots of the roots
  `rootChar n k a.castSucc last` are the cocharacters with coordinates `e_a`
  (`coroot_eq_corootChar` and `cocharacterCoordEquiv_corootChar_last`). They form the
  coordinate basis of the cocharacter lattice.

## Provenance

The coroot of `ε_p - ε_q` for the diagonal torus of `SL_{n+1}` is the cocharacter
`t ↦ diag(…, t, …, t⁻¹, …)`, and these coroots span the cocharacter lattice: taking `q` to be the last index gives
the coordinate basis. Both facts are standard. The spanning computation establishes
the lattice condition of simple connectedness directly. Here the coroots are derived from the abstract
root datum by Mathlib's uniqueness of reflections preserving a finite root set. No explicit
`SL_2` homomorphisms are used. The module was written for this project.
