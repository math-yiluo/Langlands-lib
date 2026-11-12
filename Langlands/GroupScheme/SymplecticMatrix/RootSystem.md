# The roots of the split symplectic group

This internal module determines all roots of the diagonal torus `diagonalTorus l k` of the
split symplectic group `SymplecticMatrix.groupScheme l k` over a field `k`. It also computes
pairings with the long coroots. Earlier modules supply the inputs: `SymplecticMatrix.Torus`
(the torus and its weights `w(x) = weightCoord l x`, with `w(inl a) = e_a` and
`w(inr a) = -e_a`), `SymplecticMatrix.Roots` (long roots) and
`SymplecticMatrix.SimplyConnected` (a root datum and its long coroots). Let `𝔻` be the split
torus `splitTorus.commGroupScheme (Spec k) (ULift l)`. Characters have coordinates
`GeneralLinear.characterCoordEquiv l k : characterLattice 𝔻 ≃ₗ[ℤ] (l → ℤ)`. No assumption is
made on `l` or on the characteristic of `k`.

## Matrix facts (any commutative ring)

* `single_inl_inl_sub_single_inr_inr_mul_J_add`: the matrix
  `E_{inl a, inl b} - E_{inr b, inr a}` satisfies the Lie condition `Y J + J Yᵀ = 0` of
  `SymplecticMatrix.Roots.lie_condition_iff`.
* `weightCoord_apply_mem_Icc`: every coordinate of a weight `w(x)` lies between `-1` and `1`.

## Roots over a field

* `pairing_eq_coord_of_root_eq_longRoot` (**pairing with a long coroot**): let `P` be a root
  datum of the diagonal torus (`IsRootDatumOf (diagonalTorus l k) P`), with
  `P.root j = 2e_a`. Then `P.pairing i j` equals the `a`-th coordinate of `P.root i`, for
  every `i`. The pairing of `P` is `latticePairing`, which is the dot product of coordinates.
  The coroot `P.coroot j` has coordinates `e_a` by
  `cocharacterCoordEquiv_coroot_of_root_eq_longRoot`.
* `coord_mem_Icc_of_mem_roots`: every coordinate of a root lies between `-2` and `2`. A root
  has coordinates `w(x) - w(y)` (`exists_coord_of_mem_roots`).
* `neg_mem_roots`: the roots are stable under negation. Take a root datum
  (`exists_rootDatum`). The reflection of a root in itself is its negative.
* `diffRoot l k a b` and `sumRoot l k a b`: the characters with coordinates `e_a - e_b` and
  `e_a + e_b`. `characterCoordEquiv_diffRoot` and `characterCoordEquiv_sumRoot` restate the
  definitions.
* `diffRoot_mem_roots`: for `a ≠ b`, `e_a - e_b` is a root. It is nonzero. The Lie algebra
  element with matrix `E_{inl a, inl b} - E_{inr b, inr a}` (`exists_lieMatrix_eq`) is
  nonzero, and its two nonzero entries have weight `w(inl a) - w(inl b)` and
  `w(inr b) - w(inr a)`, both equal to `e_a - e_b`
  (`mem_weightSpace_diagonalTorus_iff_support`).
* `sumRoot_mem_roots`: for `a ≠ b`, `e_a + e_b` is a root. It is the reflection of the root
  `e_a - e_b` in the long root `2e_b`. By the pairing lemma, this reflection is
  `(e_a - e_b) - (-1) · 2e_b = e_a + e_b`. Reflections of roots in a root datum are roots.
* `inl_sub_inr_mem_roots`: for all `a`, `b`, the character with coordinates
  `w(inl a) - w(inr b) = e_a + e_b` is a root. It is the long root `2e_a` when `a = b`
  (`longRoot_mem_roots`) and `sumRoot` otherwise.
* `mem_roots_iff` (**the roots**): a character `χ` is a root exactly when its coordinates
  are `w(x) - w(y)` for some `x ≠ y` in `l ⊕ l`. That is, the roots are the characters with
  coordinates `±2e_a` and `±e_a ± e_b` for `a ≠ b`. Forward: `exists_coord_of_mem_roots`, and
  `x ≠ y` since roots are nonzero. Backward: by cases on `x` and `y`. `(inl a, inl b)` gives
  `diffRoot a b`. `(inl a, inr b)` gives `inl_sub_inr_mem_roots`. `(inr a, inl b)` gives the
  negative of `inl_sub_inr_mem_roots b a`. `(inr a, inr b)` gives `diffRoot b a`.

## Provenance

These are the standard roots of type `C_l` of the split symplectic group. Milne, *Algebraic
Groups* (2017), Summary 21.98 (printed p. 460) lists them as `±2e_i` and `±e_i ± e_j`. The
module is internal, and its proofs are written from the cited Library results and the
earlier `SymplecticMatrix` modules. The short roots `e_a + e_b` come from reflections in the
root datum, not from explicit root vectors.
