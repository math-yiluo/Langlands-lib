# The Cartan involution of an injective matrix realization with self-adjoint range

Module `Langlands.Group.MatrixCartanInvolution` (namespace
`Langlands.Group.MatrixCartanInvolution`). Internal supporting construction: the standard Cartan
involution `M ↦ (Mᴴ)⁻¹` of a self-adjoint matrix group (Mostow, *Self-adjoint groups*, Ann. of
Math. 62 (1955); Harish-Chandra's Cartan decomposition), transported to an abstract group through an
injective realization and conjugated so that a prescribed element becomes unitary-adapted.

## Setting

`X` is a group, `𝕜` an `RCLike` field, `R : X →* GL (Fin n) 𝕜` injective, its range stable under
`star` (conjugate transpose), and `a` an element of the range.

## Declarations

- `cartanCenter a = a * star a`; it lies in the range (`cartanCenter_mem`) and is self-adjoint
  (`star_cartanCenter`).
- `cartanTarget_mem`: `c * (star (R x))⁻¹ * c⁻¹` lies in the range, for `c = cartanCenter a`
  (range is a subgroup, stable under `star`).
- `cartan R hR hstar a ha : X → X`: `x ↦` the unique preimage of `c * (star (R x))⁻¹ * c⁻¹`
  (via `MonoidHom.ofInjective`), so that `map_cartan` holds:
  `R (cartan … x) = c * (star (R x))⁻¹ * c⁻¹`.
- `cartan_cartan`: `cartan` is an involution. Applying `R`, the identity follows from
  `star (c * Y * c⁻¹) = c⁻¹ * star Y * c` (`star c = c`) and `star (star M)⁻¹ = M⁻¹`.
- `cartan_one`: `cartan 1 = 1`.
- `conj_cartan_mul_star`: `a⁻¹ * R (cartan x) * a * star (a⁻¹ * R x * a) = 1`, i.e. after
  conjugation by `a` the involution is `M ↦ (star M)⁻¹`; group algebra with
  `c⁻¹ = (star a)⁻¹ * a⁻¹`.
- `conj_mem_unitary_of_cartan_eq`: if `cartan x = x` then the matrix of `a⁻¹ * R x * a` is
  unitary (`Matrix.mem_unitaryGroup_iff`).
- `val_conj_cartan_mul_conjTranspose`: the matrix form of `conj_cartan_mul_star`,
  `(a⁻¹ R(θ x) a) (a⁻¹ R(x) a)ᴴ = 1`.
- `val_map_cartan`: `R (cartan x) = c * (R x⁻¹)ᴴ * c⁻¹` as matrices.
- `cartanUnitary R a`: the subgroup
  `Langlands.Group.MatrixPolarCompact.unitarySubgroup` of the realization `x ↦ a⁻¹ * R x * a`;
  `mem_cartanUnitary_iff` (membership is unitarity of the conjugated matrix),
  `mem_cartanUnitary_of_cartan_eq` (fixed points of `cartan` belong to it), and
  `isCompact_cartanUnitary` (it is compact when `R` is a closed embedding for a topology on `X`:
  conjugation by `a` is a homeomorphism of `GL`, and
  `MatrixPolarCompact.isCompact_unitarySubgroup` applies).
