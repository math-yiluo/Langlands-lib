# Limits and the decomposition `P(χ) = U(χ) ⋊ Z(χ)` on points

This module proves general facts about the dynamic subgroup functors of
`Langlands.GroupScheme.Dynamic.Basic`. They hold for a cocharacter `χ : 𝔾_m ⟶ G` of a group
scheme `G` over an arbitrary base scheme `S`, on every test scheme `T` over `S`. Here
`HasLimit χ g l` means that some extension `E` of the orbit map of `g` to `T ×_S 𝔸¹` has value `l`
at zero. The facts are:

- `HasLimit.mul` and `HasLimit.inv`: limits are multiplicative. If `E` and `E'` extend the orbits
  of `g` and `h`, then `E * E'` extends the orbit of `g * h` and has value `l * m` at zero.
  Inverses work the same way. This uses `IsOrbitExtension.mul`, `IsOrbitExtension.inv`,
  `evalZero_mul` and `evalZero_inv` from the Library.
- `HasLimit.mem_parabolic` and `exists_hasLimit`: a point has a limit exactly when it lies in
  `P(χ)`.
- `conj_mem_unipotent`: if `p ∈ P(χ)` has limit `l` and `u ∈ U(χ)`, then `p * u * p⁻¹` has limit
  `l * 1 * l⁻¹ = 1`. So `U(χ)` is normalized by `P(χ)` (`unipotent_isNormalizedBy_parabolic`).
  On every test scheme it is a normal subgroup of the points of `P(χ)`
  (`unipotent_subgroupOf_parabolic_normal`).
- `eq_one_of_mem_centralizer_of_mem_unipotent`: a point of `Z(χ)` has itself as limit
  (`hasLimit_of_mem_centralizer`). If limits are unique, a point of both `Z(χ)` and `U(χ)` is
  `1`.
- `isComplement'_unipotent_centralizer`: assume that limits are unique and lie in `Z(χ)`. Then
  on every test scheme the points of `U(χ)` and of `Z(χ)` are complementary subgroups of the
  points of `P(χ)`. They meet trivially by the previous item. A point `x ∈ P(χ)` with limit `l`
  is `(x * l⁻¹) * l`, where `x * l⁻¹` has limit `l * l⁻¹ = 1`. The proof uses Mathlib's
  `Subgroup.isComplement'_of_disjoint_and_mul_eq_univ`.

The two hypotheses of the last item are not proved here for general `G`. For an affine group
over a ring `k` and test algebras over `k`, Conrad–Gabber–Prasad, *Pseudo-reductive groups*
(2nd ed., 2015), Lemma 2.1.4 (printed p. 49) notes that the extension of the orbit map is
unique, and Lemma 2.1.5 (printed pp. 50–51) shows that the limit map is a homomorphism
`P(λ) → G` with kernel `U(λ)` and that `Z(λ)` is the centralizer. The module `Langlands.GroupScheme.Dynamic.GeneralLinearOrbit` proves them
directly for diagonal cocharacters of `GL_n`. With them, the item is the points-level form of
CGP, Proposition 2.1.8(2) (printed p. 53): multiplication `Z(χ) ⋉ U(χ) → P(χ)` is an isomorphism.
The general hypotheses and their discharge for `GL_n` are internal to this formalization.
