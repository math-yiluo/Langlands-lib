# Finiteness of the rational character lattice

This file proves `Langlands.GroupScheme.RationalCharacterLatticeStatement`
as the theorem `Langlands.GroupScheme.rationalCharacterLattice`. For every
field `k` and every connected reductive group `G` over `Spec k`, the group
`rationalCharacters G` is a free `ℤ`-module of finite rank. The proof works
for every universe `u` and assumes nothing beyond the statement.

The proof uses only three fields of `IsConnectedReductive G`: smoothness of
`G.X.hom`, affineness of `G.X.hom` (`isAffineHom`), and connectedness of the
underlying space (`connectedSpace`). The fourth field, triviality of the
geometric unipotent radical, is not used.

## The coordinate algebra is a domain

- `isDomain_sections_spec`, `isIntegrallyClosed_sections_spec`: the global
  sections of `Spec k` form a domain and are integrally closed. Both are
  transported from `k` along `Scheme.ΓSpecIso`.
- `isIntegral_of_smooth`: let `X` be locally noetherian, connected and
  smooth over `Spec k`. Then `X` is an integral scheme. The published
  `AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk` shows
  that every stalk of `X` is a domain. The published
  `AlgebraicGeometry.isOpen_irreducibleComponent_of_isDomain_stalk` then
  shows that irreducible components of `X` are open. They are also closed.
  Since `X` is connected and nonempty, the irreducible component of any
  point is all of `X`, so `X` is irreducible. Domain stalks are reduced, so
  `X` is reduced (Mathlib's `isReduced_of_isReduced_stalk`). An irreducible
  reduced scheme is integral.
- `isDomain_coord`: the coordinate algebra `O(G) = Lie.coordinateAlgebra G`
  is a domain. The isomorphism `Lie.coordinateIso G : Spec O(G) ≅ G` over
  `Spec k` is an open immersion. So the structure map
  `Spec O(G) → Spec k` is smooth, being its composite with the smooth map
  `G.X.hom`. `O(G)` is of finite type over `k`
  (`Lie.coordinateAlgebraFiniteType`), hence noetherian. `Spec O(G)` is
  homeomorphic to `G`, hence connected. So `Spec O(G)` is integral by
  `isIntegral_of_smooth`, and `O(G)` is a domain by
  `affine_isIntegral_iff`.

## Assembly

Let `D = O(G)` and let `L` be its fraction field. Define
`w : Multiplicative (rationalCharacters G) →* L` by
`χ ↦ algebraMap D L (unit χ)`, using `CharacterUnits.unit`. It is a monoid
homomorphism by `unit_zero` and `unit_add`. The units are `k`-linearly
independent in `D` by `CharacterUnits.linearIndependent_unit`. The map
`D → L` is injective and `k`-linear, so their images in `L` are
`k`-linearly independent too. Choose a finite set `s` generating `D` as a
`k`-algebra. The image of `s` in `L` generates the image of `D`
(`Algebra.adjoin_image`), and that image contains every value of `w`.
`CharacterLattice.free_and_finite` now gives
`Module.Free ℤ (rationalCharacters G) ∧ Module.Finite ℤ (rationalCharacters G)`.
