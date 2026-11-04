# The preimage of a split torus under a central fppf surjection is commutative

Author: Worker 1387.

This internal module lives in the namespace
`Langlands.GroupScheme.CentralSurjectionImage`.

## The preimage

For homomorphisms `q : G ⟶ H` and `j : T ⟶ H` of group schemes over any scheme
`S`:

- `preimage q j` is the pullback of `q` and `j` in `Grp (Over S)`, with
  projections `preι q j` to `G` and `preπ q j` to `T`, and
  `preι_comp : preι ≫ q = preπ ≫ j`.
- `preimage_isPullback` and `preimage_isPullback_scheme` give the pullback
  squares in `Over S` and in schemes (forgetful functors preserve the pullback).
- By base change, `preπ` inherits flatness, surjectivity and local finite
  presentation from `q` (`preπ_flat`, `preπ_surjective`,
  `preπ_locallyOfFinitePresentation`). `preι` inherits closed immersions from
  `j` (`preι_isClosedImmersion`) and monomorphisms (`preι_mono`).

## Commutators

`comm a b = a b a⁻¹ b⁻¹` in a group. `comm_mul_central`: the commutator is
unchanged by central factors; `comm_mul_left`: if `comm a' b` is central,
`comm (a a') b = comm a b * comm a' b`; `comm_one_right`; `comm_eq_one_iff`.
`comp_comm` and `comm_comp` move commutators of points through composition.

Assume `IsCentral (kernelι q)`.

- `commute_of_comp_eq_one`: a point of `G` killed by `q` is central. It factors
  through the published kernel pullback.
- `commute_inv_mul_of_comp_eq`: points of the preimage with equal images in `T`
  differ by a central point of `G`.
- `comm_comp_eq_one`: if the points of `T` commute, commutators of points of the
  preimage are killed by `q`.
- `commMor : M ⊗ M ⟶ G` is the commutator morphism of `M = preimage q j`, and
  `lift_commMor_eq` says its value on a pair of points depends only on their
  images in `T`.

## Descent

Let `fpqcP` be quasi-compact, flat and surjective. Suppose
`fpqcP (preπ q j).hom.hom.left`. Then `πp = preπ ⊗ preπ` also satisfies it
(`fpqcP_πp`, via `MorphismProperty.pullbackMap`) and is an effective
epimorphism of schemes (`effectiveEpi_πp`, Mathlib's fpqc theorem).
`commMor_scheme_eq` supplies the descent condition. `descComm : T ⊗ T ⟶ G` is
the descended morphism, with `fac_descComm : πp ≫ descComm = commMor` and
`lift_comp_descComm`.

- `descComm_mul`: if `T` has commuting points, `descComm` is multiplicative in
  the first variable on points over every test scheme. The identity is checked
  on the universal triple after precomposing with the epimorphism
  `πp ⊗ preπ` (`epi_of_fpqcP`). There it is `comm_mul_left`, the needed
  centrality coming from `comm_comp_eq_one`.
- `descComm_one`: `descComm` is trivial on `T × 1`. Precompose with the
  epimorphism `preπ`.

## Over a field

Let `k : Type u` be a field, `G` affine over `Spec k`, `T` a commutative group
scheme with `IsSplitTorus T.toGrp`, and `j : T.toGrp ⟶ H`. Assume `q` has central
kernel, `preπ` is fpqc and `preι` is a monomorphism.

- `preimage_mul_comm`: points of the preimage commute. Transport `descComm`
  along `T ≅ 𝔾_m^I ≅ D(ℤ^I)` (published `Diagonalizable.splitIso`). By
  `lift_comp_eq_one_of_bimul` (from `BimultRigidity`) it is trivial. Hence
  `commMor = 1`, and the monomorphism `preι` gives `m m' = m' m`.
- `preimageComm` is the preimage as a `CommGroupScheme`.

This is internal derived content; no literature result is attributed to it.
