# Actual additive root maps and rational generation for split SLₙ

For an arbitrary finite index type `n : Type` with a decidable equality and
commutative base ring `R : CommRingCat.{u}`, this internal construction gives
the actual homomorphism
`SpecialLinear.Root.rootMap R hij : Ga ⟶ SpecialLinear.groupScheme n R`
for every pair of distinct indices `i`, `j`.
On every scheme `T` over `Spec R`, its matrix is the transvection
`1 + x Eᵢⱼ`, where `x` is the actual additive coordinate in `Γ(T, 𝒪_T)`.
The test scheme need not be affine.

The ring-level `transvectionHom` is additive multiplication of transvections.
The theorem `map_transvection` verifies compatibility with every coefficient
ring homomorphism. The definition `rootPoints` uses the existing
`SpecialLinear.pointsEquiv` and `VectorGroup.coordinates` to give the natural
homomorphism on each actual test-point group. The group-valued Yoneda
constructor `homOfPoints` then gives `rootMap`, and `pointsEquiv_rootMap`
proves its matrix formula on every test scheme.

The definition `matrixRingEquiv` applies an actual coefficient-ring
equivalence entrywise to determinant-one matrices. Applying it to the
canonical global-sections equivalence for `Spec k` defines
`rationalMatrixEquiv`, a multiplicative equivalence between actual base-valued
points of SLₙ and determinant-one matrices over the base ring `k`.
The theorem `rationalMatrixEquiv_rootMap` identifies each actual root image
with its scalar transvection. Conversely, `exists_rational_rootPoint`
constructs an actual additive point giving every prescribed scalar
transvection.

For every field `k : Type u`, `diag2n_decompose` proves the following
identity for distinct indices `i`, `j` and a nonzero scalar `a`:

```text
diag(a at i, a⁻¹ at j, 1 elsewhere)
  = Tᵢⱼ(a) Tⱼᵢ(-a⁻¹) Tᵢⱼ(a) Tᵢⱼ(-1) Tⱼᵢ(1) Tᵢⱼ(-1).
```

The proof compares matrix entries, separates the indices `i`, `j` and their
complement, and simplifies products of matrix units. This extends the binary
six-transvection identity to arbitrary finite index types.
Mathlib's `Matrix.SpecialLinearGroup.diagonal_transvection_induction'`
already reduces determinant-one matrices over a field to these two-entry
diagonals, scalar transvections and products. The theorem
`eq_top_of_transvections` applies this reduction to membership in a subgroup.
For a subsingleton index type, the whole matrix group is subsingleton and
the subgroup equality follows directly. Thus no lower bound on `n` is needed.

The theorem `eq_top_of_root_images` transfers this result through the actual
rational matrix equivalence. Any abstract subgroup containing the ranges of
all the actual maps `rootMap R hij` is the whole actual rational-point group.
The theorem `iSup_root_ranges_eq_top` expresses the same generation as the
supremum of those ranges. These are ordinary subgroup-generation statements;
no normality assumption on the tested subgroup is needed. They hold over
every field, in every characteristic, including finite fields.

The provenance is internal. The all-test constructions extend the existing
binary construction in `SpecialLinearBinaryRootGroups` using the general
matrix and vector coordinate equivalences. The generation argument combines
the displayed direct matrix identity with the existing Mathlib diagonal
reduction. This unit does not identify these coordinate-root images with the
Library's relative-root subgroup functors at a specified torus, prove
parabolic-radical generation for arbitrary SLₙ, classify general simply
connected groups, or prove the unrestricted local Kneser–Tits statement.
