# Eigen-covectors of the negative Borel subgroup

This module proves that every nonzero finite representation of a group with a
split pinning has a nonzero covector on which the negative Borel subgroup acts
through the character coordinate of a torus character. It is the Lean form of the
existence of a lowest-weight line for the negative Borel subgroup in the dual
representation.

## The negative unipotent subgroup

- `SplitPinning.negativeUnipotent` is the unipotent group scheme
  `Dynamic.Affine.unipotentScheme` of the opposite of the positive cocharacter
  `p.positiveGm`, that is, the subgroup contracted by the reversed cocharacter.
- `SplitPinning.negativeUnipotentToBorel` is its inclusion into `p.negativeBorel`.
  It is the Library isomorphism `Dynamic.unipotentIsoKernel` onto the kernel of the
  limit map `p.negativeBorelToTorus`, followed by the kernel inclusion `kernelι`.
- `SplitPinning.range_negativeUnipotentToBorel`: its range is the range of
  `kernelι p.negativeBorelToTorus`.
- `SplitPinning.isNormal_range_negativeUnipotentToBorel`: this range is normal,
  since a kernel is normal (`HopfPrimitive.isNormal_range_kernelι`).
- `SplitPinning.isUnipotent_negativeUnipotent`: the subgroup is unipotent, by the
  Library's `Dynamic.isUnipotent_of_isRepresentedBy_unipotent` for the smooth group
  `G`.
- `SplitPinning.exists_negativeUnipotent_factor`: every point `b` of the negative
  Borel subgroup is `t * y` with `t` its torus part
  `b ≫ negativeBorelToTorus ≫ torusToNegativeBorel` and `y` a point of the negative
  unipotent subgroup. Since `torusToNegativeBorel` is a section of the limit map,
  `t⁻¹ * b` lies in the kernel, so it is the image of some `y`.

## The eigen-covector

`SplitPinning.exists_negativeBorel_eigenCovector`: for every
`ρ : MatrixRepresentation G n` with `n` nonempty, there are `ξ : n → k`, `ξ ≠ 0`,
and `lam : characterLattice p.torus` such that, for every scheme test `T` and point
`h` of the negative Borel subgroup,

```text
ξ ᵥ* ρ(h ≫ negativeBorelHom) = pointValue (borelCharacterCoordinate lam) h • ξ
```

with `ξ` mapped to `Γ(T)` by `scalarMap T`.

Proof.

1. Let `σ` be the restriction of the dual representation `ρ.dual` to the negative
   Borel subgroup. Let `D` be the Library's
   `MatrixRepresentation.normalFixedSubrepresentation` of `σ` for the normal
   negative unipotent subgroup. It is the space of vectors fixed by that subgroup,
   with inclusion, retraction and an actual representation of the negative Borel
   subgroup.
2. The negative unipotent subgroup is unipotent, so it has a nonzero fixed vector in
   `σ`. Hence `D` is nonzero.
3. Restricted to the split torus through `p.torusToNegativeBorel`, the representation
   on `D` is the span of its character spaces
   (`iSup_characterSpace_eq_top_of_isSplitTorus`). So some character `χ` of the torus
   has a nonzero vector `w`.
4. On a point `b = t * y` of the negative Borel subgroup, the factor `y` acts
   trivially on `D` (`kills_subgroup`). So `D(b) w = D(t) w = χ(b ≫ limit map) • w`.
   That is, `w` is an eigenvector for the extended character
   `characterRestrict p.negativeBorelToTorus χ`.
5. The image `η = inclusion *ᵥ w` is nonzero, because the retraction recovers `w`.
   By the intertwining property of the inclusion, `σ` acts on `η` through the same
   character.
6. In the dual representation, `σ(h⁻¹) η = χ'(h⁻¹) η` becomes
   `η ᵥ* ρ(h) = χ'(h)⁻¹ • η`. With `lam` the negative of the character-lattice element
   of `χ`, `p.pointAlgebraHom_borelCharacterCoordinate` identifies `χ'(h)⁻¹` with the
   value of the character coordinate of `lam` at `h`. The covector is `ξ = η`.

## Provenance

This is internal. It takes the place of the primitive vectors (eigenvectors for a
Borel subgroup, Definition 22.16) in Milne, *Algebraic Groups* (2017, registered as
`milne-2017-algebraic-groups`). The route through primitive vectors is recorded in
the Markdown of the target statement `SplitHighestWeightClassificationStatement`.
Here the argument uses the opposite Borel subgroup and the dual representation. The
fixed space of the normal unipotent part is a representation of the torus, and a
weight vector there is an eigenvector for the whole Borel subgroup.
