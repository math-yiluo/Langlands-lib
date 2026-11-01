# Untwisted source projection for an actual geometric piece

Workers 526 and 828 implemented this route; Workers 359 and 430 supplied the
coordinate, source-twist and normalization guidance. Its provenance is internal
composition of the actual functors, character reflection, admissible
fixed-space extraction and real-part formulas named below.

`Langlands.Geometric.geometricPiece_untwisted_real_projection` starts with
an admissible actual smooth representation `A` of a product Levi `B`,
an arbitrary real coarse vector `t`, and the actual geometric piece of its
coarse real twist. It retains the source and target intersection Levi
equalities with refinements `S` and `R`. A supplied coarse uniform generalized
character `chi` of that piece has real part `y`. The theorem produces an
open-kernel fine generalized character `psi` of the actual normalized upper
refined Jacquet module of the untwisted `A`, its real part `x`, and

```text
y_j = sum over a in target block j of
  (x_(fine block of w^-1 a) / size_(fine block of w^-1 a)
   + t_(coarse source block of w^-1 a)).
```

The proof first uses
`geometricPiece_coarse_character_reflects_fineScalars`: evaluating an actual
induced generalized eigenfunction and using the inverse-intersection scalar
formula reflects `chi` to the source upper refined Jacquet action restricted
to the actual chamber tuple map. The public normalized refined Jacquet
real-twist equivalence removes the source twist from this restricted action.
Its character becomes `chi` times the inverse restricted twisting character.

`exists_eigencharacter_extension` then extracts `psi` in an admissible
fixed space for the actual untwisted Jacquet module. Its flattened scalar
action is central and continuous. This extraction needs finite dimension of
that fixed space, supplied by admissibility, and assumes no finite dimension
of the full carrier. The produced character has open kernel, so
`exists_isRealPartOf` supplies `x`.

`leviRealPowerCharacter_flatten` identifies the source twist on fine
scalars with the fine determinant character whose parameters are pulled
back along `flattenOuter`. Multiplying `psi` by that character restores
`chi` on the chamber tuple group and adds `fineSize * t` to each fine
scalar real coordinate. The numerical projection in
`ChamberRealPartProjection` divides by the positive fine size.
`blockIndex_eq_flatten` identifies the resulting coarse source label and
gives exactly the displayed formula.

The normalized upper Jacquet action keeps its inverse half modulus,
intersection transport uses inverse conjugation, and target induction
keeps right translation and the positive half modulus. There is no
supplied fine character, support, semisimplicity or sign premise.
The conclusion retains the common-power generalized occurrence and
independent field and source-carrier universes.
