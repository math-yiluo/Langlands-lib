# Admissibility of representations and their Hecke modules

Worker 279, Task 5792. This proof targets exactly the published proposition
`Langlands.Hecke.AdmissibleIffHeckeAdmissibleStatement`, with independent group
and carrier universes and no additional hypotheses. The target and its imports
are unchanged.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, III.1.7,
printed p.62 / PDF p.68. The proof uses the compact-open projection construction
of III.1.5.

The auxiliary map `heckeFixedPartInclusion` includes an idempotent-fixed part
with its canonical recovered complex scalars into the original representation.
The Hecke action comes from a complex linear algebra homomorphism and therefore
satisfies the scalar-tower law. The published
`NondegenerateScalars.scalarMul_eq_of_compatible` proves that recovered scalars
equal the given scalars, establishing complex linearity of the inclusion.

`isAdmissible_iff_compactOpen_fixedVectors` uses
`compactOpenSubgroupBasis` to place a compact open subgroup inside each open
subgroup. Antitonicity of fixed vectors embeds the latter's fixed space in the
finite-dimensional compact-open fixed space. The other implication is
restriction of the definition.

For admissible representations, `heckeAction_finiteDimensional_range` shows
that each Hecke operator has finite-dimensional image. Its published proof
places that image inside a compact-open fixed space by bi-invariance of the
test function. Every vector fixed by an idempotent is in that operator's image.
The canonical fixed-part inclusion, restricted to this image, is injective, so
every intrinsic idempotent-fixed part is finite-dimensional.

Conversely, for a compact open subgroup, choose its normalized-indicator
idempotent. Its intrinsic fixed part maps to the representation's subgroup-fixed
space: the normalized indicator always produces fixed vectors and acts as the
identity on this fixed part. The map is surjective because the same indicator
fixes every subgroup-fixed vector. Finite dimension descends along this linear
surjection. The compact-open criterion gives admissibility.

The final theorem `admissibleIffHeckeAdmissible` assembles both equivalences.
These auxiliary maps and finiteness transfers implement Renard's argument using
the Library's existing canonical scalar and projection interfaces.
