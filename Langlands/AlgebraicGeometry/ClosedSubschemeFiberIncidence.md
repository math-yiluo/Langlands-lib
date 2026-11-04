# Closed-subscheme incidence in actual fibres

This is a derived prerequisite for the generic geometric-connectedness argument
in Stacks Project Lemma 37.28.4 (055G), supporting Conrad's Theorem 3.4(2).
It proves preservation of a finite intersection pattern over a Noetherian base.
It does not prove spreading of geometric irreducibility, identification of the
irreducible components of nearby fibres, generic constancy of geometric
connectedness, or Conrad's full descent assertion.

The registered source is
`stacks-fibre-constructibility-local-dimension-2026-11-04`, retained
`055C.html`, Lemma 37.28.4, proof from the definition of the closed subsets
`Z_{i,j}` through the final intersection-pattern argument. The source shrinks
using generic flatness and openness. Here, over a Noetherian base, the existing
Mathlib Chevalley theorem gives constructible images, which yields the same
finite incidence-preservation step directly. This is an internal derived
comparison, not a transcription of that entire source proof.

All scheme objects have arbitrary common universe `u`. The finite indexing type
has an independent universe `v`. No affineness or separation hypothesis is used.

## Actual constructions

For an actual morphism `f : X ⟶ Y`, a family `g i : Z i ⟶ X`, and a point
`y : Y`, `fiberSubschemeSets f g y i` is the inverse image of the actual range
of `g i` under `f.fiberι y`. Thus it is a subset of Mathlib's scheme-theoretic
fibre `f.fiber y`, formed by pullback along the residue-field point of `Y`.
`range_baseChange_eq_fiberSubschemeSets` identifies this subset with the range
of the actual base-change projection
`pullback (g i) (f.fiberι y) ⟶ f.fiber y`.
When `g i` is a closed immersion, that projection is a closed immersion.

`closedSubschemeFiberIncidence f g y i j` is the nonempty intersection of these
two subsets in the actual fibre. The definition itself makes sense for arbitrary
`g`; closedness is imposed by the shrinking theorem. Equal indices are permitted,
so diagonal incidence detects nonemptiness of the corresponding member.
`preimage_fiberι_nonempty_iff` uses the exact range of `f.fiberι y` to identify
nonempty inverse image of any subset `s` with membership of `y` in `f '' s`.
Consequently `closedSubschemeFiberIncidence_iff` identifies incidence with
membership in `f '' (range (g i) ∩ range (g j))`.

## Proved comparisons

For any topological space and a point generic for the whole space,
`exists_open_constructible_membership` proves that membership in one
constructible subset agrees with membership at that point throughout an open
neighbourhood. It inducts on the Boolean algebra defining constructibility:
an open generator either contains the generic point or is empty; unions use
intersection of the two neighbourhoods; complements retain a neighbourhood.
No Noetherian or sobriety hypothesis is needed. The finite-family theorem takes
the intersection of the finitely many resulting open neighbourhoods.
The empty indexing family is allowed.

`exists_open_finiteType_image_membership` applies this to the ranges of any
finite family of locally finite-type quasi-compact morphisms into a Noetherian
scheme. Locally finite type over a locally Noetherian scheme implies locally
finite presentation, so Mathlib's Chevalley theorem makes each range
constructible. No quasi-separatedness assumption is added to the morphisms.

`exists_open_closedSubschemeFiberIncidence` assumes `Y` is a Noetherian scheme,
`f` is locally finite type and quasi-compact, each `g i` is a closed immersion,
and the family is finite. It obtains an open set containing the given generic
point on which every incidence predicate agrees with its generic value.
The source `X` is Noetherian by finite type over `Y`. Each closed intersection
of ranges is constructible in `X`; its image is constructible by Chevalley.
The finite-family result applied to pairs of indices and the actual-fibre image
comparison prove the assertion. The open set is nonempty because it contains
the generic point. A generic point for the whole base is an explicit hypothesis;
neither its existence nor irreducibility of the whole base is an assumed
structural field.

These are intrinsic construction and image comparisons. The source's general
non-Noetherian spreading assertions, geometric field-extension comparisons,
and the remaining geometric-connectedness proof are separate obligations.
