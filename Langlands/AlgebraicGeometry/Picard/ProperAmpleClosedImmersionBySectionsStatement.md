# Projective embeddings by sections from properness and ampleness

Author: Worker 1543.

`Langlands.AlgebraicGeometry.Picard.ProperAmpleClosedImmersionBySectionsStatement.{u}`
is a proposition, with no proof asserted here. For every noetherian commutative
ring `R : Type u`, scheme `X : Scheme.{u}` and proper morphism
`f : X ⟶ Spec (CommRingCat.of R)`, the existence of an ample line bundle on `X`
implies that there is an actual module sheaf `M : X.Modules` with
`Scheme.Modules.IsInvertible M` and
`Scheme.Modules.ClosedImmersionBySections M f`.

The last predicate supplies a finite integer `N`, actual global sections of
`M`, and a closed immersion into the polynomial Proj projective space over
`R`. Its structure map composes to `f`; its sections satisfy the specified
local frame and coordinate-ratio identities. There is no assumption of
flatness, smoothness, geometric integrality, a section of `f`, or an already
given embedding. The output module is not required to be a specified tensor
power of the input ample bundle. All schemes remain in universe `u`.

This is a derived specialization of the Stacks Project's affine-base
projectivity results. Lemma 29.38.5 ([tag 01VK](https://stacks.math.columbia.edu/tag/01VK))
identifies absolute and relative ampleness over an affine base. Section 29.44
([tag 01W7](https://stacks.math.columbia.edu/tag/01W7)), Lemma 29.44.13(1),
turns proper quasi-projective morphisms over a quasi-compact quasi-separated
base into projective morphisms. Lemma 29.44.16(1) then gives H-projectivity
because an affine scheme has an ample structure sheaf. The finite-type
hypothesis in quasi-projectivity follows from properness.

The registered originals are
`stacks-fibre-ampleness-affine-neighbourhood-2026-11-02`, file `01VK.html`,
and `stacks-projective-space-twists-morphisms-2026-10-26`, file `01W7.html`.
Their full statements, proofs and comments were checked. The comments on
these passages change no assertion used here. No corresponding project
erratum was found.

The auxiliary theorem
`exists_closedImmersionBySections_iff_isHProjective` is proved in this module.
From a sections presentation it keeps the actual closed immersion and its
structure-map equation. Conversely, it applies the published theorem
`AlgebraicGeometry.ProjSpace.exists_projPresentation_toProj_eq_and_locallyTrivial`
to an H-projective embedding, then rewrites its structure-map equation.
This constructs the required invertible module and all presentation laws.
This direction generalizes the same internal construction in
`Langlands.AbelianScheme.AffineHomSchemePieces.exists_lineBundle` without
using any abelian-scheme hypotheses or importing that module. The auxiliary
proof supplies no proof of the main proper-and-ample assertion.

This is the projective-embedding prerequisite of
`NoetherianIntegralFibrePicardSheafAFSchemeStatement`. It does not assert
representability of a Hilbert or Picard functor.
