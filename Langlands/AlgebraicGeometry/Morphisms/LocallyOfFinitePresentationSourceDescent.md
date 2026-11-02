# Local finite presentation descends along fppf covers of the source

Author: Worker 293. The refinement lemma adapts Worker 1150's published
`Langlands.AlgebraicGeometry.exists_affine_fppf_refinement` (module
`Langlands.AlgebraicGeometry.Morphisms.SourceDescentReduction`).

This module proves the local finite presentation case of Stacks Project,
Descent, Lemma 35.14.3 (Tag 02KL; Lemma 14.3 on p.43 of the registered PDF
source `stacks-descent-ed88ff78-2026`, citing EGA IV 17.7.5).

## Declarations

- `Langlands.AlgebraicGeometry.exists_affine_fppf_refinement_of_locallyOfFinitePresentation`:
  for a surjective, flat, locally finitely presented `f : X ⟶ Y` with `Y`
  affine, there are an affine scheme `Z` and a morphism `p : Z ⟶ X` such that
  `p` is locally of finite presentation and `p ≫ f` is surjective, flat and
  locally of finite presentation.
- `Langlands.AlgebraicGeometry.finitePresentation_of_faithfullyFlat_finitePresentation_comp`:
  Stacks 02KK, finite presentation case, for morphisms `r : R ⟶ A` and
  `s : A ⟶ B` in `CommRingCat`. If `s` is faithfully flat and of finite
  presentation and `r ≫ s` is of finite presentation, then `r` is of finite
  presentation.
- `Langlands.AlgebraicGeometry.locallyOfFinitePresentation_of_surjective_flat_comp`:
  Stacks 02KL, local finite presentation case. For `f : X ⟶ Y` and
  `g : Y ⟶ S`, if `f` is surjective, flat and locally of finite presentation
  and `f ≫ g` is locally of finite presentation, then `g` is locally of
  finite presentation.

## Proofs

Refinement. The proof is Worker 1150's proof with local finite presentation
in place of local finite type for `p`. Flat locally finitely presented
morphisms are open, so `QuasiCompactCover.exists_hom` refines the singleton
cover given by `f` to finitely many affine schemes `Spec (𝒱.X i)`. Each one
maps to `X` by an open immersion. Let `Z` be their finite disjoint union and
`p` the induced map. Then `Z` is affine. Local finite presentation of `p`
is checked on the components, where `p` is an open immersion. Flatness and
local finite presentation of `p ≫ f` are also checked on the components.
Surjectivity holds because the components cover `Y`.

Ring form. This is `Langlands.Algebra.finitePresentation_of_faithfullyFlat_of_finitePresentation`
from `Langlands.Algebra.FinitePresentationSourceDescent`, after turning the
ring homomorphisms into algebra structures with `algebraize`.

Scheme form. The proof follows the Stacks proof.

1. Local finite presentation is local on the target. So it suffices to treat
   the restrictions of `f` and `g` over each affine open `U` of `S`. The
   hypotheses restrict to the preimages of `U`.
2. Local finite presentation is local on the source. So with `S` affine it
   suffices to treat `j ≫ g` for each affine chart `j` of `Y`. Here `f` is
   replaced by its pullback `pullback.snd f j`. This pullback is again
   surjective, flat and locally of finite presentation. The composite
   `pullback.snd f j ≫ j ≫ g = pullback.fst f j ≫ f ≫ g` is locally of finite
   presentation.
3. With `S` and `Y` affine, the refinement gives an affine `Z` with
   `p ≫ f : Z ⟶ Y` surjective, flat and locally of finite presentation, and
   `(p ≫ f) ≫ g` locally of finite presentation. On global sections, a flat
   surjective morphism of affine schemes gives a faithfully flat ring map.
   The ring form then shows that `g.appTop` is of finite presentation. This
   is local finite presentation of `g` for affine schemes.

## Provenance

The statements are the local finite presentation case of Stacks 02KL and its
affine ring form 02KK. The refinement lemma is internal derived content
adapted from Worker 1150's published local finite type version.
