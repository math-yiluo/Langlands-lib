# Smoothness of cut-out subgroup schemes from infinitesimal lifting

This module works over a commutative ring `R`. It fixes a group-valued functor `F` on commutative `R`-algebras, corepresented by `B` through `e`, and a family of subgroups `H A ⊆ F A` cut out by an ideal `J` of `B` (`IsCutOutBy e H J`). It turns an infinitesimal lifting property of `H` into smoothness of the cut-out group scheme `cutGroupScheme`, whose underlying scheme is `Spec (B ⧸ J)`.

## Definitions

- `reduction C N` is the quotient map `C ⟶ C ⧸ N` in `CommAlgCat R`.
- `HasSquareZeroLifting H` means the following. For every `R`-algebra `C` and ideal `N` with `N ^ 2 = ⊥`, every element of `H (C ⧸ N)` is the image under `F.map (reduction C N)` of an element of `H C`.

## Results

- `formallySmooth_of_hasSquareZeroLifting`: if `H` is cut out by `J` and has the square-zero lifting property, then `B ⧸ J` is formally smooth over `R`.

  The proof uses Mathlib's criterion `Algebra.FormallySmooth.of_comp_surjective`. Given an `R`-algebra map `g : B ⧸ J → C ⧸ N` with `N ^ 2 = ⊥`, the point of `F (C ⧸ N)` classified by `B → B ⧸ J → C ⧸ N` lies in `H`. A lift `y ∈ H C` has a classifying map `B → C` that kills `J`. The induced map `B ⧸ J → C` reduces to `g` by naturality of the corepresentation.
- `smooth_cutGroupScheme`: if `B ⧸ J` is a smooth `R`-algebra (formally smooth and of finite presentation, `Algebra.Smooth`), then `(cutGroupScheme hJ).X.hom` is a smooth morphism over `Spec R`. The structure morphism is `Spec` of `R → B ⧸ J`. Mathlib's `HasRingHomProperty.Spec_iff` for smooth morphisms and `RingHom.smooth_algebraMap` identify the two notions.
- `finitePresentation_quotient`: over a noetherian ring, every quotient of a finite-type algebra is of finite presentation (Mathlib's `Algebra.FinitePresentation.of_finiteType`).
- `smooth_groupScheme_iff`: the corepresented group scheme `Spec B` is smooth over `Spec R` exactly when `B` is a smooth `R`-algebra.
- `AffineCoordinates.smooth_algebra`: for a smooth group scheme `G` over `Spec R` whose underlying scheme is affine, the published coordinate algebra `AffineCoordinates.algebra G` is a smooth `R`-algebra. The proof transports smoothness along `AffineCoordinates.groupSchemeIso G`; an isomorphism is an open immersion and so smooth, and smooth morphisms compose.

Together these give the route to smoothness used for the normalizer and centralizer of a split torus. Over a field, the representing closed subgroups from `NormalizerRepresentability` are cut-out group schemes `Spec (B ⧸ J)`, with `B` of finite type when `G` is smooth. Smoothness of such a representative then reduces to the square-zero lifting property of its family of algebra points.

## Provenance

This is an internal construction toward task `0f453442`. It uses the infinitesimal lifting characterization of formal smoothness; Mathlib's definition of `Algebra.Smooth` is formal smoothness plus finite presentation. No source result is formalized here beyond these standard Mathlib facts.
