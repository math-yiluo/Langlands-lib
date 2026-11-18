# Points of a group scheme are separated by an fppf cover of the base

Namespace `Langlands.GroupScheme.AffineCoverSeparation`. This internal module supplies the final
separation step of the proof of `WeilAbelianImageTrivialityStatement`. `A` is a commutative ring
in universe `u`.

## Definitions

- `tensorAlg X P` (abbreviation): the `A`-algebra `X ⊗[A] P`, for `A`-algebras `X` and `P`.
- `inclLeft X P` (definition): the inclusion `X ⟶ X ⊗[A] P`, `x ↦ x ⊗ 1`.
- `specCover P hflat hfp hsurj` (definition): for a family `P i` (index type in universe `u`) of
  `A`-algebras with `A → P i` flat (`hflat`) and of finite presentation (`hfp`), such that every
  prime of `A` is the contraction of a prime of some `P i` (`hsurj`), the fppf cover
  (precoverage `Flat ⊓ LocallyOfFinitePresentation`) of `Spec A` by the maps
  `Spec (P i) → Spec A`. It is built with `Scheme.Cover.mkOfCovers`; the morphism properties come
  from `Flat.SpecMap_iff` and `LocallyOfFinitePresentation.SpecMap_iff`.

## The separation theorem

- `affinePoint_eq_of_cover`: let `M` be any group scheme over `Spec A` and `X` an `A`-algebra. Two
  points `a b` of `M` over `X` are equal if their images over `X ⊗[A] P i` (along `inclLeft`) are
  equal for every `i`.

  Proof. Pull the cover `specCover` back along `Spec X → Spec A` (`pullback₁`; fppf covers are
  stable under base change). The pulled-back cover is an effective epimorphic family
  (`RelativeDerived.effectiveEpiFamily_fppfCover`), so it suffices to compare `a` and `b` after
  each projection `pullback (Spec X → Spec A) (Spec (P i) → Spec A) ⟶ Spec X`. This projection is
  the composition of the isomorphism `pullbackSpecIso` with `Spec` of `inclLeft`
  (`pullbackSpecIso_hom_fst`), and the hypothesis compares `a` and `b` after `Spec` of `inclLeft`.

## Provenance

Internal. This is the separatedness of the point functor of a scheme for the fppf topology,
specialized to covers of an affine base by affine pieces and pulled back to `Spec X`.
