# Global functions on base changes of a proper scheme over a field

Author: Worker 766.

This module is `Langlands.AlgebraicGeometry.Picard.FieldBaseChangeSections`. It
imports `Langlands.AlgebraicGeometry.Picard.TrivialLocusComparison` and two
theorems of the Library's port of the Anthropic FLT formalization:
`Scheme.Modules.exists_twoTermComplex_sectionsEquiv_forall_baseChange` (a
two-term complex of finite free modules computing the global sections of all
base changes of a module on a proper flat scheme over a Noetherian ring) and
`Module.Flat.bijective_kerBaseChangeHom_and_nonempty_homology_baseChange_linearEquiv`
(kernels commute with flat base change).

## Purpose and provenance

This is an internal helper for the proof of the Library statement
`FieldPicardClassEqualizerImmersionStatement`. When a line bundle `N` on
`Spec A ×_k X` becomes trivial, its global sections are the global functions
on `Spec A ×_k X`. These form a free `A`-module whose rank `a` does not depend
on `A`. This rank fixes the number of remaining columns used later to
stratify the base. No literature theorem is claimed. The fact proved is the
degree-zero case of flat base change for coherent cohomology over a field. Here
it is derived from the FLT port's two-term complex together with the flatness
of every `k`-algebra over the field `k`.

## Conventions

- `specMap R A` is `Spec.map (CommRingCat.ofHom (algebraMap R A))`.
- `AlgebraicSpace.specOver k A` (opened as `specOver`) is
  `Over.mk (specMap k A)`, the spectrum of a `k`-algebra over `Spec k`.
- Global sections of a module on a scheme `P` with a morphism
  `p : P ⟶ Spec A` are an `A`-module through `moduleSectionsOfHom p`.

## Declarations

- An instance `Subsingleton (Spec (.of k))` for a field `k`: the spectrum of a
  field has one point. With Mathlib's instance for integral schemes, it makes
  every morphism to `Spec k` flat.
- `SectionsComparison.exists_unitSectionsEquiv_of_field`: let
  `f : X ⟶ Spec k` be proper. There is `a : ℕ` such that, for every
  `k`-algebra `A` and every pullback square `IsPullback q p f (specMap k A)`
  with `p : P ⟶ Spec A`, the global sections of the structure sheaf of `P` are
  `A`-linearly equivalent to `Fin a → A`. The proof applies the FLT two-term
  complex theorem to the structure sheaf of `X`, which is trivially locally
  trivial, and takes `a` to be the `k`-dimension of the kernel of the complex.
  For a `k`-algebra `A`, the sections over the chosen base change are the kernel
  of the base-changed complex. Since `A` is flat over `k`, this kernel is
  `A ⊗_k ker d`, which is free on the base change of a `k`-basis. The chosen
  base change is transported to `P` by `unitSectionsEquivOfIsPullback`.
- `RelativePicard.baseMap X R` is the projection
  `pullback.fst (specOver k R).hom X.hom` from `Spec R ×_k X` to `Spec R`.
- `RelativePicard.SectionsRank X a` is the following proposition. Let `R` be a
  `k`-algebra, `N` a line bundle on `Spec R ×_k X`, and `A` an `R`-algebra,
  compatibly a `k`-algebra. Suppose `specMap R A` lies in the isomorphism
  locus of `N` and the trivial bundle. Then the global sections of the pullback
  of `N` along `pullback.fst (baseMap X R) (specMap R A)` are `A`-linearly
  equivalent to `Fin a → A`, with `A` acting through
  `pullback.snd (baseMap X R) (specMap R A)`.
- `RelativePicard.exists_sectionsRank`: for proper `X.hom` there is `a` with
  `SectionsRank X a`. The bundle is trivial on the base change by
  `nonempty_pullback_iso_trivial_of_mem`. The base change is a pullback of
  `X.hom` along `specMap k A` by pasting two pullback squares
  (`IsPullback.paste_horiz`, `FrameCombination.specMap_comp`). Then
  `exists_unitSectionsEquiv_of_field` applies.
