# The triviality locus where sections are free of the expected rank is open

Author: Worker 766.

This module is `Langlands.AlgebraicGeometry.Picard.TrivialLocusOpen`. It imports
`Langlands.AlgebraicGeometry.Picard.TrivialLocusStrata`, and through it the FLT
port's two-term complex theorem, the Library module `KernelColumnSplit` and
the polynomial trick `FrameCombination.exists_flat_trivialization_of_span`.

## Purpose and provenance

This is an internal helper for the proof of the Library statement
`FieldPicardClassEqualizerImmersionStatement`. It treats one stratum. Suppose
that over a Noetherian `k`-algebra `C` the global sections of every base change
of a line bundle `N` on `Spec C ×_k X` are free of rank `a`. Then the fppf
triviality locus of `N` is cut out by an open immersion. The proof shows that
every point in the image of the locus has an open neighbourhood `V` such that
`N` becomes trivial fppf-locally on `V`. Near the point, the global sections of
`N` over `C` span the sections of every base change. So the polynomial trick
produces a flat finitely presented `C`-algebra over which `N` is trivial, and
the image of its spectrum is such a neighbourhood. No literature theorem is
claimed. The construction works directly with the field `K` of a point of an
fppf cover, as provided by `exists_field_of_mem_trivialLocus`. It does not use
the descent of triviality from `K` to a residue field of `Spec C`.

## Conventions

As in `TrivialLocusStrata`. `X : Over (Spec k)` for a field `k`, and `specMap`,
`specOver`, `baseMap`, `trivialLocus`, `isoLocus`, `SectionsRank` and
`SectionsEquivs` are as there.

## Declarations

- `cutsOut_iSup_opens` (namespace `Langlands.AlgebraicGeometry.Picard`): let
  `E` be an fppf-closed sieve on a scheme `Y`. Suppose every point in the image
  of a member of `E` has an open neighbourhood `V` with `V.ι` in `E`. Then the
  union of the opens `V` with `V.ι ∈ E` cuts out `E`. A morphism into the union
  is covered by the preimages of these opens (a Zariski, hence fppf, cover), on
  which it lies in `E`. Conversely a member of `E` has image in the union and
  lifts through the open immersion (`IsOpenImmersion.lift`).
- `RelativePicard.SectionsFree X N a`: for every `C`-algebra `A`, the global
  sections of the base change of `N` along `specMap C A` are `A`-linearly
  equivalent to `Fin a → A`, with `A` acting through
  `pullback.snd (baseMap X C) (specMap C A)`.
- `RelativePicard.exists_open_of_mem_trivialLocus`: let `X.hom` be proper,
  `SectionsRank X a`, `C` Noetherian, and `SectionsFree X N a`. If `g` lies in
  the triviality locus of `N` and `x` is a point of its source, there is an open
  `V` of `Spec C` containing `g x` with `V.ι` in the triviality locus. The proof
  runs as follows.
  1. The FLT theorem gives a two-term complex `G` over `C` with equivalences `ε`
     and the compatibility of `ε` with global sections of `N`.
  2. `exists_field_of_mem_trivialLocus` gives a field `K`, with kernel the prime
     `g x`, along which `N` is trivial.
  3. `exists_columnSplit_of_mem_trivialLocus` gives a column split `S` of `G.d`
     with `a` remaining columns and `S.t ∉ g x`.
  4. `SectionsFree` at `Localization.Away S.t` and `ε` show that the kernel of
     `G.d` is free there with one generator for each remaining column. So the
     Schur complement of `S` vanishes after inverting `S.t`
     (`schurMatrix_map_eq_zero`), and some power `u` of `S.t` kills it over `C`
     (`exists_pow_smul_schurMatrix_eq_zero`).
  5. The global sections `m j := ε₀⁻¹ (kerVector u j)` of `N` therefore span the
     sections over `K`: every element of the kernel of `G.d ⊗ K` is a
     `K`-combination of the vectors `1 ⊗ kerVector u j`
     (`exists_eq_sum_kerVector`), and `ε K` sends the pullback of `m j` to
     `1 ⊗ kerVector u j` by the compatibility of `ε`.
  6. `FrameCombination.exists_flat_trivialization_of_span` gives a flat,
     finitely presented `C`-algebra `A` with a prime over the kernel of `C → K`,
     over which `N` becomes trivial.
  7. `Spec A ⟶ Spec C` is flat and locally of finite presentation, so its image
     `V` is open and contains `g x`. The base change of `Spec A ⟶ Spec C` along
     `V.ι` is surjective, flat and locally of finite presentation. Its composite
     with `V.ι` lies in the isomorphism locus. So `V.ι` lies in the fppf-closed
     triviality locus.
- `RelativePicard.hasImmersionLocus_of_sectionsFree`: under the same
  hypotheses, `HasImmersionLocus X.hom (specOver k C) N` holds, with the open
  immersion of `cutsOut_iSup_opens`.
