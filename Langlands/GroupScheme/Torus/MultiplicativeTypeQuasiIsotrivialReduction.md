# Quasi-isotriviality: reducing to the étale-local assertion

Author: Worker 743 (Task 6941, `cb433511-4d2d-4361-b34b-2a0eff7b495e`).

This helper module serves the proof of
`Langlands.GroupScheme.MultiplicativeTypeQuasiIsotrivialStatement` (Conrad, *Reductive group
schemes* (2014), Proposition B.3.4, pp.290–292). It proves no part of that proposition outright.
It shows that the whole statement follows from its first assertion, and that the first
assertion follows from a pointwise form. Both results are implications: the pointwise
étale-local splitting is an explicit hypothesis, to be supplied by a separate module.

Throughout, `IsDiagonalizable` and `IsMultiplicativeType` are the Library predicates of
`Langlands.GroupScheme.Torus.RelativeMultiplicativeType`. An étale cover is a
`Scheme.Cover.{u} (Scheme.precoverage @Etale) S`, the encoding used by the target statement.

## Declarations

All names are in `Langlands.GroupScheme.MultiplicativeTypeQuasiIsotrivial`.

- `surjective_specAlgebraMap_of_finite_etale`: if `A` and `R'` are local rings and `R'` is a
  finite étale `A`-algebra, then `Spec R' ⟶ Spec A` is surjective.
- `exists_finite_etale_of_etale_cover`: let `A` be a henselian local ring and `H` a group
  scheme over `Spec A`. If `H` becomes diagonalizable over every member of an étale cover
  of `Spec A`, then there are `S'` and `p : S' ⟶ Spec A` with `p` finite, étale and
  surjective and `H` diagonalizable after base change along `p`. This is the deduction of
  assertion (2) of the target from assertion (1). Conrad makes the same deduction with
  EGA IV₄ 18.5.11.
- `exists_etale_cover_of_pointwise`: let every point `s` of `S` lie in the image of an étale
  morphism `f : U ⟶ S` with `(GroupScheme.baseChange f).obj H` diagonalizable. Then some étale
  cover of `S` diagonalizes `H` over each of its members.
- `multiplicativeTypeQuasiIsotrivial_of_etale`: assertion (1) of the target, taken as a
  hypothesis for all `S` and `H`, implies
  `MultiplicativeTypeQuasiIsotrivialStatement.{u}`.
- `multiplicativeTypeQuasiIsotrivial_of_pointwise`: the hypothesis "every group of
  multiplicative type has, at every point `s` of its base, an étale neighbourhood
  `f : U ⟶ S` with `s ∈ Set.range f` over which it is diagonalizable" implies
  `MultiplicativeTypeQuasiIsotrivialStatement.{u}`.

## Proofs

**Surjectivity.** `R'` is a finitely presented `A`-module
(`Module.FinitePresentation.of_finite_of_finitePresentation`, since `R'` is a finite and
finitely presented `A`-algebra). It is flat because it is étale, so it is free over the local
ring `A` (`Module.free_of_flat_of_isLocalRing`). A nonzero free module is faithfully flat.
`flat_and_surjective_SpecMap_iff` then turns faithful flatness into surjectivity of the map
on spectra.

**Henselian assertion.** Choose a member `𝒰.f i` of the cover whose image contains the
closed point `x` of `Spec A`, and a point `y` over `x`. Choose an affine open
`Spec C ⟶ 𝒰.X i` containing `y`, using `Scheme.affineOpenCover`. The composite
`f : Spec C ⟶ Spec A` is étale and its image contains `x`. The published
`Langlands.CommutativeAlgebra.henselianFiniteEtaleRefinement` gives a local finite étale
`A`-algebra `R'` and `g : Spec R' ⟶ Spec C` with `g ≫ f = Spec.algebraMap A R'`. Take
`p = Spec.algebraMap A R'`:

- `p` is finite by `IsFinite.SpecMap_iff` and `RingHom.finite_algebraMap`;
- `p` is étale by `HasRingHomProperty.Spec_iff` and `RingHom.etale_algebraMap`;
- `p` is surjective by the lemma above.

Diagonalizability of `H` over `𝒰.X i` survives base change along
`g ≫ (Spec C ⟶ 𝒰.X i)` (`IsDiagonalizable.baseChange`). The result is transported to
the base change along `p` by the Library comparison `Descent.pullbackComparison`, using
`(g ≫ (Spec C ⟶ 𝒰.X i)) ≫ 𝒰.f i = p`.

**Cover from points.** With choices `U s`, `f s` for each point `s`, the family indexed by
the points of `S` (a type in universe `u`) is an étale cover by `Scheme.Cover.mkOfCovers`.

**Assembly.** The whole statement is the first assertion together with
`exists_finite_etale_of_etale_cover` applied to the cover it provides. The pointwise
version composes this with `exists_etale_cover_of_pointwise`.
