# Exact colimits of complexes preserve quasi-isomorphisms

Author: Worker 61. This module depends only on Mathlib: complexes in
functor categories (`Algebra/Homology/Functor`,
`HomologicalComplex.quasiIso_iff_evaluation`), colimits of complexes
computed degreewise (`Algebra/Homology/HomologicalComplexLimits`,
`HomologicalComplex.isColimitOfEval`), `HasExactColimitsOfShape`
(`CategoryTheory/Abelian/GrothendieckAxioms/Basic`), the additivity of
`colim` (`Algebra/Category/Grp/AB`) and the colimit of a constant diagram
over a connected category (`CategoryTheory/Limits/Connected`,
`isColimitConstCocone`).

Everything is in the namespace `Langlands.Cohomology.ExactColimit`.

Notation: `A` is an abelian category, `J` a category, `c` a complex shape on
an index type `ι`, and `HomologicalComplex A c` the category of complexes of
shape `c` (for example `CochainComplex A ℤ`). `f ≫ g` is `f` followed by
`g`. A diagram of complexes is a functor `F : J ⥤ HomologicalComplex A c`.

## Complexes of diagrams

- `functorComplex F`: the complex in the functor category `J ⥤ A` whose
  degree `n` term is `j ↦ (F j).X n` (`F ⋙ eval n`) and whose differential
  is given objectwise by the differentials of the `F j`. It is natural by
  the commutation of the morphisms `F f` with the differentials.
- `functorComplexMap f`: for `f : F ⟶ G`, the morphism
  `functorComplex F ⟶ functorComplex G` given in degree `n` by the
  components of `f` in degree `n`.
- `quasiIso_functorComplexMap f hf`: if every component `f.app j` is a
  quasi-isomorphism, so is `functorComplexMap f`. Mathlib's
  `HomologicalComplex.quasiIso_iff_evaluation` detects quasi-isomorphisms
  in `J ⥤ A` after evaluation at each `j`. Evaluating
  `functorComplexMap f` at `j` gives `f.app j`, by definition.

## Colimits

Assume `[HasColimitsOfShape J A]`.

- `colimitCocone F`: the cocone over `F` whose vertex is
  `colim : (J ⥤ A) ⥤ A` applied degreewise to `functorComplex F`. Its
  degree `n` term is the colimit of `j ↦ (F j).X n` and its differentials
  are induced on colimits. Its legs are the coprojections in each degree.
- `isColimitColimitCocone F`: this cocone is a colimit cocone, since it is
  one in each degree (`HomologicalComplex.isColimitOfEval`).
- `colimitCocone_ι_app_comp_map f j`: the coprojection at `j` of
  `colimitCocone F` followed by `colim` applied degreewise to
  `functorComplexMap f` is `f.app j` followed by the coprojection of
  `colimitCocone G`.

Assume in addition `[HasExactColimitsOfShape J A]`: `colim` preserves finite
limits. It also preserves colimits, being a left adjoint, so it preserves
homology (`Functor.preservesHomology_of_preservesEpis_and_kernels`).

- `quasiIso_isColimit_map f hf hs ht`: for `f : F ⟶ G` with every
  `f.app j` a quasi-isomorphism, and colimit cocones `s` of `F` (`hs`) and
  `t` of `G` (`ht`), the induced morphism `hs.map t f : s.pt ⟶ t.pt` is a
  quasi-isomorphism. Proof: up to the canonical isomorphisms of `s.pt` and
  `t.pt` with the vertices of `colimitCocone F` and `colimitCocone G`
  (checked on coprojections with `colimitCocone_ι_app_comp_map`), it is
  `colim` applied degreewise to `functorComplexMap f`. That map is a
  quasi-isomorphism by `quasiIso_functorComplexMap`, because `colim`
  preserves homology (`HomologicalComplex.quasiIso_map_of_preservesHomology`).
- `quasiIso_colimMap f hf`: the case of the chosen colimits, for `colimMap f`
  (assuming `[HasColimitsOfShape J (HomologicalComplex A c)]`).
- `quasiIso_isColimit_desc hs t ht` (`J` connected): if every leg
  `t.ι.app j` of a cocone `t` over `F` is a quasi-isomorphism, then the
  morphism `hs.desc t : s.pt ⟶ t.pt` from a colimit `s` is a
  quasi-isomorphism. Proof: `hs.desc t` is `hs.map` of the legs `t.ι`,
  viewed as a morphism to the constant diagram at `t.pt`, whose colimit is
  `t.pt` because `J` is connected (`isColimitConstCocone`). Then apply
  `quasiIso_isColimit_map`.

A filtered category is connected (Mathlib's `IsFiltered.isConnected`). For
filtered `J`, `HasExactColimitsOfShape J A` is AB5 for that shape. Mathlib
provides AB5 for abelian groups and for `ModuleCat.{u} R` with
`R : Type u`.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), section 2, printed p.306: "Taking the
direct limit as H shrinks to the identity, we obtain an ℓ-divisible system
of complexes C_m^• of projective Z/ℓ^mZ[S(ẽ)]-modules and a natural
S(ẽ)-equivariant quasi-isomorphism (2.6)". In our reading, (2.6) is the
direct limit over `H` of the quasi-isomorphisms from `C_m^{•,H}` to the
complexes `G_m^•` (one for each `H`). That a direct limit of
quasi-isomorphisms is a quasi-isomorphism is the standard exactness of
filtered colimits of modules, which Harris uses without comment. This
module proves it for any abelian category with exact colimits of the given
shape. The statements and proofs are ours.

Worker 3's published `Langlands.Cohomology.FilteredColimitQuasiIsoStatement`
(Langlands/Cohomology/FilteredColimit/Statement.lean) states, as an unproved
proposition, a related fact for `ℤ`-graded complexes of `ModuleCat.{v} R`
and small filtered `J : Type v`. This module does not prove that
proposition. Its theorems assume `HasExactColimitsOfShape J A` as an
instance, and the module provides no such instance for `ModuleCat.{v} R`
when `R : Type u`.

## Scope

The module proves that exact colimits of complexes preserve
quasi-isomorphisms, in the three forms above. It does not construct
Harris's `C_m^•` or (2.6), does not provide exact-colimit instances for
modules or representations, and does not compare the homology of a colimit
with the colimit of the homology.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies: Mathlib only, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
