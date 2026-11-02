# Local finite type descent along fppf covers of the source: proof

Authors: Worker 1103, Worker 866, Worker 1150.

This module proves the published proposition
`Langlands.AlgebraicGeometry.LocallyOfFiniteTypeSourceDescentStatement.{u}`
(Stacks Descent, Lemma 35.14.3, Tag 02KL, local finite type branch) as the
theorem
`Langlands.AlgebraicGeometry.locallyOfFiniteType_of_surjective_flat_locallyOfFinitePresentation_comp`.
If `f : X ⟶ Y` is surjective, flat and locally of finite presentation and
`f ≫ g` is locally of finite type, then `g` is locally of finite type. The
module adds no axioms.

The proof is written in two layers. The first two theorems take the flat
finitely presented model theorem (Stacks Algebra, Lemma 10.168.1(1)) as an
explicit hypothesis `hmodel`. The final theorem discharges `hmodel` with
`Langlands.Algebra.exists_flat_finitePresentation_model` from
`Langlands.Algebra.FlatFinitePresentationModel`.

## Implemented proof

`finiteType_of_faithfullyFlat_finitePresentation_of_model` proves Stacks
Tag 0367 for morphisms `r : R ⟶ A` and `s : A ⟶ B` of `CommRingCat.{u}`.
If `s` is faithfully flat and of finite presentation and `r ≫ s` is of finite
type, then `r` is of finite type. The proof rewrites `(r ≫ s).hom` as
`s.hom.comp r.hom`. `algebraize` then turns the ring homomorphisms into
algebra structures with `IsScalarTower R A B`, so that `hff` becomes
`Module.FaithfullyFlat A B`. Applying `hmodel` to `A → B` (finitely
presented by `hfp`, flat because faithfully flat) gives the model, and
`Langlands.Algebra.finiteType_of_faithfullyFlat_of_flat_model` (module
`Langlands.Algebra.FaithfullyFlatFinitePresentationModel`) concludes.

`locallyOfFiniteType_sourceDescent_of_model` introduces the schemes, the
morphisms `f : X ⟶ Y`, `g : Y ⟶ S` and the four hypotheses. It then applies
Worker 1150's `locallyOfFiniteType_sourceDescent_of_ring` (module
`Langlands.AlgebraicGeometry.Morphisms.SourceDescentReduction`) to the
previous ring lemma. That reduction works Zariski locally on `S` and `Y`,
refines `f` by a finite affine fppf cover, and passes to global sections.

`locallyOfFiniteType_of_surjective_flat_locallyOfFinitePresentation_comp`
is `locallyOfFiniteType_sourceDescent_of_model` applied to
`Langlands.Algebra.exists_flat_finitePresentation_model`. Its type is exactly
`LocallyOfFiniteTypeSourceDescentStatement.{u}`.
