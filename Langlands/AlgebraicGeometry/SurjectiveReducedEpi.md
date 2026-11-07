# Surjective morphisms onto reduced schemes are epimorphisms

Worker 1425 authored this module as a helper for the proof task
`5dc6c43c-2acc-40a0-92ad-454b4232a509` (central torus and derived subgroup
generation for connected reductive groups). It supplies the final conjunct
`Epi (subgroupProductMap i d)` of
`Langlands.GroupScheme.ReductiveCentralDerivedProductStatement` once the
underlying map of the product morphism is known to be surjective.

## Scheme-level results (`Langlands.AlgebraicGeometry.SurjectiveReducedEpi`)

`ext_of_fromSpecResidueField_eq` states that two morphisms `g h : Y ⟶ T` out of a
reduced scheme `Y` are equal once `Y.fromSpecResidueField y ≫ g` and
`Y.fromSpecResidueField y ≫ h` agree for every point `y`. The target `T` is an
arbitrary scheme, with no separatedness hypothesis. The proof is local on `Y`
through Mathlib's `Scheme.hom_ext_of_forall`. First, evaluating the hypothesis at
the unique point of `Spec κ(y)` gives `g y = h y`. Then choose an affine open `V`
of `T` containing this point, and let `U` be the intersection of the preimages of
`V` under `g` and `h`. Both restrictions `U.ι ≫ g` and `U.ι ≫ h` factor through
`V.ι` by `Scheme.Hom.resLE_comp_ι`. The two factorizations `U ⟶ V` agree by
Mathlib's `AlgebraicGeometry.ext_of_fromSpecResidueField_eq`, applied with the
dense set of all points of `U` and with `V ⟶ ⊤_ Scheme` as the separated morphism
(an affine scheme is separated). `U` is reduced as an open subscheme of `Y`. Its
residue-field hypothesis follows from the one on `Y` by cancelling the monomorphism
`V.ι` and rewriting with
`Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField` for `U.ι`.

`epi_SpecMap_of_fields` states that `Spec.map φ` is an epimorphism of schemes for
every ring homomorphism `φ` between fields. It is surjective because `Spec` of a
field has exactly one point. It is flat because every module over a field is flat,
transported through `HasRingHomProperty.Spec_iff` for `Flat`. Mathlib's
`Flat.epi_of_flat_of_surjective` then gives the epimorphism.

`epi_of_surjective` states that a morphism `f : X ⟶ Y` with surjective underlying
map and reduced target `Y` is an epimorphism in the category of all schemes. If
`f ≫ g = f ≫ h`, apply `ext_of_fromSpecResidueField_eq`. For a point `y`, choose
`x` with `f x = y`. By `Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField`,
`Spec.map (f.residueFieldMap x) ≫ Y.fromSpecResidueField (f x)` equals
`X.fromSpecResidueField x ≫ f`. The map `Spec.map (f.residueFieldMap x)` is an
epimorphism by `epi_SpecMap_of_fields`, so it cancels.

`over_epi_of_surjective` states that a morphism `f : A ⟶ B` in `Over S` is an
epimorphism there once `f.left` is surjective and `B.left` is reduced. The
forgetful functor `Over.forget S` is faithful, so it reflects epimorphisms.

## Group-scheme consequences (`Langlands.GroupScheme`)

`epi_subgroupProductMap_of_surjective_of_smooth` states the following. Let `k`
be a field and let `G`, `Z`, `D` be group schemes over `Spec k` with
homomorphisms `i : Z ⟶ G` and `d : D ⟶ G`. Assume `Smooth G.X.hom` and that the
underlying function of `(subgroupProductMap i d).left` is surjective. Then
`subgroupProductMap i d` is an epimorphism in `Over (Spec k)`. The proof uses the
Library result
`Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field`,
which makes `G.X.left` reduced, and then applies `over_epi_of_surjective`.

`IsConnectedReductive.epi_subgroupProductMap_of_surjective` is the same statement
for a connected reductive `G`, with smoothness taken from the `smooth` field of
`IsConnectedReductive`.

No finiteness, separatedness, connectedness or group-structure hypothesis is
used in the scheme-level results.

The scheme-level statements are standard. The flat surjective case is Mathlib's
`Flat.epi_of_flat_of_surjective`, which Mathlib attributes to Stacks Project
Tag 02VW. The reduced-target case follows from the fact that a morphism out of a
reduced scheme is determined by its values on residue-field points.
