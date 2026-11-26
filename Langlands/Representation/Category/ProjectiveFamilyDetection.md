# Detection of nonzero maps by a family of projective smooth representations

Module `Langlands.Representation.Category.ProjectiveFamilyDetection`, namespace
`Langlands.SmoothRep`.

This is an internal criterion for smooth complex representations of an arbitrary topological
group `G`, at one carrier universe. It is the version, for a class of objects, of the published
`SmoothRep.exists_comp_ne_zero_of_projective_subquotients` (module
`Langlands.Representation.Category.ProjectiveGeneration`), which uses a single projective
object. It is used in the proof of `LeviCenterComponentsLiftStatement` (module
`Langlands.Representation.CuspidalSupport.LeviCenterComponentsLift`).

## Statement

`exists_comp_ne_zero_of_projective_family`. Let `Q` be an `ObjectProperty` of
`SmoothRep.{0, uG, uV} ℂ G` such that

- every object `P` with `Q P` is projective;
- every irreducible smooth representation `D` receives a nonzero morphism `P ⟶ D` from some
  object `P` with `Q P`.

Then for every nonzero morphism `d : X ⟶ Y` there are `P` with `Q P` and `s : P ⟶ X` with
`s ≫ d ≠ 0`.

## Proof as implemented

The argument is that of `exists_comp_ne_zero_of_projective_subquotients`; only the choice of the
projective object moves after the choice of the irreducible subquotient.

1. Since `d ≠ 0`, some vector has nonzero image, so the image `image d` of `d` is nontrivial.
   The published `exists_isIrreducible_isSubquotient_of_nontrivial` gives an irreducible
   subquotient `D` of `image d`.
2. The detection hypothesis gives `P` with `Q P` and a nonzero `a : P ⟶ D`. The subquotient
   relation provides a subrepresentation `C` of `image d` (inclusion `i`, injective) and a
   surjection `q : C ⟶ D`. Projectivity of `P` lifts `a` through `q` to `r : P ⟶ C`; then
   `b = r ≫ i : P ⟶ image d` is nonzero, since `r ≫ q = a ≠ 0` and `i` is a monomorphism.
3. The corestriction `X ⟶ image d` of `d` is surjective. Projectivity of `P` lifts `b` to
   `s : P ⟶ X`. Then `s ≫ d = b ≫ imageι d`, which is nonzero because `imageι d` is injective.
