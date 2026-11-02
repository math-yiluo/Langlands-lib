# The universal closed-factorization locus

This module defines a coordinate-projectivity predicate and a proposition target.
It states the existence of a closed locus and does not prove that existence.
Both declarations are in namespace `Langlands.AlgebraicGeometry`.

For a commutative ring `R : CommRingCat.{u}` and an actual scheme
`X : Over (Spec R)`, let `A = ((algΓ R).obj X).unop`. This is the
global-section algebra with its structural `R`-algebra map.
`HasFpqcProjectiveCoordinateModule X` means that there exists a commutative
`R`-algebra `B : CommAlgCat.{u} R` such that `Module.FaithfullyFlat R B` and
`Module.Projective B (B ⊗[R] A)`. There is no finite-generation assumption
on either algebra or on the projective module. For affine `X`, this tensor
product is its coordinate algebra after extension to `Spec B`. Affineness
and flatness of `X → Spec R` are separate premises of the main target.

`ClosedFactorizationLocusStatement.{u}` quantifies over every such `R` and `X`
with affine flat structural morphism and this coordinate-projectivity
property. For every pair of schemes `Y, D` over `Spec R` and every
`d : D ⟶ X ⊗ Y` whose underlying scheme morphism `d.left` is a closed
immersion, it asserts the existence of a scheme `Z` over `Spec R` and a
morphism `i : Z ⟶ Y` with `IsClosedImmersion i.left`. These witnesses must
work simultaneously for every test scheme `T` over `Spec R` and every
`t : T ⟶ Y`, with the equivalence

```lean
(∃ z : T ⟶ Z, z ≫ i = t) ↔
  ∃ q : X ⊗ T ⟶ D, q ≫ d = (X ◁ t).
```

Here `⊗` is the categorical product in the cartesian monoidal category
`Over (Spec R)`, so its underlying scheme is the fiber product over
`Spec R`. Whiskering `X ◁ t` is the product morphism
`id_X × t : X ×_R T → X ×_R Y`. All compositions and equalities are
those of actual scheme morphisms over the base. The right side requires
factorization of the entire scheme `X ×_R T` through `D`; it retains
nilpotent structure. It is preserved by every refinement `T' → T` by
composition with the induced product morphism.

Thus `Z → Y` represents the subfunctor of the functor of points of `Y`
consisting of maps whose full product with `X` lies in `D`. Both
factorizations are unique when they exist because closed immersions are
monomorphisms; the statement only needs existence. The test scheme need
not be affine or reduced. Neither `Y` nor `D` is required to be affine,
separated, of finite type or Noetherian. The universe `u` is arbitrary.
The existence of `Z` is the conclusion, with no representability premise.

The source is Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition
(2015), Proposition A.8.10(1) and its proof, printed pp.547–549
(PDF pp.573–575), registered as
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
The proposition itself concerns fixed loci for group actions. This generic
formulation extracts the closed-subfunctor construction inside its proof.
After faithfully flat descent, the proof embeds the projective coordinate
module as a direct summand of a free module, forms coefficient ideals for
the ideal of `D` on affine opens of `Y`, and checks compatibility with
localization to glue them. Its factorization criterion on p.549 uses the
closed subscheme `D` and the coordinate module, without using a group law
or an action. In the source, separatedness of `Y` ensures that the action's
equalizer `D` is closed. Here closedness of `d` is supplied directly, so
that separatedness condition is unnecessary.

The source tests the resulting locus on affine schemes. The all-scheme
formulation here is the corresponding Zariski-local extension: maps into
a closed subscheme, and factorization through a closed immersion, can
both be checked and glued on an affine open cover of the test scheme.
Flatness, affineness and projectivity after faithfully flat extension are
retained from the source. This extraction and the helper predicate are
derived interfaces, not additional claims quoted verbatim from CGP.
The module imports Mathlib's generic algebra-valued global-section
functor; it does not depend on the Library's group-action or
fixed-representability declarations.
