# Independence of absolute degree-two restriction from the closure embedding

Author: Worker 160.

`Langlands.ClassFieldTheory.Local.AbsoluteRestrictionClosureIndependence`
is a proposition-valued definition. It states that the published actual
absolute restriction morphism in degree two is independent of the compatible
algebra structure between the specified algebraic closures. This module
states the proposition; it does not prove it.

## Exact scope

For every universe `u`, let `K` and `L` be fields in `Type u`, with a fixed
`Algebra K L`. Take any two algebra structures `α` and `β` of
`AlgebraicClosure K` on `AlgebraicClosure L`. Require separately that each
structure makes `K`, `AlgebraicClosure K`, and `AlgebraicClosure L` a scalar
tower, relative to the fixed base map from `K` to `L` and the canonical
inclusion of `L` into its closure. Then the two instances of
`absoluteRestriction K L 2` are equal as morphisms from
`absoluteCohomology K 2` to `absoluteCohomology L 2` in `TopModuleCat` over
`IntegerScalars.{u}`.

Each side explicitly installs its own algebra structure and scalar-tower
certificate. The proposition thus quantifies over every compatible closure
embedding, without restricting to Mathlib's chosen lift. An algebra map
between these fields is injective. Compatibility is only over `K`; no extra
condition relating the chosen closure embedding to an intermediate copy of
`L` is imposed. No finite-dimensional, Galois, characteristic-zero, local-field,
or invariant-existence hypothesis occurs.

The arbitrary universe parameter is retained. Both field carriers lie in
the same arbitrary universe because the published `absoluteRestriction` API
uses one lifted integer scalar ring for its source and target. The statement
does not construct a restriction API between separately lifted scalar rings.

## Actual cohomology and maps

The sole import is `Langlands.ClassFieldTheory.Local.Cohomology`, unchanged.
Its `absoluteCohomology K 2` is Mathlib's continuous cohomology of the actual
absolute Galois group, acting on the units of the full algebraic closure of
`K`, in additive notation with the discrete topology. `absoluteRestriction`
is `ContinuousCohomology.map` for `Field.absoluteGaloisGroup.mapOfAlgebra`
and the corresponding inclusion of closure units. The target is equality
of these actual continuous linear maps, not an equivalence of representation
models or an equality of the underlying Galois restriction homomorphisms.

## Provenance and role

This is a derived formulation of Serre, *Local Fields*, English translation
by Marvin Jay Greenberg (1979), Chapter X, Section 4, Proposition 5, printed
pp.155–156 (PDF pp.161–162). Serre proves independence of the induced
cohomology map from the field embedding, using the inner-conjugation result
of Chapter VII, Section 5, Proposition 3, printed pp.115–116 (PDF pp.121–122).
The original pages were read directly. Registered source:
`serre-1979-local-fields`,
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

The formulation specializes to degree two and to the Library's fixed
algebraic-closure unit modules. It uses full algebraic closures and all field
characteristics, whereas Serre's discussion uses Galois extensions and
separable closures. This adaptation is justified mathematically by normal
restriction in full algebraic closures: two compatible embeddings differ by
an automorphism of the source closure. To prove the proposition in Lean one
must still construct the comparison for these actual coefficient maps and
prove that its inner-conjugation action is trivial on actual continuous
cohomology. Neither result is assumed or asserted as proved in this module.

This is a focused prerequisite for `AbsoluteInvariantExistence`. It supplies
no invariant isomorphism, finite-stage arithmetic normalization, or degree
formula. The stronger all-degree independence statement and comparison
between different models of the algebraic closure are outside its scope.
