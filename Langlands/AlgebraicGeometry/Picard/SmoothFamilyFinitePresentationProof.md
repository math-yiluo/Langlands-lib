# Local finite presentation of a universal smooth-family parameter: proof

`Langlands.AbelianScheme.smoothFamilyFinitePresentation.{u}` proves exactly the
published statement
`Langlands.AbelianScheme.SmoothFamilyFinitePresentationStatement.{u}`. The
universe is arbitrary and there are no extra outer hypotheses. Stated in
words: let `S` be a quasi-separated scheme, `A` an abelian scheme over `S`, and
`P : Over S` an arbitrary parameter with an actual rigidified family `L` that
is universal for smooth-family algebraically trivial classes on quasi-separated
tests. Then `P.hom` is locally of finite presentation. The theorem places no
condition on `P.left`.

## Inputs

The proof only combines theorems already published in the Library:

- `finiteTypeSmoothFamilyAbelianRepresentability`
  (`FiniteTypeSmoothFamilyAbelianRepresentabilityProof`) proves the
  representer over affine bases `Spec R` with `R` of finite type over `ℤ`.
- `smoothFamilyAbelianRepresentabilityOfFiniteType`
  (`SmoothFamilyAbelianRepresentabilityOfFiniteTypeProof`) turns that
  finite-type case into `SmoothFamilyAbelianRepresentabilityStatement.{u}`.
  Over every quasi-separated base `S` this gives an actual abelian scheme `B`
  and an actual rigidified family `M` on `B.X` that is universal on
  quasi-separated tests.
- `smoothFamilyUniversalComparison` (`SmoothFamilyUniversalComparisonProof`)
  says that two universal families, the first with a quasi-separated
  parameter, have parameters related by a unique isomorphism over `S`
  compatible with the families. The second parameter may be arbitrary.
- `AlgebraicGeometry.quasiSeparatedSpace_of_quasiSeparated` from Mathlib, and
  Mathlib's instances for local finite presentation of isomorphisms, of smooth
  morphisms and of composites.

## The Lean proof

1. Introduce `S`, its quasi-separatedness instance, `A`, `P`, `L` and the
   universality hypothesis `hL`.
2. Apply `smoothFamilyAbelianRepresentabilityOfFiniteType` to
   `finiteTypeSmoothFamilyAbelianRepresentability` and then to `S` and `A`.
   This gives an abelian scheme `B` over `S`, a rigidified family `M` on `B.X`
   and the universality proof `hM`.
3. The structure morphism `B.X.hom` of an abelian scheme is proper, hence
   quasi-separated, and `S` is quasi-separated. So
   `quasiSeparatedSpace_of_quasiSeparated B.X.hom` makes the space `B.X.left`
   quasi-separated. This is the instance the comparison theorem needs for its
   first parameter.
4. Apply `smoothFamilyUniversalComparison S A B.X P M L hM hL` to get an
   isomorphism `e : B.X ≅ P` in `Over S`. Its uniqueness and the family
   compatibility are discarded. The given family `L` stays in the argument
   because the comparison is applied to `L` and `hL`.
5. `e.inv.left` is the image of `e.inv` under `Over.forget S`, so it is an
   isomorphism of schemes. The slice triangle `Over.w e.inv` says
   `e.inv.left ≫ B.X.hom = P.hom`.
6. Rewrite the goal along this triangle. The goal becomes local finite
   presentation of `e.inv.left ≫ B.X.hom`, which instance search closes:
   isomorphisms are locally of finite presentation, the smooth morphism
   `B.X.hom` is too, and the property is stable under composition.

## Scope and provenance

This is a derived internal argument about Library predicates. It makes no new
claim about the literature. The route is the one in the published Markdown of
the target statement: an actual representer, the actual functor comparison,
and transport of a property of the smooth abelian-scheme parameter along the
isomorphism. The representer and the comparison are imported as published
proofs and are not reproved here. The proof does not use
`RelativeDualSchemeFinitePresentationStatement` or
`RelativeDualSchemeGeometryStatement`. It adds no axioms, `sorry` or other
proof holes. A development `lean_check` reported only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`.
