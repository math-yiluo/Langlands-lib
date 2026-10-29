# Lifting the field smooth-family comparison

This module proves that the field comparison
`Langlands.AbelianScheme.SmoothFamilyTranslationInvarianceStatement.{u}`
implies the whole aggregate
`Langlands.AbelianScheme.SmoothFamilyPicardZeroComparisonStatement.{u}`.
It does not prove the field comparison. Every theorem here takes it as an
explicit hypothesis `h`.

## Declarations

- `isFibrewiseAlgebraicallyTrivialViaSmoothFamily_iff_of_field h A L`: for
  any base `S`, any abelian scheme `A` over `S` and any actual
  `L : LineBundle A.X.left`, gives
  `IsFibrewiseAlgebraicallyTrivialViaSmoothFamily A L ↔ IsGeometricallyPicardZero A L`.
- `isAlgebraicallyTrivialFamilyViaSmoothFamily_iff_of_field h A L`: for any
  `T : Over S` and `L : RigidifiedFamily A T`, gives
  `IsAlgebraicallyTrivialFamilyViaSmoothFamily A L ↔ IsPicardZeroFamily A L`.
- `isAlgebraicallyTrivialClassViaSmoothFamily_iff_of_field h A q`: for any
  `q : RigidifiedClasses A T`, gives
  `IsAlgebraicallyTrivialClassViaSmoothFamily A q ↔ IsPicardZeroClass A q`.
- `smoothFamilyPicardZeroComparison_of_field h`: the aggregate statement.
  Its first conjunct is `h` itself, and the other three are the lifts above.

## Proof

The two fibre predicates quantify over the same data: a universe-`u`
algebraically closed field `K` and a point `s : Spec K ⟶ S`. Each tests
the same actual bundle `fibreLineBundle A L s` on the same abelian scheme
`(baseChange s).obj A`. So the fibre lift is `forall_congr'` over these
binders, applied to `h K ((baseChange s).obj A) (fibreLineBundle A L s)`.

Both family predicates unfold to the fibre predicates of the abelian
scheme `(baseChange T.hom).obj A`. Each is evaluated at the same
`familyLineBundle A L`, which pulls the underlying bundle back along the
inverse of `relativeSpaceSymmetry`. So the family lift is the fibre lift
for that abelian scheme and bundle.

Both class predicates are `Quotient.lift`s of the two family predicates
through actual rigidified isomorphism, under the same setoid. Hence
`Quotient.inductionOn` reduces the class lift to the family lift on a
representative. The descended predicates then reduce definitionally.

## Scope

This module adds no hypothesis beyond the field comparison. Bases and
tests stay arbitrary, with no quasi-separatedness or reducedness
restriction. The substantive mathematics is the field comparison, which
is still an explicit input. It requires the theorem of the cube with a
non-proper third factor for the forward direction. The reverse direction
needs (7.21) of Edixhoven, van der Geer and Moonen together with an ample
bundle on the abelian variety.
