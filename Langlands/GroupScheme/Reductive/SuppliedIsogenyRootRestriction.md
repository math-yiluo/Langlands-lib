# Actual supplied-root restrictions over arbitrary rings

This internal derived module extends the actual root restriction construction to
an arbitrary commutative ring `R`, including nonreduced and zero rings. It keeps
supplied full reduced fibrewise coordinate root data `P` and `Q`, an isogeny
`r : RootDatumIsogeny p Q P`, and compatibility of the actual torus homomorphism
with every fixed-exponent character. The ambient homomorphism has the supplied
torus square. The source and target group schemes are affine; the target is
reductive with a fibrewise maximal coordinate torus. No finiteness, flatness or
surjectivity of the ambient homomorphism, source reductivity, or local-ring
hypothesis is required.

The namespace `SuppliedRootIsogeny` preserves the existing local-ring API in
`RelativeIsogeny`. The new subgroup-containment theorem additionally takes an
actual target additive root parametrization. Both source and target
parametrizations are explicit inputs to the restriction construction; this
module does not construct global root coordinates from field data.

`IsFibrewiseRootDatumOf.pairing_of_nontrivial` identifies the coordinate pairing
with the integer dot product when `R` is nontrivial. It chooses a maximal ideal
and applies the existing fibrewise pairing theorem over its quotient field.
The lemmas `dot_coweightMap`, `root_dot_coweightMap` and
`isolating_coweightMap` use this identity to transport an isolating root
cocharacter through the coweight map. The root-line argument uses reducedness
and the injectivity of the supplied weight map. These combinatorial lemmas
retain a nontriviality hypothesis because fibrewise root-data compatibility is
vacuous over the zero ring. `cocharacter_comp_torusHom` compares coordinate
projections to obtain actual cocharacter compatibility, and
`ambient_cocharacter_square` then uses the supplied ambient torus square.
These two helper lemmas also retain nontriviality.

`subgroup_le_comap` has no nontriviality hypothesis. In its nontrivial-ring
branch the proof chooses an isolating source cocharacter using `ULift ℚ`,
independently of the base ring. Its other cocharacter is the source root's
coroot, which pairs to two by the coordinate pairing lemma. Transport gives
a target zero pairing and positive pairing `2 * r.rootFactor b`. The existing
`hasEquivariantFibres_of_isolating_cocharacters` provides actual equivariant
field fibres. `DynamicCutRootParametrization` then identifies the target root
subgroup with its dynamic intersection using the supplied target coordinate
and target smoothness. Functoriality of the dynamic centralizer and positive
subgroup carries every source root point into this intersection on every
scheme test. For the zero-ring branch, the spectrum and every test scheme
over it are empty. Initiality of that test scheme makes the image point the
identity, which belongs to the target root subgroup.

`rootRestriction` restricts the ambient homomorphism through the supplied root
representatives to an actual map `Ga R ⟶ Ga R`.
`rootRestriction_comp` states its exact ambient restriction square. The
construction uses the existing represented-subgroup restriction API. All
subgroup containments and equalities are on arbitrary scheme tests; field
fibres are not used to detect equality of morphisms over the base.

This unit is derived from the imported local restriction's root-line and
field-fibre helpers, the supplied-coordinate dynamic comparison, and the
represented-subgroup API. The old local-ring declarations are unchanged. The
power formula, unit coefficient, alignment and full isogeny rigidity theorem
remain subsequent obligations.
