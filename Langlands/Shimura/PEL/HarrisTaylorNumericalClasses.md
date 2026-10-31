# Actual action classes with the Harris–Taylor numerical conditions

This fixed-base construction uses actual abelian schemes over
`S : Scheme.{0}`, an actual structure map `s : S → Spec K`, and unital
rational algebra actions `A →ₐ[ℚ] End0 B`. Here `L` and `K` are CM
number fields with `Algebra L K`, `A` is a rational algebra with
`Algebra K A`, and `E` is a number field used to specify the dimension
factor. All fields and the algebra are in universe zero, as in the
imported central-trace construction.

The ambient type is the published
`RationalAlgebraAction.IsoClass S A`. It is the actual quotient of
abelian schemes with algebra action by equivariant isomorphism in the
rational category. The Hom groups of that category are
`ℚ ⊗[ℤ] (B ⟶ B')`; an isomorphism includes an actual inverse and both
composition identities.

## Central trace descent

`centralLieTraceCondition_actionIso` applies the published
all-chart trace-invariance theorem to the actual rational isomorphism
underlying an equivariant action isomorphism. The action intertwines
every element of `A`, so in particular it intertwines the central
elements coming from `K`.

`CentralLieTraceClassCondition` is a genuine quotient lift to `Prop`.
Its well-definedness is proved by the preceding invariance theorem and
propositional extensionality. The representative formula and
`centralLieTraceClassCondition_iff_of_classOf_eq` show that it agrees
with the all-chart central trace test on every actual representative.
It does not select a basis or an arbitrarily supplied trace. The
imported test quantifies over actual finite free Lie charts and all
smaller opens, using the differential of the actual rational action.

## Numerical classes

`NumericalActionClassCondition q` means that an actual representative
`X` of the ambient rational-isomorphism class `q` satisfies

```text
X.abelianScheme.HasRelativeDimension ([E : ℚ] * n²)
  ∧ CentralLieTraceCondition L s X.abelianScheme X.action n.
```

The dimension predicate is the published abbreviation for
`SmoothOfRelativeDimension` of the actual structure morphism.
`NumericalActionClass` is the image of these satisfying representatives
inside the ambient quotient, implemented as a subtype using this
existential predicate.

The following properties are proved:

- An actual satisfying representative defines a numerical class.
- Two satisfying representatives define the same numerical class
  exactly when they admit an actual equivariant rational isomorphism.
  The expanded criterion retains the inverse and the equation
  intertwining every element of `A`.
- Every numerical class has an actual satisfying representative.
- Forgetting the numerical restriction is injective into the ambient
  action quotient.
- Every representative of a numerical class satisfies the central
  trace test.

The equality criterion and representative-surjectivity theorem describe
precisely the quotient of the satisfying objects by the restricted
equivariant rational-isomorphism relation. The existential dimension
condition is part of this image construction. This file does not prove
that every ambient representative has the geometric dimension of a
satisfying representative. In particular, the final representative
theorem concludes only the central trace condition. Arbitrary-base
geometric dimension preservation under rational isomorphism is a
separate target, `RationalIsoRelativeDimensionStatement`.

No nonempty, reduced, connected or locally noetherian hypothesis on `S`
is imposed. The construction does not assert that the class type is
inhabited. It does not provide pullback maps: arbitrary-base
naturality of the central trace test requires the actual Lie
base-change compatibility and trace comparison.

## Source and derived scope

Harris and Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.1, printed pages 89–91 / PDF pages 97–99, give the
source conditions. Printed page 89 prescribes dimension `d n²`;
Lemma III.1.2(3), printed page 90, gives the central Lie trace formula;
printed page 91 identifies quadruples by rational isogenies
intertwining the algebra actions and carrying the polarization and
level data. The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

This is a derived construction isolating the dimension-and-central-trace
action part of that moduli problem. In the source notation the imaginary
quadratic field `E` is Lean's `L`, the CM field `F` is Lean's `K`, the
totally real field `F⁺` is Lean's dimension field `E`, and the algebra
`B` is Lean's `A`. The imported numerical condition retains the exact
central formula. The quotient and image proofs themselves use only the
listed weaker field/algebra hypotheses; they do not establish the
source's compositum hypotheses, signatures, positivity, polarization,
level orbit or the equivalence with its `Lie⁺` compatibility definition.

The source moduli functor is on connected locally noetherian schemes
over its indicated CM field. The present fixed-base image construction
is meaningful over any `K`-scheme, without claiming the source
representability theorem in that broader scope. It does not identify
this CM base with the independently constructed cocharacter reflex
field. The full polarized level functor, its reflex/base-field
comparison, geometric-point independence, representability and scheme
levels remain further obligations.

The implemented proofs use the already constructed actual rational
action quotient and the proved central-trace invariance. They introduce
no assumed dimension-preservation theorem or selected geometric model.
