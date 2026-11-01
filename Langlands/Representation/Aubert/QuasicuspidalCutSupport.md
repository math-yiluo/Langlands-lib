# Actual constituent support and Jacquet detection for cut degrees

This internal prerequisite proves detection for the actual Aubert cut degrees on
finite-length subquotients of quasicuspidal induction. It retains the supplied
p-adic field and topology, independent universes `uF` and `uV`, and actual smooth
carriers in `Type (max uF uV)`. Positive rank is assumed in the geometric-filtration
arguments. The inducing representation is finite length and quasicuspidal; neither
it nor its chosen subquotient is required to be irreducible.

`DegreesDetected F T B π` is a proposition about every actual
`ActualCutComplex.degreeObject T π.representation k`. Every nonzero actual smooth
subquotient of every degree must have a nonzero normalized Jacquet module at some
Levi associated to `B`. The associated Levi may depend on that subquotient. This is
the all-subquotient detector required for exactness reflection, rather than a
claim only about irreducible degree constituents.

## Exact classes of the geometric filtration

`inducedGeometricPieceK0_quasicuspidal` applies the published compatibility between
induction and each geometric piece. A proper source refinement has zero normalized
Jacquet class by quasicuspidality. The whole source refinement gives the original
induced class through the published whole-refinement induction--Jacquet identity.
Thus an induced geometric piece has either zero class or the original induced
class, according to its source refinement.

`inductionJacquetInduction_natural_multiple` applies actual normalized induction
to the exact Grothendieck-class identity of the geometric filtration. It sums those
pieces and obtains, for every target shape `C`, a natural number `N` such that

```
[i_C r_C i_B σ] = N • [i_B σ].
```

Here the brackets are classes in the existing finite-length Grothendieck group
with all actual short exact relations. The natural number counts the pieces with
whole source refinement. No direct-sum decomposition or splitting of the actual
representation is asserted.

## Actual support and transport

`normalizedInduction_subquotient` transports an actual injective/surjective
presentation through normalized parabolic induction, using the published
injectivity and surjectivity results for its actual maps.
`normalizedInductionJacquet_subquotient` combines this with actual Jacquet
subquotient transport. These helpers are separated so the more complicated
induced objects do not require repeated expansion of their carrier instances.

The published constituent-support criterion turns the natural-multiple identity
into `inductionJacquetInduction_constituentSupport`: every actual irreducible
subquotient of `i_C r_C i_B σ` occurs in `i_B σ`. Transport and actual subquotient
transitivity give `inductionJacquet_constituentSupport` for `i_C r_C π` whenever
`π` is an actual subquotient of `i_B σ`.

`finiteTerm_val` identifies the existing actual finite term with the object of the
actual induction--Jacquet composite; the equality is definitional. Consequently
`term_constituentSupport` applies the support theorem to the unchanged actual cut
term. `degree_constituentSupport` then uses the existing exact finite-product
class sum and the constituent-support finite-sum criterion to obtain the same
support bound for every actual finite degree. No choice of a split model of a
degree or differential is made.

## Detection of every degree subquotient

`detects_of_constituentSupport` takes a nonzero subquotient `D` of a finite-length
object with the stated support bound. Finite length passes to `D`, so `D` has an
actual irreducible subquotient `S`. The support bound places `S` in the original
quasicuspidal induction. The published `cuspidalInductionSubquotientJacquet`
theorem gives an associated Levi with nonzero Jacquet module of `S`. Actual
Jacquet subquotient preservation then forces the Jacquet module of `D` to be
nonzero: a subquotient of a zero carrier would have zero carrier.

`term_detectsSubquotients` and `degree_detectsSubquotients` instantiate this
argument with the proved actual term and degree support bounds.
`degreesDetected` packages the latter result as `DegreesDetected F T B π`.

## Provenance and scope

The content is an internal derivation from the published geometric-filtration
Grothendieck identity, compatibility of induced geometric pieces, quasicuspidal
refinement vanishing, actual subquotient transport, and natural composition
multiplicities. It introduces no external source assertion or classification
input. It proves the detector on the actual terms and degrees. It does not prove
Jacquet concentration, identify filtered graded differentials, establish actual
cut-complex concentration, or prove `SignedEffectivityStatement`; those further
steps remain necessary.
