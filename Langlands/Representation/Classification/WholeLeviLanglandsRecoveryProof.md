# Standard Langlands recovery for arbitrary whole-Levi inputs

Worker 545 authored the shared conditional assembly. Worker 1155 supplied
the closed assembly with fixed-parameter recovery on the original carriers.
Worker 1437 combined and checked this work and prepared the contribution.
The imported results retain their documented authorship.

`Langlands.glWholeLeviLanglandsRecovery.{uF,uV,uW,uJ,uK}` has exactly the
type `Langlands.GLWholeLeviLanglandsRecoveryStatement.{uF,uV,uW,uJ,uK}`.
The field and all four representation carrier universes are independent.
Its inputs are arbitrary irreducible analytically tempered whole-Levi
representations, strictly decreasing real exponent vectors and equivalent
arbitrary irreducible quotients of their actual normalized twisted inductions.

The proof applies `glWholeLeviTemperedFactorization` separately to the two
input representations. This proved theorem derives admissibility from the
whole-Levi analytic predicate, uses the same-universe algebraic Levi
factorization, transports whole-Levi temperedness through its actual
equivalence and reflects it to each factor by `glBlockTensorTempered`.
It supplies smooth irreducible tempered block factors in each original
carrier universe and actual equivalences from the original inputs to their
untwisted external tensors. No factorization or factorwise temperedness is
an extra premise.

The constructions in `WholeLeviQuotientUniverse` lift these factors and the
given quotients to the common carrier universe `max uF uV uW uJ uK`.
The first side uses auxiliary universe `max uW uK`; the second uses
`max uV uJ`. Smoothness of each original quotient follows from its given
surjective intertwiner. `liftedDatum` forms the two regular tempered data,
and `isLanglandsQuotient_quotientLift` transports each given quotient witness
using the actual equivalence of its standard module with induction of the
twisted original representation. That equivalence twists the lifted
whole-Levi factorization and applies normalized induction. Composing with
the original quotient map and the quotient lift preserves surjectivity.
`quotientLiftIso` turns the given equivalence of the original quotients
into a smooth isomorphism of their lifts. The quotient witnesses remain
arbitrary surjective intertwiners throughout.

`glRegularLanglandsParameterUniqueness` applies in this common universe and
returns an order isomorphism matching block ranks and exponents.
`GeneralLinear.BlockShape.eq_of_orderIso` converts the rank matching to
literal equality of the ordered shapes. Eliminating this equality reduces
both explicit `Eq.rec` transports in the target to identity transports,
with the original stored `Rep` instances. The self-order isomorphism of
the resulting finite linear order is the identity, so the exponent matching
gives equality of the real vectors. After eliminating that equality, compose
the second original quotient map with the inverse of the supplied quotient
equivalence. The two original twisted inductions then surject onto the same
original irreducible representation `J`. `fixedRegularLeviRecovery` from
`RegularLanglandsTensorRecoveryProof` applies directly to these maps and
the original analytically tempered whole-Levi inputs. It recovers an actual
equivalence of their untwisted representations in the independent original
carrier universes. This final step needs no further universe descent.

This is an internal derivation from the named Library results and the
unchanged target. The paired explanations of those results document their
analytic, algebraic and source inputs. This file makes no additional
assertion from external literature. It preserves the supplied p-adic field
and topology, positive rank, arbitrary ordered positive block shapes,
actual normalized induction and analytic temperedness, all real central
shifts and the one-block case. It introduces no universe domination
premise, chosen head, support witness or classification hypothesis.
Neither the proof nor its import closure uses
`SemistandardLanglandsStatement`; semistandard conjugacy and full regular
data uniqueness are downstream consumers.
