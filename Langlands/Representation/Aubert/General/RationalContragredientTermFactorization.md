# Actual rational-point duality factorization and term comparison

This is an internal conditional specialization of
`ContragredientTermFactorization` and `RationalFiniteLengthDuality`. The former
was authored by Worker 490; the rational specialization was authored by
Worker 196. The two closed natural-duality propositions and the closed ambient
and dynamic-Levi finite-length admissibility propositions remain explicit
inputs. Neither this construction nor its supporting theorem proves them or
the closed `RationalContragredientCommutationStatement`.

`finiteLengthInductionJacquetDualityIso` works on the actual rational points
of any connected reductive group over any nonarchimedean local field. For a
standard subset `I` and any actual standard cocharacter `ζ` for it, let `rO`
be the normalized Jacquet functor of the inverse-cocharacter opposite
parabolic. The literal standard Levi is the target of `rO`. For a finite-length
ambient object `A`, the definition constructs

`iP (rP (A.contragredient)) ≅ (iP (rO A)).contragredient`.

It first applies
`oppositeJacquet_preservesFiniteLength_of_rationalDuality` to derive finite
length of `rO A` from standard Jacquet preservation, the displayed ambient
smooth-dual preservation and the explicit duality/admissibility inputs. This
uses the published smooth-dual admissibility reflection and admissible
biduality, with standard-Levi compact-open cofinality derived from its actual
topology. The construction then feeds `finiteLengthJacquetDualityIso` and
`finiteLengthInductionDualityIso` at that finite-length opposite Jacquet
object into `inductionJacquetDualityFactorizationIso`. That definition applies
the actual standard induction functor to the Jacquet isomorphism and composes
with the inverse induction-duality isomorphism. No new naturality statement
is asserted here.

`standardContragredientTermComparison_of_rationalDuality` specializes
`contragredientTermComparison_of_duality` to the literal standard rational
family and to actual inverse-cocharacter opposites. It accepts any family of
witnessed standard cocharacters; `standardCocharacterForDuality` provides one
from the original standard-cocharacter input. No compatibility between choices
is assumed. Besides the closed duality and admissibility inputs, its remaining
hypotheses are exactly:

- a cardinality-preserving equivalence `e` of the simple-root subsets;
- actual ambient elements `g I` with membership identities
  `x ∈ P(e I) ↔ (g I)⁻¹ * x * g I ∈ P_opposite(I)`, and the same orientation
  for the actual Levi and unipotent subgroups;
- equality of the exact finite-length Grothendieck classes of opposite and
  standard normalized induction of every finite-length object on the same
  literal Levi, for arbitrary finite-length witnesses of the two outputs.

The proof supplies the original `standardParabolicFiniteLength` package and
derives ambient compact-open cofinality from the displayed nonarchimedean
group topology. Opposite Jacquet finite length and both duality components
come from the same constructions used above. No separate opposite-induction
finite-length premise is introduced: the generic theorem transports finite
length through the actual induction-Jacquet conjugation isomorphism. The
relative-root-system input supplies a finite simple-root type, including the
empty type. The result is exactly the already published
`standardContragredientTermComparison`, which can be passed to
`rationalContragredientCommutation_of_standardTermComparison`.

The canonical rational-point topology is `pointTopology`. The carrier
universe is `max (u + 1) v` for independent `u` and `v`; no splitness,
quasisplitness, characteristic-zero or nonempty-root hypothesis is imposed.
The Grothendieck classes retain every actual short-exact-sequence relation.
The proof uses no Langlands classification, character independence, geometric
lemma, adjointness or cuspidal-support theorem. Actual opposite-to-standard
geometry, opposite/standard induction class comparison, and the four closed
representation-theoretic inputs still require their separately owned proofs.
The original closed commutation target and all its visible premises are
unchanged.
