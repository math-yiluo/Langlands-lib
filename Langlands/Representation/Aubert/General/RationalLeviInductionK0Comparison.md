# Actual rational Levi principal-open comparisons in exact K0

This internal derived interface composes the actual normalized induction and
exact distribution-character constructions. It uses the canonical rational-point
topology and the literal `SimpleRoot i ν` labels and Levi `levi i ν I` over any
nonarchimedean local field `F`. The field and representation carrier universes
are independent. No restriction on characteristic, splitness or positive rank
is inserted.

The ambient scheme is affine, with the canonical evaluation topology on its
rational points. The displayed ambient hypotheses are local compactness,
nonarchimedeanness, Hausdorffness and a Borel measurable structure. The measure
is a regular Haar measure. A semidirect decomposition has the literal Levi,
an arbitrary actual parabolic subgroup and a closed radical.

`rationalLeviInductionK0Distribution` composes the actual integer-linear
`inductionK0` map with `Character.exactK0DistributionCharacter`. Both maps use
the genuine exact finite-length quotient, including all actual short exact
sequence relations. The input hypotheses are finite-length and finite-length
short-exact preservation by the induction functor and admissibility of every
finite-length ambient representation in carrier universe `max u v`.
`rationalLeviInductionK0Distribution_ofRepresentation` computes its value on
every actual finite-length object. Its value is precisely the genuine
distribution of the normalized induced representation. The proof uses
`inductionK0_ofRepresentation` and the character map's generator formula.

`rationalLeviInductionClass_eq_of_principalOpen` compares two actual
decompositions sharing the same literal Levi. It additionally assumes both
parabolics closed, both Levi projections continuous and both actual left
quotients compact. The exact scheme representative
`Standard.leviScheme i ν (rootSet i ν I)` must be connected reductive. A
specified nonzero polynomial in its actual finite character coordinates and
equality of the two genuine normalized induced distributions on its principal
open are explicit inputs. Both coefficient objects are admissible, and both
original normalized induced objects have explicit finite-length proofs. The
conclusion is equality of their classes in exact finite-length K0.

The implemented proof applies `normalizedInductionClass_eq_of_dense` to the
full actual rational norm family `leviRationalNormCharacters`.
`continuous_leviRationalNormCharacters` discharges every norm-continuity input;
`dense_leviUnramifiedPrincipalOpen` proves the specified locus dense. The generic
comparison extends scalar distribution equality by continuity, evaluates at the
trivial character, removes the trivial twists by genuine induction isomorphisms
and applies exact character injectivity. It assumes no isomorphism between the
two different parabolic inductions. Rank zero is included.

`rationalLeviInductionK0_eq_of_principalOpen` gives equality of the entire two
integer-linear induction maps. It takes actual preservation proofs for both
functors and additionally admissibility of every finite-length coefficient
object of the Levi. For each such object separately, its comparison input
provides a nonzero polynomial and genuine distribution equality on that
polynomial's principal open. The polynomial may depend on the object. The proof
uses `FiniteLengthGrothendieckGroup.hom_ext_object`, computes both maps on an
actual generator by `inductionK0_ofRepresentation`, and applies the preceding
class comparison. Carrier universe `max u v` is closed under induction and may
be instantiated at the larger universe required by the rational Weyl target.

The character map and injectivity depend on the published
`Character.exactK0CharacterRealization` and
`Character.exactK0CharacterInjectivity`. The realization uses
`Character.distributionShortExactAdditivity`; injectivity uses
`Character.finiteFamilyLinearIndependence` and
`SmoothRep.irreducibleGrothendieckStatement`, hence the actual Jordan–Hölder
comparison. These are the declaration-level character-independence dependencies
of this interface. No new Langlands classification, geometric lemma,
adjointness or cuspidal-support theorem is supplied here.

Connected reductivity of the same actual Levi, finite-length admissibility,
the genuine generic comparison and its nonzero polynomial witness remain
inputs. The result does not establish unconditional Weyl conjugacy or the
whole `RationalInducedK0WeylConjugacyStatement`.

The 5 local instances have module-specific names to prevent generated-name
collisions when related modules are imported together. The instance types,
bodies and local scope are unchanged.
