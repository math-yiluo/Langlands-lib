# Conditional construction of absolute local invariants

Author: Worker 154.

The definition
`Langlands.ClassFieldTheory.Local.AbsoluteInvariantAssembly.descendedEquiv`
constructs an additive equivalence from the actual absolute degree-two continuous
cohomology of a p-adic field to `RationalModIntegers`, conditional on three
explicit finite-stage hypotheses. The companion theorem
`absoluteInvariantExistence_of_finite_stages` adds three base-change hypotheses
and obtains the simultaneous family and restriction degree law in
`AbsoluteInvariantExistence.{u}`. This is an internal assembly construction,
not an unconditional proof of that proposition or of its remaining inputs.

All primes and arbitrary common universe `u` are retained. Restriction permits
every finite compatible base extension and every specified base-compatible
closure embedding. No Galois hypothesis on the base extension, normality of the
target stage over the source base, or compositum equality is introduced.

## Inputs and published ingredients

The equivalence takes exactly these proposition proofs as arguments:

- `UnramifiedH2Exhaustion.{u}`: every absolute class has an actual finite
  unramified Galois representative under `closureInflation`.
- `ClosureInflationTowerCompatibility.{u}`: inflating through a larger
  compatible finite normal stage does not change its absolute class.
- `UnramifiedInvariantInflationCompatibility.{u}`: the finite arithmetic
  invariant is preserved by the actual relative inflation map.

The restriction construction additionally takes:

- `UnramifiedBaseChangeStageExistence.{u}`: a finite unramified Galois target
  stage contains the prescribed closure image of the source stage.
- `ClosureInflationBaseChangeCompatibility.{u}`: the actual mixed
  finite-to-absolute square commutes for compatible stage embeddings.
- `UnramifiedInvariantBaseChangeCompatibility.{u}`: the finite invariant
  scales by the base degree under relative inflation followed by restriction.

These six hypotheses remain explicit. The imported statement modules define
them but do not supply their proofs. The constructor does not use an assumed
absolute invariant, reciprocity map, or class formation.

The following inputs are supplied by published proofs: arithmetic coordinate
existence from `UnramifiedArithmeticProof`, prescribed positive unramified
degrees from `UnramifiedExtensionDegreeProof`, the canonical inertia criterion
from `Galois.Local.UnramifiedCriterionProof`, and injectivity of actual closure
inflation from `AbsoluteH2InflationProof`. The construction also uses the
published explicit finite invariant and its exact denominator-subgroup range
from `UnramifiedInvariant`, and the actual compositum construction from
`UnramifiedCommonExtension`. In particular, prescribed degrees are not an
additional hypothesis of this module's equivalence or conditional theorem.

## Stages and representative independence

`Stage F` is a finite intermediate field of the existing algebraic closure,
with its Galois certificate and equality of canonical absolute ramification
indices. Its `field` and `padic` abbreviations retain the actual field and the
published `asPadicField` wrapper, whose p-adic scalar map is the composite
through `F`. `Stage.coordinate` chooses an arithmetic Frobenius coordinate
using the published existence proof; `coordinate_arithmetic` records the
corresponding certificate. `Stage.invariant` is the published finite
`unramifiedH2Invariant` for that coordinate.

`Stage.common` uses the actual compositum and the proved canonical inertia
criterion. The two inclusion lemmas are the supremum inclusions.
`Stage.inflate` installs the inclusion algebra and scalar tower, then uses the
actual relative inflation. `inflate_closure` and `inflate_invariant` specialize
the two explicit compatibility hypotheses. `closure_injective` uses the
published absolute inflation exactness theorem, deriving characteristic zero
from the p-adic algebra.

`Value F x q` means that some actual finite unramified representative of `x`
has finite invariant `q`. Exhaustion proves `value_exists`. To prove
`value_unique`, inflate two representatives to their common stage. Tower
compatibility makes their absolute images equal, and injectivity of closure
inflation equates the representatives there. Finite invariant compatibility
then equates their values. The same common-stage argument, now using
additivity of the actual maps, proves `value_add`.

## The additive equivalence

`chosenValue` selects the value supplied by exhaustion. Uniqueness and the
zero representative prove that it is the additive homomorphism `descendedHom`.
`descendedHom_stage` identifies its value on every finite representative.

For injectivity, represent the difference of two absolute classes. Equality
of their descended values makes the finite invariant of that representative
zero. The published finite invariant injectivity makes the representative
zero, and its absolute image is therefore zero.

`exists_denominator` represents a rational class by a rational number `r` and
uses its positive denominator `r.den`. The exact `denominatorEquiv_intCast`
formula together with `Rat.num_div_den` puts the class in that denominator
subgroup. The published prescribed-degree theorem supplies a finite unramified
Galois stage of that degree. Its exact finite invariant range supplies a
preimage of the desired rational class. Inflating it proves surjectivity of
`descendedHom`. `descendedEquiv` packages the resulting bijective additive map.

## Specified embeddings and restriction

`value_restriction` starts from a representative in `L/F` and uses the stage
existence hypothesis to obtain `M/E` containing its specified image. The map
`L → M` is the actual composite `L → Fbar → Ebar`, restricted to `M` by
`RingHom.codRestrict`; it is not a separately chosen embedding. The `F`-algebra
on `M` is the composite through `E`. Equality of the two maps on `F`, proved
from the given closure scalar tower, supplies the `F-L-M` tower. The equality
of the two embeddings of `L` into `Ebar` is definitional for this construction.

The mixed naturality hypothesis now identifies absolute restriction of the
source representative with closure inflation of relative inflation followed
by relative restriction. The finite base-change invariant hypothesis computes
its value as `[E:F]` times the source value. Both finite arithmetic coordinates
are those already chosen for the stages. This proves `value_restriction` for
every specified compatible closure map.

Representative uniqueness over `E` turns that result into
`descendedHom_restriction`. Finally,
`absoluteInvariantExistence_of_finite_stages` takes, simultaneously for every
`F`, the equivalence `descendedEquiv F` and supplies this degree law. The family
depends on the three equivalence inputs and `F`, not on a target extension or
its closure embedding. Thus the conditional theorem has the exact original
conclusion with all its quantifiers, while retaining the six prerequisite
proofs as explicit arguments.

## Provenance and scope

This module assembles the named published constructions and proposition
interfaces. It introduces no new assertion attributed to external literature;
the finite arithmetic and continuous cohomology content belongs to the cited
Library modules and the six explicit hypotheses. No closure-choice comparison
hypothesis is hidden in the construction: the restriction proof works directly
with each specified embedding. It does not separately prove the equality of
restriction maps associated with two such embeddings.

The unconditional `AbsoluteInvariantExistence` theorem remains a separate
obligation: every remaining input must be discharged by actual proofs. Acceptance
of this conditional construction does not complete that proof task.
