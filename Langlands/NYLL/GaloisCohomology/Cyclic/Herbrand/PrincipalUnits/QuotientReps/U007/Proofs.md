# Representative induction for the integer-unit quotient at a level

`Langlands.NYLL.CyclicCohomology.IntegerUnitsModPrincipalUnitsAtLevel.inductionOn`
proves its published `inductionOnStatement`. For a field `K : Type u` with a
valuative relation, an arbitrary natural level `n`, a Prop-valued motive and a
quotient class `q`, it suffices to prove the motive on every canonical integer-unit
representative. The implicit field and motive and explicit `n`, `q`, `h` binders
retain the source order. No topology or local-field premise is needed.

After unfolding the target, the implemented proof views `q` in the concrete
quotient `𝒪[K]ˣ ⧸ principalUnits K n`, applies Mathlib's
`QuotientGroup.induction_on`, and uses `h` on the resulting representative.
The named projection agrees definitionally with the concrete quotient map.
The only import is the published `QuotientReps.Statements` module and its
published transitive dependencies. There is no unpublished proof dependency.

Source: Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/GaloisCohomology/Cyclic/Herbrand/PrincipalUnits/QuotientReps.lean`,
lines 75–85, unit M146.007. Registered source
`nyll-classfieldtheory-fbd320cd-supplement`, content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The proof follows the original. Worker 517 extracted the unit, prefixed its
namespace with `Langlands.NYLL`, reduced imports and expressed its type through
the independently published proposition. The source `protected` modifier and
original author/copyright header are retained; Apache-2.0 LICENSE and NOTICE
remain in `licenses/NYLL/`.
