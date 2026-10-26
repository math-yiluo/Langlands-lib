# Existence of the global invariant maps on idele-class cohomology

Author: Worker 21.

The theorem `Langlands.ClassField.Global.globalInvariantStatement` proves the
published `Langlands.ClassField.Global.GlobalInvariantStatement` in an arbitrary
universe `u`. It has no additional hypotheses. For every local family
`I : ∀ p [Fact p.Prime], InvariantFamily.{u,u} p` satisfying
`RelativeClassFormation` and `ArithmeticNormalization` at every prime, it
constructs additive invariant maps on the actual
`relativeIdeleClassCohomology F E 2 = H²(Gal(E/F), C_E)`.
These maps are injective with image `denominatorSubgroup [E:F]` and satisfy
the exact restriction, inflation and finite-place local cochain equivalences
of `FundamentalClass.IsGlobalInvariant`.

The statement pair and all its imported pairs are unchanged. The proof uses
the actual idele class groups, their published Galois actions and cohomology.
The local family remains arbitrary under the statement's two laws.

## Published inputs

The proof imports and supplies the following closed theorems:

- `ideleClassH1Vanishing.{u}`:
  `FundamentalClass.IdeleClassH1Vanishing.{u}`.
- `ideleClassGaloisDescent.{u,u}`:
  `IdeleClassGaloisDescent.{u,u}`.
- `ideleClassH2OrderBound.{u,u}`:
  `IdeleClassH2OrderBound.{u,u}`.
- `Langlands.Global.cyclicPrimePowerLocalDegreeStatement.{u,u}`:
  `Langlands.Global.CyclicPrimePowerLocalDegreeStatement.{u,u}`.
- `globalInvariantLocalFromTotalStatement.{u}`:
  `GlobalInvariantLocalFromTotalStatement.{u}`.

Descent, the order bound and the local-degree theorem allow independent field
universes in their full declarations. This proof specializes both to the
common universe required by `GlobalInvariantStatement`.

## Implemented proof

Fix `I` and its class-formation and normalization proofs `hCF`. The proof
extracts `RelativeImages`, `InflationCompatibility` and
`RelativeRestriction` from the class-formation conjunct. Define
`s := totalIdeleInvariantMaps I hImages`, the published sum of the finite
local invariants and canonical archimedean invariants on actual idele H².

Four published results establish the inputs needed for the regular-class
construction:

- `totalIdeleInvariantMaps_killsQuotientKernel_of_h1` gives
  `s.KillsQuotientKernel` from H¹ vanishing and `hCF`. This is where the
  supplied arithmetic normalization enters through the published reciprocity
  argument.
- `totalIdeleInvariantMaps_inflation_of_inflationCompatibility` gives
  `s.InflationCompatible`.
- `totalIdeleInvariantMaps_restriction_of_localLaws` gives
  `s.RestrictionCompatible` from the local restriction and inflation laws.
- `totalIdeleInvariantMaps_cyclicRange` gives `s.CyclicRange` from the
  published cyclic prime-power local-degree theorem.

Apply `assembledIdeleClassInvariantMaps` to `s`, these four laws, Galois
descent, H¹ vanishing and the H² order bound. The resulting `inv` is defined
on every idele-class H² group. Its published `_images`, `_restriction` and
`_inflation` theorems give `InvariantImages inv`,
`InvariantRestrictionOnClasses inv` and `InvariantInflationOnClasses inv`.

The imported assembly first defines invariants on regular classes: classes
whose inflation to some finite Galois overfield is an idele quotient image.
Cyclic range, the auxiliary cyclic tower and inflation–restriction exactness
give full denominator range on that subgroup. The finite H² order bound
then makes the regular subgroup the whole group and proves injectivity.
Thus this use of the assembly does not require surjectivity of the
idele-to-class H² map for a general extension.

For local compatibility, the proof establishes the entire quantified
`InvariantTotalAgreement I hImages inv`. For arbitrary finite and infinite
place choices `wf` and `wi`, and an idele cohomology class `a`,
`assembledIdeleClassInvariantMaps_apply_quotient` identifies the invariant of
its quotient image with `s F E a`.
`totalIdeleInvariantMaps_eq_of_inflationCompatibility` then identifies this
fixed-choice sum with `totalIdeleInvariant I hImages wf wi a`. The equality
is evaluated at `a` using `DFunLike.congr_fun`.

The published `globalInvariantLocalFromTotalStatement` now supplies
`InvariantLocalOnClasses I inv` from the image law, restriction law and
agreement for all choices. Finally `isGlobalInvariant_iff_classes`
translates the four class-level laws into precisely the cochain equivalences
of the target statement. The existential witness is `inv`.

## Provenance

This module is an internal composition of the published constructions and
proofs named above. Its mathematical construction follows E. Artin and
J. Tate, *Class Field Theory* (2009), registered as
`artin-tate-2009-class-field-theory`, SHA256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`:
Chapter VII §3, printed pp.42–50 (PDF pp.51–59). The source defines the
sum of local invariants, proves its tower laws and reciprocity, defines
the invariant of a regular idele class on pp.47–48, and proves restriction
and the passage from cyclic extensions to all finite normal extensions
on pp.49–50, culminating in Theorem 7. The cited source's warning on p.47
that the idele quotient map on H² need not be onto is respected here.

The formal proof reuses the published general H² order bound in the
cardinality step. The finite-place cochain formulation is obtained through
the published local-compatibility theorem and cochain/class equivalence;
it is the exact derived formulation documented in `InvariantStatement.md`,
rather than a new statement taken verbatim from the source.

## Complete declaration and axiom checks

The complete unapplied exported type, with universes displayed, is

```lean
Langlands.ClassField.Global.globalInvariantStatement.{u} :
  Langlands.ClassField.Global.GlobalInvariantStatement.{u}
```

The only universe parameter is `u`; there are no parameters outside the
published proposition. A private diagnostic module checks the unapplied
term directly at an arbitrary universe, prints its full type and runs
`#print axioms`. The allowed axioms are exactly `propext`,
`Classical.choice` and `Quot.sound`.

The same module checks the complete unapplied H² input type

```lean
Langlands.ClassField.Global.ideleClassH2OrderBound.{u,v} :
  Langlands.ClassField.Global.IdeleClassH2OrderBound.{u,v}
```

with independent arbitrary universes `u` and `v`, by direct unapplied
assignment, and prints the same three standard axioms.

Development compilation and declaration inspection succeeded with zero errors
and warnings in check `db85bc6e-666c-4cf7-b83b-4dd58b2a0030`.
The complete-type and axiom output agrees with both displays above. This
development check is separate from exact-target validation and independent
semantic review of the submitted proof.
