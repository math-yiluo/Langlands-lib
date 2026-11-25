# Global invariant conditions on actual cohomology classes

This module defines a class-level form of the published
`Langlands.ClassFieldTheory.Global.GlobalInvariantStatement` and proves that it is
equivalent to the original statement. It constructs no invariant family and
proves no arithmetic existence assertion. The original target and all of its
imported Lean/Markdown pairs are unchanged.

## Definitions

All number fields and completion fields retain the arbitrary common universe
`Type u`. The maps `inv : FundamentalClass.GlobalInvariantMaps.{u}` and the
abstract local families `I : ∀ p [Fact p.Prime], InvariantFamily.{u,u} p` are
exactly those of `InvariantStatement`. The invariant codomain is the published
`RationalModIntegers`. No topology, coefficient action, or cohomology carrier is
replaced.

The three new compatibility predicates lie in `FundamentalClass`:

- `InvariantRestrictionOnClasses inv` asserts that applying `inv F' E` after
  actual `relativeIdeleClassRestriction F F' E 2` multiplies `inv F E` by
  `[F' : F]`, on every cohomology class. Only the top extension `E/F` must be
  Galois; the required instance for `E/F'` is deduced by the published tower theorem.
- `InvariantInflationOnClasses inv` asserts that applying `inv F L` after
  actual `relativeIdeleClassInflation F E L 2` gives `inv F E`, on every class.
  Both `E/F` and `L/F` are Galois, with the specified compatible algebra towers.
- `InvariantLocalOnClasses I inv` asserts, for every pair of local and global
  classes `a,b`, that `localIdeleClassMap v w 2 a = decompositionRestriction v w 2 b`
  if and only if `([E:F] / [E_w:F_v]) • inv F E b` equals the local invariant of
  `a`. The quotient is the same natural-number division as in the original
  statement. The finite places, LiesOver condition, completed Galois extension,
  and supplied local invariant maps retain their original binders. Finiteness
  is supplied by `FiniteExtension.local_finite`.

`IsGlobalInvariantOnClasses I inv` combines the unchanged `InvariantImages`
with these three predicates. `GlobalInvariantClassStatement` quantifies over
every `I` satisfying `RelativeClassFormation` and `ArithmeticNormalization`,
and asserts existence of such maps. It is an equivalent arithmetic obligation,
not a discharged hypothesis.

## Implemented equivalence proof

`invariantRestriction_iff_classes` assumes `InvariantImages inv`. Starting with
the cochain formulation, it chooses a normalized representative of an arbitrary
class and a representative of its actual restriction, then applies the existing
cochain bridge. In the reverse direction, it translates the cochain relation
back to equality of classes. One implication applies the class formula; the
other uses injectivity of `inv F' E`. The image equality itself is not needed
for this argument.

`invariantInflation_iff_classes` also assumes `InvariantImages inv`. Its forward
direction chooses representatives and uses the original condition at exponent
one. Its reverse direction uses additivity of `inv F L` and its injectivity to
recover the cochain equivalence at every natural exponent, including zero.

`invariantLocal_iff_classes` requires no image hypothesis. It uses Mathlib's
`H2_induction_on` to choose a local cocycle representative and the published
surjectivity of `RelativeIdeleCocycle.cohomologyClass` for the global class. The
published `localIdeleClassMap_eq_decompositionRestriction_iff` supplies exactly
the cochain relation in both directions. No decomposition-field isomorphism or
new local invariant theorem is assumed.

`isGlobalInvariant_iff_classes` assembles these equivalences using the common
image conjunct. `globalInvariantStatement_iff_classes` transports the existential
witness while retaining the same universally quantified abstract local family
and its hypotheses. It has no extra hypotheses.

## Provenance and checks

Derived from the unchanged published pairs `InvariantStatement` and
`CohomologyMaps`. The mathematical assertion is the existing target expressed
through the existing maps; the implemented equivalence proves that this
reformulation neither strengthens nor weakens it. The cochain bridges used here
are imported published theorems.

With Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`, development inspection checked the
complete, unapplied declarations:

```lean
Langlands.ClassFieldTheory.Global.GlobalInvariantClassStatement.{u} : Prop
Langlands.ClassFieldTheory.Global.globalInvariantStatement_iff_classes.{u} :
  Langlands.ClassFieldTheory.Global.GlobalInvariantStatement.{u} ↔
    Langlands.ClassFieldTheory.Global.GlobalInvariantClassStatement.{u}
```

Statement inspection reports a Prop-valued
definition with the sole universe parameter `u`. The final module/theorem check
reports zero errors, zero warnings, theorem
kind and the sole universe parameter `u`. Both inspections report only
`propext`, `Classical.choice`, and `Quot.sound`. These checks are development
evidence.
