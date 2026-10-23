# Rational Tate comparison for the multiplicative group

This internal construction identifies the actual selected rational Tate
module of the multiplicative group scheme with the rationalized actual
roots-of-unity limit. It includes the full and away specializations,
compatibility with rationalized residue scalars and full finite-adelic
scalars, and both directions of the full-to-away restriction square.
The namespace is `Langlands.GroupScheme.Gm.TateComparison`.

## Inputs and provenance

Let `S` be an arbitrary scheme, `T : Over S` a test scheme over it, and
`P : ℕ → Prop` an arbitrary selection of positive orders. The source
`Tate.Rational (Gm S).toGrp T P` is the rationalization over `ℤ` of the
actual selected torsion-section limit. The target
`TateTwist.Divisibility.Rational Γ(T.left, ⊤) P` is the rationalization of
the corresponding limit of actual roots of unity in the global-section
ring of `T.left`.

The published `MultiplicativeDivisibility.integralEquiv` identifies these
integral limits by applying the actual torsion-to-roots equivalence at each
order. This file extends that equivalence over `ℤ` to `ℚ` using Mathlib's
`LinearEquiv.baseChange`. The scalar laws use the published
`TateScalarExtension.map_action` and the actual scalar actions of
`RationalScalars` and `TwistRationalScalars`. These are internal consequences
of the published constructions, with no additional literature assertion.

No closure, nonemptiness or cofinality hypothesis on `P` is needed.
There is no characteristic, invertibility, finite-étaleness, rank or
finiteness assumption on `S`, `T` or their torsion sections.

## Rational equivalence

`rationalEquiv T P` is the rational-linear equivalence

```text
ℚ ⊗[ℤ] Tate.Integral (Gm S).toGrp T P
  ≃ₗ[ℚ]
ℚ ⊗[ℤ] TateTwist.Divisibility.Integral Γ(T.left, ⊤) P.
```

The integer-linear equivalence underlying `integralEquiv T P` is extended
to `ℚ`. The forward pure-tensor formula is
`q ⊗ x ↦ q ⊗ integralEquiv T P x`; the inverse uses
`(integralEquiv T P).symm`. Both formulas are definitional.
`rationalEquiv_toRational` expresses compatibility with the canonical
integral-to-rational maps `x ↦ 1 ⊗ x`; it is also definitional.

## Scalar compatibility

`rationalEquiv_scalarAction` says that this equivalence intertwines the
two existing actions of `ℚ ⊗[ℤ] Global.ProfiniteIntegerRing`.
It is `TateScalarExtension.map_action` applied to the actual
profinite-integer-linear integral comparison. Thus both source and target
actions come from their existing coordinatewise residue actions.

For an explicit hypothesis
`h : Global.RationalProfiniteIntegerAdeleComparison`,
`rationalEquiv_finiteAdeleAction` gives compatibility with the two
finite-adelic actions. Both use the inverse of the same rational scalar
comparison selected by `h`, so the assertion follows from the preceding
rationalized residue compatibility. This file does not prove `h`.

`finiteAdeleEquiv T P h` bundles the same additive equivalence as linear
over `Global.FiniteAdeles ℚ`, using the source and target module definitions
locally. Its apply theorem identifies it with `rationalEquiv T P`.
Its inverse and bijectivity are inherited from the rational equivalence.
In particular, taking `P` constantly true gives the full finite-adelic
comparison; the general definition also applies to an away selection.

## Full and away specializations

`fullRationalEquiv T` uses `P := fun _ => True`.
For an arbitrary natural number `m`, `awayRationalEquiv T m` uses
`P := fun n => Nat.Coprime n m`. There is no primality or nonzero
assumption on `m`.

`awayRationalEquiv_scalarAction` proves compatibility with
`ℚ ⊗[ℤ] Global.PrimeToProfiniteIntegerRing m`. Its proof applies
`TateScalarExtension.map_action` to the integral `awayEquiv T m`.
That integral map has the same underlying additive equivalence as the
selected comparison, so its rationalization is the displayed
`awayRationalEquiv`.

`awayRationalEquiv_restrictAway` states that the comparison after the
actual full-to-away rational restriction equals the roots-of-unity
restriction after the full comparison. `awayRationalEquiv_symm_restrictAway`
proves the corresponding square for the inverse equivalence.
Both proofs use tensor induction: the pure-tensor case is definitional,
because the integral restriction and comparison read the same coordinates;
zero and addition follow from linearity.

## Scope

These are algebraic rational equivalences. This file does not assert a
rational topology or continuity, prove the scalar-comparison hypothesis,
bundle a linear equivalence over the away finite adeles, construct
test-scheme base change or geometric monodromy, prove torsion rank or
finite étaleness, trivialize a twist, or construct a Weil pairing.
The parent abelian-scheme and PEL level-structure task remains incomplete.
