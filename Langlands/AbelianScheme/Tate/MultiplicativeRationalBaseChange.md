# Rational multiplicative Tate comparison under actual base change

This internal construction rationalizes the actual multiplicative Tate
base-change comparison, preserving its root coordinates, actual pullback
interpretation, scalar actions and naturality. All declarations are in
`Langlands.GroupScheme.Gm.TateComparison`.

## Inputs and provenance

Let `b : S' ⟶ S` be a morphism of arbitrary schemes in the same universe,
`T : Over S'` a test scheme and `P : ℕ → Prop` a selection of positive
orders. No closure or cofinality condition on `P` is required. The test
scheme `(Over.map b).obj T` has the same underlying scheme and global
section ring as `T`.

The imported `MultiplicativeIntegralBaseChange` constructs a continuous
profinite-integer-linear comparison of the actual selected torsion limits
and identifies it with actual pullback after `(Gm.baseChangeIso b).inv`.
`MultiplicativeRationalAffine` supplies the rational root comparisons and
`RationalBaseChange` supplies rationalization of actual group-scheme
pullback. This file derives new comparisons by scalar extension and tensor
induction. It makes no additional assertion from external literature.

## Rational comparison and actual geometry

`rationalBaseChange b T P` is the rational-linear equivalence

```text
ℚ ⊗[ℤ] Tate.Integral (Gm S').toGrp T P
  ≃ₗ[ℚ]
ℚ ⊗[ℤ] Tate.Integral (Gm S).toGrp ((Over.map b).obj T) P.
```

It applies `LinearEquiv.baseChange` to the integer-linear equivalence
underlying `integralBaseChange b T P`. The pure-tensor formula
`rationalBaseChange_tmul` is `q ⊗ x ↦ q ⊗ integralBaseChange b T P x`.
`rationalBaseChange_toRational` gives compatibility with `x ↦ 1 ⊗ x`.
Both formulas are definitional.

`rationalEquiv_rationalBaseChange` says that the image under the target
rational root comparison is the source root family:

```text
rationalEquiv ((Over.map b).obj T) P (rationalBaseChange b T P x)
  = rationalEquiv T P x.
```

The two root-module targets agree because their global section rings do.
Tensor induction reduces pure tensors to the integral root-coordinate
identity and sums to linearity.

`rationalBaseChange_eq_actual` proves the geometric interpretation

```text
rationalBaseChange b T P x
  = Tate.rationalBaseChange b (Gm S).toGrp T P
      (Tate.rationalMap T P (Gm.baseChangeIso b).inv x).
```

The inverse canonical isomorphism first maps `Gm S'` to the pullback of
`Gm S`; the actual pullback adjunction then compares its sections over
`T` with sections over the composed test scheme. Tensor induction applies
the corresponding integral equality on pure tensors. Thus the constructed
map is a rationalization of actual geometry.

## Full, away and scalar compatibility

Taking `P` constantly true gives the full rational module. Taking
`P := fun n => Nat.Coprime n m` gives the away module for any natural
number `m`, with no primality or nonzero assumption. The theorem
`rationalBaseChange_restrictAway` says that full-to-away restriction
commutes with base change. The pure-tensor case is definitional since
both integral maps read the same coordinates; tensor induction handles
sums.

`rationalBaseChange_scalarAction` intertwines the existing actions of
`ℚ ⊗[ℤ] Global.ProfiniteIntegerRing`. It applies
`TateScalarExtension.map_action` to the profinite-integer-linear integral
comparison. For an explicit hypothesis
`h : Global.RationalProfiniteIntegerAdeleComparison`, the theorem
`rationalBaseChange_finiteAdeleAction` gives the same compatibility over
`Global.FiniteAdeles ℚ`: both actions use the same scalar comparison `h`.
`finiteAdeleBaseChange b T P h` bundles the rational additive equivalence
as linear over that ring, with its two module structures introduced
locally. Its apply theorem identifies it with `rationalBaseChange`.

`rationalBaseChange_awayScalarAction` similarly intertwines the actions
of `ℚ ⊗[ℤ] Global.PrimeToProfiniteIntegerRing m`, using the integral
`awayBaseChange`. For an explicit coupled comparison
`hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m`,
`rationalBaseChange_primeToFiniteAdeleAction` intertwines the actions of
`Global.PrimeToFiniteAdeles m`. The linear equivalence
`primeToFiniteAdeleBaseChange b T hAway` bundles this same map with the
existing away finite-adelic module structures. Its apply theorem again
identifies its function with the selected rational comparison. This file
does not prove either scalar-comparison hypothesis.

## Naturality and affine points

For every morphism `a : T' ⟶ T` of test schemes over `S'`, the theorem
`rationalBaseChange_testRestrict` states

```text
C_(b,T') (Tate.rationalTestRestrict (Gm S').toGrp P a x)
  = Tate.rationalTestRestrict (Gm S).toGrp P ((Over.map b).map a)
      (C_(b,T) x).
```

Its tensor-induction proof uses the actual integral test-restriction
square on pure tensors and linearity on sums.

For any `R : CommRingCat` and `t : Spec R ⟶ S'`, the theorem
`affineRationalEquiv_rationalBaseChange` says that composing the point
with `b` preserves the affine rational root coordinate in
`TateTwist.Divisibility.Rational R P`. On pure tensors its proof uses
`affineIntegralEquiv_integralBaseChange`, which itself uses the canonical
Gamma-Spec isomorphism. Fields and geometric-point fields are valid
specializations; no field hypothesis is required.

## Scope

These are algebraic rational and conditional finite-adelic equivalences.
No topology or continuity on the rational modules, rational prime-adic
comparison, rank, finite étaleness, monodromy pullback, pairing
compatibility or iterated-base-change coherence is asserted here. No
roots, basis or twist trivialization is chosen. Completion of the parent
PEL task is not claimed.
