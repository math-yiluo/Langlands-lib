# Base change of actual rational Tate modules

For a scheme morphism `b : S' ⟶ S`, a commutative group scheme `G` over
`S`, a test scheme `T` over `S'`, and a predicate `P` on positive torsion
orders, this module constructs

```text
Rational (b*G) T P ≃ₗ[ℚ] Rational G (T → S' → S) P.
```

It rationalizes the actual integral pullback comparison, preserving the
existing full and away residue actions. With the explicit scalar-comparison
hypotheses already used by the Library, it is a linear equivalence over
the full finite-adeles, or over the finite-adeles away from a natural
modulus. It also proves naturality and specializes to bundled abelian
schemes and field-valued points.

## Provenance

This is a derived construction from `Tate.IntegralBaseChange`,
`Tate.Rational`, `Tate.RationalScalars`, `Tate.AwayRationalScalars`, and
`Tate.RationalTestScheme`. The integral comparison is constructed from
actual pullback-adjunction maps on torsion points. Here
`LinearEquiv.baseChange` extends that equivalence from integers to
rationals; no caller-supplied module comparison is introduced.

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), printed p.18 / PDF p.26, defines the rational full
and away Tate modules by rationalizing their integral limits.
Section III.1, printed p.91 / PDF p.99, uses the rational Tate module at
a geometric point in the pointed PEL problem. These passages motivate
the conventions and intended application; the elementary comparison
here has the weaker hypotheses stated below. Registered source:
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The tensor factor order is the Library convention
`ℚ ⊗[ℤ] Integral`; the existing `rationalTensorComm` compares it with
the source's opposite order.

## Construction and scalar compatibility

In namespace `Langlands.GroupScheme.Tate`, `rationalBaseChange` is
the scalar extension of `integralBaseChange.toIntLinearEquiv`.
Its source is the rational Tate module of the actual pullback group
scheme, and its target uses the composite structure morphism of `T`.
The forward and inverse pure-tensor formulas are
`rationalBaseChange_tmul` and `rationalBaseChange_symm_tmul`. The map
acts on the integral factor and leaves the rational factor unchanged.
`rationalBaseChange_toRational` is the same formula with rational factor
one. The equivalence's inverse laws come from scalar extension of the
integral equivalence.

`rationalBaseChange_restrictAway` states that retaining only orders
coprime to `m` commutes with rational base change. Tensor induction
reduces it to the integral restriction square; the pure-tensor case
is definitional, and additivity treats sums.

`rationalBaseChange_scalarAction` applies the existing
`TateScalarExtension.map_action` to the full residue-linear integral
comparison. Thus the map preserves the action of
`ℚ ⊗[ℤ] ProfiniteIntegerRing`. Substitution of the inverse of the chosen
scalar comparison proves `rationalBaseChange_finiteAdeleAction`.
`finiteAdeleBaseChange` bundles the resulting finite-adelic linear
equivalence; its application lemma identifies its underlying map.
The same explicit `h : RationalProfiniteIntegerAdeleComparison`
defines both endpoint module structures.

For the away system, `rationalBaseChange_awayScalarAction` applies
the same argument to `awayBaseChangeLinearEquiv`, using
`ℚ ⊗[ℤ] PrimeToProfiniteIntegerRing m`.
`rationalBaseChange_primeToFiniteAdeleAction` and
`primeToFiniteAdeleBaseChange` transport this compatibility along the
same `hAway : PrimeToRationalProfiniteIntegerAdeleComparison h m`
at both endpoints. This is the existing coupled full/away comparison;
the construction does not assume independently chosen, unrelated
scalar identifications.

## Naturality and abelian schemes

`rationalBaseChange_testRestrict` compares restriction along
`a : T' ⟶ T` over `S'` with restriction along `(Over.map b).map a`
over `S`. `rationalBaseChange_map` compares the pullback of an actual
group-scheme homomorphism `f : G ⟶ H` with `f` over the original base.
Both proofs use tensor induction and the corresponding integral
naturality equations on pure tensors.

In namespace `Langlands.AbelianScheme.Tate`, `rationalBaseChange`,
`finiteAdeleBaseChange`, and `primeToFiniteAdeleBaseChange` specialize
the generic equivalences to the actual bundled abelian-scheme pullback.
`rationalBaseChange_map` specializes the homomorphism square.

For a field-valued point `t : Spec Ω ⟶ S'`,
`rationalFullBaseChangeAt` and `rationalAwayBaseChangeAt` compare the
rational Tate module of the pullback at `t` with that of the original
abelian scheme at `t ≫ b`. The field is the same on both sides.
Taking an algebraically closed field gives the geometric-point
application. The adelic versions are obtained by taking `T = Over.mk t`
in the corresponding bundled equivalences.

## Scope

All schemes and the pointed coefficient field lie in the same universe.
No connectedness, local noetherianity, algebraic closure, finiteness,
étaleness, or invertibility of torsion orders is needed for the underlying
comparison. Full finite-adelic linearity retains `h`; away finite-adelic
linearity retains both `h` and its coupled `hAway`. Independence from
those scalar-comparison witnesses is not asserted.

This unit makes no rational topology claim. It does not construct the
base-change functor on rational homomorphisms, prove naturality for
`Hom⁰` or endomorphism tensor-algebra actions, or prove identity and
composition coherence in the base morphism. Fundamental-group
compatibility, Weil forms, and invariant PEL level base change remain
separate obligations.
