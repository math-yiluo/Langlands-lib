# Polarized actions on a supplied rationally isogenous model

Author: Worker 344.

This is an internal construction from the published rationalization, actual
integral dual pullback, and polarized-action interfaces. It is not a translation
of an external existence theorem. Its purpose is to retain an exact supplied
rational isomorphism while equipping its source model with a compatible actual
polarization. This exactness is needed when the rational isomorphism has already
been chosen to realize a prescribed full integral Tate image.

## Inputs and output

Let `P : Prerequisites.{u}` provide the existing geometric and tensor-coherence
statements, let `S : Scheme.{u}` be quasi-separated, and let `R : Type v` be a
ring, rational algebra and star ring. The original input `X` is the published
`PolarizedAction`: an actual abelian scheme `A`, a faithful rational algebra
action `alpha : R →ₐ[ℚ] End0 A`, an actual geometric polarization `lambdaA`,
its dual witnesses, and the full involution equation.

The construction takes an actual abelian scheme `B` over the same `S` and an
exact supplied isomorphism

```text
e : Rationalization.of B ≅ Rationalization.of A.
```

It additionally takes `W : DualWitness B`, providing the actual dual scheme,
dual geometry and inverse Poincare evaluation data for `B`. For the polarization
proof and the resulting model it takes a structure morphism
`p : S ⟶ Spec K`, with `K : Type u` a characteristic-zero field. No connectedness,
local noetherianity, number-field, division, CM, rank or Tate-image hypothesis is
used.

`PolarizedAction.isogenyModel` is a polarized action on this same `B`.
`PolarizedAction.isogenyModelIso` is an isomorphism of rational algebra actions
from `X` to that model. Its underlying rational homomorphism is exactly `e.inv`,
and its inverse is exactly `e.hom`. The supplied isomorphism is never rescaled.

## Conjugated action and exact comparison

`PolarizedAction.isogenyAction` defines the action on `B` by

```text
beta(r) = e.hom ≫ alpha(r) ≫ e.inv.
```

The one, multiplication, zero, addition and rational-scalar laws follow from
the corresponding laws of `alpha`, distributivity of categorical composition,
and the inverse identities of `e`. Multiplication uses the existing
endomorphism-ring convention: the product of endomorphisms is their composition
in reversed categorical order.

`PolarizedAction.isogenyActionIso` lifts `e` to an isomorphism of rational
algebra actions from `(B,beta)` to `X`. Its intertwining proof cancels
`e.inv ≫ e.hom`. The `_hom` and `_inv` theorems identify both underlying maps
by reflexivity. The faithful-action field of the final model follows from the
published injectivity equivalence for an isomorphism of rational algebra actions
and `X.faithful`.

## Integral representatives and actual polarization

Let `c := Rationalization.integralIsoData e`. This is the published choice of
integral representatives of the exact rational isomorphism, with nonzero
integer denominators `c.homDenom` and `c.invDenom` and exact integral
inverse-multiple identities. `PolarizedAction.isogenyIntegralData` rescales
these representatives, using `c.rescale c.homDenom c.invDenom`. Write the result
as `d`. Then

```text
d.homDenom = c.homDenom * c.homDenom,
d.invDenom = c.invDenom * c.invDenom,
ofHom d.hom = d.homDenom • e.hom,
ofHom d.inv = d.invDenom • e.inv.
```

Only the integral representatives and their denominators change. The input
`e` remains the very same rational isomorphism. Both exact integral composition
identities have common multiplier

```text
N = d.homDenom * d.invDenom.
```

`PolarizedAction.isogenyInverseData` bundles these maps as the existing
`IntegralInverseData B A`. `isogenyInverseData_pos` proves `0 < N` as a product
of two positive squares. `isogenyInverseData_unit` uses `p`: the nonzero integer
`N` is a unit in `K`, and hence maps to a unit in the global sections of `S`.

`PolarizedAction.isogenyModelPolarization` is the actual integral dual pullback
of `X.polarization` along `d.hom : B ⟶ A`. Thus it is an actual morphism
`B ⟶ W.dual P`, formed using the constructed dual homomorphism, rather than
an abstract pairing or merely a rational dual-valued morphism.

`isogenyModelPolarization_isPolarization` applies the published
`integralInverseData_finiteEtaleIsogenies` and
`dualIntegralInverseData_finiteEtaleIsogenies` to the same exact integral data,
positive `N`, and its global unit proof. Consequently the selected map and
its actual dual are finite etale isogenies. The published actual-polarization
pullback theorem then proves that the displayed integral pullback is a
geometric polarization in the original `IsPolarization` sense.

## Full involution equation

The model uses the relative-dual additivity proof supplied by
`relativeDualSchemeMapAdditivity`. The same construction supplies all ordered
pairs of additivity proofs needed in this module.

To prove the model's full `IsInvolutionCompatible` field, the Lean proof first
identifies rationalization of the integral dual pullback with rational dual
pullback. It applies the published involution-transport theorem. One premise is
exactly `X.involutionCompatible`; the other is intertwining by `homToHom0 d.hom`.
The latter follows by multiplying the exact intertwining equation for `e.hom`
by `d.homDenom`, using `d.ofHom_hom` and linearity of rational composition.
This proves the equation for every element of `R`, including its original star
operation.

## Exact positive multiplier

Set

```text
q = (d.homDenom : ℚ)^2.
```

`isogenyModelMultiple_pos` proves `0 < q` from the nonzero denominator. The
`Units.mk0` in `isogenyModelMultiple` gives this very rational number as a
rational unit. That theorem accepts the published `PairAdditivity` argument
required by `Multiple` and proves `Multiple X Y q isogenyModelIso`, where
`Y := isogenyModel`. Explicitly, the rational dual pullback of `lambdaB` along
`e.inv : A → B` is exactly `q • lambdaA`.

The implemented proof uses
`integralDualPullbackHom_rationalization` to write rationalization of `lambdaB`
as `q` times rational dual pullback of `lambdaA` along `e.hom`. Rational dual
pullback is linear in the dual-valued morphism. The published inverse-pullback
identity cancels the successive pullbacks by `e.hom` and `e.inv`, leaving
`q • lambdaA`. The final `pow_two` rewrite identifies the displayed square.
The `_hom` and `_inv` formulas for `isogenyModelIso` are reflexive and record that
this multiplier holds for the unchanged input inverse.

## Scope and remaining work

The construction assumes `B`, `e` and `W`. It proves neither their existence nor
any integral order action on `B`, determinant condition, relative dimension
identity, full integral Tate-image equality, normalized level existence,
representability, smoothness or projectivity. It supplies the actual compatible
polarization and precise rational multiplier needed to use a separately
constructed exact model comparison in the published Weil level transport.
The host division CM representability proposition remains a separate obligation.
