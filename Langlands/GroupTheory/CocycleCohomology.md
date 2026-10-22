# Normalized multiplicative cocycles and actual group cohomology

This module compares the published `Langlands.NormalizedTwoCocycle G A`
with Mathlib's actual second group cohomology. Here `G` is a group, `A` is
an abelian multiplicative group, and `MulDistribMulAction G A` is the given
action. Both carriers inhabit `Type u`, as required by the cohomology API.
All declarations are in `Langlands.NormalizedTwoCocycle` unless indicated.

## Coefficients and differential conventions

`CoefficientScalars` is `ULift.{u} ℤ`, with the explicit ring equivalence
`coefficientScalarsEquiv` to `ℤ`. This lift satisfies Mathlib's category
universe requirements; it does not change the group or coefficient carrier.
`coefficientRepresentation G A` has carrier `Additive A` and is the integral
representation induced by the original multiplicative action. It restricts
the integer-linear action to the lifted integer scalars. Its identity and
composition laws are the original representation laws. The theorem
`coefficientRepresentation_apply` identifies its action exactly with
`Additive.ofMul (g • a.toMul)`.

The theorems `differential₁₂` and `differential₂₃` are definitional equalities
with Mathlib's inhomogeneous differentials. In multiplicative notation they
are respectively

- `δb(g,h) = (g • b(h)) / b(g*h) * b(g)`;
- `δf(g,h,j) = (g • f(h,j)) / f(g*h,j) * f(g,h*j) / f(g,h)`.

Consequently `mem_cocycles₂_iff` identifies membership in the actual additive
cocycle submodule with Mathlib's `IsMulCocycle₂`, namely
`f(g*h,j) * f(g,h) = (g • f(h,j)) * f(g,h*j)`.
`toCocycle₂` sends a normalized multiplicative cocycle to this submodule by
`Additive.ofMul`. `cohomologyClass` applies Mathlib's `H2π` to it. The target
is `groupCohomology (coefficientRepresentation G A) 2`, rather than a newly
defined quotient or an assumed class group.

## Normalization and surjectivity

For an actual additive cocycle `f`, `normalizedRepresentative` subtracts the
boundary of the constant one-cochain with value `f(1,1)`, and then reads the
result multiplicatively. Closure of the cocycle submodule under subtraction
and Mathlib's `d₁₂_apply_mem_cocycles₂` prove that the result is a cocycle.
Its value at `(1,1)` is zero additively because the identity acts trivially;
this is the multiplicative normalization value one. The published
`NormalizedTwoCocycle.one_left` and `one_right` then give normalization on
both axes. `normalizedRepresentative_apply` proves the explicit formula

`normalizedRepresentative(f)(g,h) = f(g,h).toMul / (g • f(1,1).toMul)`.

`cohomologyClass_normalizedRepresentative` uses the linearity of `H2π`
and `H2π_eq_zero_iff`: the subtracted cocycle is a boundary and therefore
has zero class. Finally `cohomologyClass_surjective` uses Mathlib's
`H2_induction_on` to choose an actual additive representative and then
normalizes it by this construction. No desired class or existence theorem
is included as an input assumption.

## Explicit cochains and existing extension maps

`cohomologyClass_eq_of_cochain` assumes the explicit equation

`c(g,h) * b(g*h) = b(g) * (g • b(h)) * d(g,h)`

for normalized cocycles `c,d`. It proves equality of their classes by
`H2π_eq_iff`, with range witness `Additive.ofMul ∘ b` for the differential.
The pointwise boundary identity follows by multiplication and cancellation
in the commutative coefficient group. The theorem does not require a separate
`b(1)=1` hypothesis, so in particular applies to normalized cochains.
`MapData.cohomologyClass_eq` specializes this result to the published
`MapData` with identity coefficient and group homomorphisms. The extension
maps themselves remain those in `Langlands.GroupTheory.CocycleMap`.

## Provenance and scope

The cocycle and cochain conventions are from Artin and Tate, *Class Field
Theory* (2009), Chapter XIII section 1, printed pp.127–129 (PDF pp.136–138),
registered as `artin-tate-2009-class-field-theory`, SHA256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
In particular the cochain equation is their p.129 equation (*) multiplied
by `b(g*h)`, using commutativity of the coefficients. The representation
packaging, universe lift, normalization calculation and comparison proofs
are derived constructions implemented directly in Mathlib's cochain complex.
They do not assert an arithmetic invariant, a fundamental-class theorem,
or a continuous cohomology comparison.
