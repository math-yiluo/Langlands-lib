# Compatible coefficient-linear residual actions on original tensors

Worker 185 authored this construction. Its namespace is
`Langlands.Algebra.NonUnitalBimoduleTensorScalars`.
It refines the published original residual action to a nonunital
coefficient-algebra homomorphism and compares the two actual coefficient
Module structures on the same tensor. The sufficient compatibility hypothesis
on the first factor is explicit.

## Provenance and scope

The governing registered original is David Renard, *Représentations des
groupes réductifs p-adiques*, French edition dated 9 July 2026,
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The Chapter I conventions preceding I.1.1, printed pp.5–6 / PDF11–12, give
the original nonunital ring/module and commuting bimodule conventions.
I.2.1, printed p.14 / PDF20, recovers
coefficient scalars on nondegenerate modules. I.2.2–I.2.3, printed pp.15–18 /
PDF21–24, supplies tensors and the additive F/P constructions.
I.4.2, printed p.24 / PDF30, motivates subsequent coefficient-linear duality
comparisons.

The registered supplement `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was checked on PDF1–2. Its adjunction-direction and corner-tensor corrections
do not change the elementary construction here. The 2026 edition governs.

This is derived internal infrastructure over a commutative coefficient ring.
It uses the published original additive tensor and residual action, and the
published recovered and tensor coefficients. Its extra compatibility input
is a sufficient condition for the adapter constructed here; the commuting
original actions alone are not asserted to imply that condition.
The full-source coefficient-convention audit, arbitrary-input comparisons,
F/P duality, categorical natural isomorphisms, tensor inverses and equivalences
remain separate obligations. This construction does not settle them.

## Exact structures and hypotheses

The coefficient ring `k : Type uk`, acting ring `S : Type uS`, balancing
ring `R : Type uR`, and factors `X : Type uX`, `Y : Type uY` have independent
universes. The tensor is exactly
`T = NonUnitalModuleTensor.Tensor R X Y`, in `Type (max uX uY)`,
with its inherited additive group. Its original actions on the factors are
`NonUnitalModule S X`, `NonUnitalModule Rᵐᵒᵖ X`, and
`NonUnitalModule R Y`. The hypothesis `hX : ActionsCommute S R X` says that
the first two original actions commute.

`k` is a commutative ring. `R` is a nonunital ring with the specified
`Module k R`, `IsScalarTower k R R`, and `SMulCommClass k R R`.
The hypotheses `hR : IsIdempotented R` and `hY : IsNondegenerate R Y`
give the exact published tensor coefficients
`MT = NondegenerateTensorScalars.module k R X Y hR hY`.
The original residual action is exactly
`HS = NonUnitalBimoduleTensor.leftModule hX Y`.
Both are named structures, installed explicitly where used.
There is no prior coefficient Module input on either factor or on the tensor.

For `hRX : IsNondegenerate Rᵐᵒᵖ X`, the exact factor coefficients are

* `MX = NondegenerateScalars.module k hR.op hRX`, definitionally the published
  `NondegenerateTensorScalars.rightModule k hR hRX`;
* `MY = NondegenerateScalars.module k hR hY`, definitionally the published
  `NondegenerateTensorScalars.leftModule k hR hY`.

When `S` has the specified `Module k S`, the proposition
`InputCompatible k hR hRX` is `IsScalarTower k S X` with exactly `MX`
installed and with the original S-action. `inputCompatible_iff` identifies it
with the explicit equation
`(c • s) • x = c • (s • x)` for every `c`, `s`, `x`, again using `MX`.
This law is separate from `hX`.

## The actual linear endomorphisms

`linearEnd k hR hX Y hY s` is exactly
`NondegenerateTensorScalars.linearMap k R hR hY hY
  (hX.leftActionHom s) (NonUnitalModuleHom.id R Y)`,
using `MT` in domain and codomain. `linearEnd_eq` is equality of the whole
linear maps. This part needs neither `hRX` nor `InputCompatible`, nor
coefficient structures on S.

`linearEnd_toAddMonoidHom` identifies the entire underlying additive map with
`NonUnitalBimoduleTensor.leftScalar hX Y s`.
`linearEnd_toAddMonoidHom_eq_map` identifies it with exactly
`NonUnitalModuleTensor.map R (hX.leftActionHom s)
  (NonUnitalModuleHom.id R Y)`.
`linearEnd_tmul` gives its value
`tmul R X Y (s • x) y` on `tmul R X Y x y`.
`linearEnd_apply` identifies its value with `s • t` on every tensor using
exactly `HS`. These identities are definitional consequences of the
published map construction.

`action_smul` proves `s • (c • t) = c • (s • t)` from this linear map's
`map_smul` law. `smulCommClass` packages the corresponding
`SMulCommClass k S T`, with exactly `MT` and `HS`. This coefficient
commutation needs no extra input compatibility.

## Linearity in S and the bundled action

With `hRX` and `hcompat : InputCompatible k hR hRX`,
`scalar_action` proves `(c • s) • t = c • (s • t)` for every tensor.
Its implemented proof compares two whole additive endomorphisms using
`NonUnitalModuleTensor.hom_ext`. On `x ⊗ y` the first becomes
`((c • s) • x) ⊗ y`. The input scalar-tower law on exactly `MX` rewrites it
as `(c • (s • x)) ⊗ y`. The published
`NondegenerateTensorScalars.smul_tmul_left` identifies this with
`c • ((s • x) ⊗ y)` under exactly `MT`.
Equality of the additive maps then gives the equation on all tensors.
`isScalarTower` bundles this derived law relative to exactly `MT` and `HS`.

`action k hR hX Y hY hRX hcompat` installs these two derived output laws
and applies `NonUnitalModule.toLinearEndHom k`. Its type is the actual
nonunital coefficient-algebra homomorphism `S →ₙₐ[k] Module.End k T`.
No replacement action is introduced. `action_apply_eq_linearEnd` identifies
the entire per-s linear endomorphism, by linear-map extensionality;
`action_toAddMonoidHom` and `action_tmul` give the entire original additive
map and the pure-tensor formula.
`ofLinearEndHom_action` proves equality of the whole original
`NonUnitalModule S T` structures after converting back, using the published
`ofLinearEndHom_toLinearEndHom` round trip.

## Intrinsic equality of tensor coefficient Modules

For this comparison, S also has `IsScalarTower k S S`,
`SMulCommClass k S S`, `hS : IsIdempotented S`, and
`hSX : IsNondegenerate S X`. With exactly `HS` installed,
`recoveredModule_eq` proves

```text
NondegenerateScalars.module k hS
  (NondegenerateTensorFunctor.isNondegenerate hS hX hSX Y)
  = MT.
```

The proof installs `MT`, derives its S-tower by `isScalarTower`, and applies
the intrinsic uniqueness theorem
`NondegenerateScalars.module_eq_of_compatible`.
Output nondegeneracy is supplied by exactly the published tensor-generation
proof `NondegenerateTensorFunctor.isNondegenerate hS hX hSX Y`.
Neither output compatibility nor Module equality is an input.

`recovered_smul_eq` applies this structure equality to
`fun M : Module k T => letI := M; c • t`.
Its statement explicitly names the recovered S-module on the left and `MT`
on the right, for every `c` and `t`.

All constructions retain subsingleton and zero cases. No unit action,
nontriviality or finite-dimensional hypothesis is imposed.
