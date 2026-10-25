# Rank-one nonvanishing and mirabolic evaluation of Whittaker functionals

Author: Worker 386.

This is an internal algebraic prerequisite of intrinsic square-integrable
genericity. It constructs evaluation at the identity as a complex-linear map
from actual mirabolic-model intertwiners to standard Whittaker functionals,
proves that it is injective, and handles rank-one nonvanishing.
It proves no higher-rank existence of a mirabolic intertwiner.

## Rank one

For an arbitrary commutative ring `F` with a topology, an allowed unitary additive
character `ψ`, and a complex representation `ρ` of `GL₁(F)`,
`hasFunctional_rankOne` assumes only `Nontrivial V`. Mathlib's algebraic
dual nontriviality supplies a nonzero complex-linear form. The published
`glFunctionals_rankOne` identifies the standard functional submodule with the
whole dual, so that form satisfies the required equivariance.

`isGeneric_rankOne` takes actual irreducibility and admissibility.
Irreducibility makes `ρ.asModule` a simple module over the monoid algebra and
therefore makes the carrier nontrivial. The theorem combines this fact with
the preceding functional and the definition of `Whittaker.IsGeneric`.
It needs neither square-integrability nor unitarizability.

## Evaluation on the actual mirabolic model

For every `n : ℕ`, assume additionally `IsTopologicalRing F` and let `ρ`
be a complex representation of the actual `GL_(n+1)(F)`. Group and carrier
universes remain independent. The incoming carrier has no topology or
finite-dimensionality assumption.

`mirabolicEvaluation ψ n ρ` is a complex-linear map

```
Representation.IntertwiningMap (ρ.comp (GeneralLinear.mirabolic n F).subtype)
  (Whittaker.mirabolicSmoothInduced ψ n)
    →ₗ[ℂ] Whittaker.glFunctionals ψ n ρ.
```

It sends `f` to the functional `v ↦ mirabolicEval ψ n (f v) 1`.
The construction uses the existing actual smooth induced function space with
right translation and left covariance. For an ambient upper-unipotent element,
`Mirabolic.upperUnipotentEquiv.symm` retains its matrix and views it in the
mirabolic group. Intertwining turns its action on `v` into right translation;
evaluation at one and left covariance give multiplication by the published
positive `standardCharacter ψ n`. There is no inverse character or sign change.
Linearity follows from pointwise addition and scalar multiplication.

`mirabolicEvaluation_coefficient` proves the exact recovery formula

```
(mirabolicEvaluation ψ n ρ f).val (ρ g.val v) =
  mirabolicEval ψ n (f v) g.
```

Thus equality of the resulting functionals implies equality of every value of
the two function-valued intertwiners. This proves
`mirabolicEvaluation_injective`, and then `mirabolicEvaluation_ne_zero`
proves that a specified nonzero input has a nonzero underlying linear functional.
`hasFunctional_of_mirabolicIntertwiner` packages that functional.
`isGeneric_of_mirabolicIntertwiner` adds actual irreducibility and
admissibility to obtain the existing `IsGeneric` predicate.

These final theorems are conditional on an actual nonzero intertwiner.
They supply only the algebraic functional passage in the intrinsic genericity
route. They do not assert the analytic mirabolic restriction theorem, construct a
Hilbert completion, identify its smooth vectors, or compare matrix coefficients
on the central quotient.

## Provenance and dependencies

The construction is derived directly from the imported Library definitions and
Mathlib linear duality, rather than a translation of an unproved source assertion.
It is the mirabolic evaluation analogue of the existing algebraic
`Whittaker.evaluationFunctional` and `Whittaker.functionalEquiv`.
The implementation imports `Whittaker.MirabolicModels` and
`Mathlib.LinearAlgebra.Dual.Lemmas`; all existing pairs are preserved.

Jacquet and Shalika, *The Whittaker models of induced representations* (1983),
§1.2, printed pp.108–109, equations (1.2.2)–(1.2.3) and the first paragraph of
p.109, motivate the functional convention and the eventual analytic use.
Registered original `jacquet-shalika-1983-whittaker`, retained file
`/home/taskhub/central-library/Jacquet-Shalika--The Whittaker models of induced representations--1983.pdf`,
SHA256 `e171831da6c064fdcb55efe79381ba1f85daa4efd7f3a79071589ffee9527f98`.
The source passage was read directly and visually checked during this task;
no source-specific erratum was present in the supplied Library notes.
The source's analytic existence assertion is not used as a theorem in this module.
