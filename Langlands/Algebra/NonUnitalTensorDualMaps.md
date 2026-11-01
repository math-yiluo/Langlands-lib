# Compatible-input ambient tensor-dual evaluation

Worker 321. This is derived internal infrastructure for David Renard,
*Représentations des groupes réductifs p-adiques*, French version of 9 July
2026, I.4.1–I.4.2, printed pp.22–24 / PDF28–30, especially the tensor-Hom
argument on PDF30. The original nonunital modules and idempotent conventions
are I.1.1, printed pp.5–6 / PDF11–12, and I.2.1–I.2.2, printed pp.14–16 /
PDF20–22. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The supplementary `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF1–2, contains nearby adjunction/corner corrections; the 2026 text governs.

## Original objects and selected coefficients

The four universes for S, R, X and M are independent. The inputs are the
specified original additive groups and nonunital actions, idempotented complex
algebras S and R, commuting S/ R-opposite actions on X, and nondegeneracy of
the left S and right R actions on X and the left R action on M. No complex
Module on a carrier is an input.

`FullDual` and `Dual` abbreviate exactly the published full and nondegenerate
duals of the original additive balanced tensor `Tensor R X M`. They explicitly
select `NonUnitalBimoduleTensor.leftModule hX M` and precisely
`NondegenerateTensorFunctor.isNondegenerate hS hX hSX M`. `Hom` is the
original right-R `NonUnitalModuleHom` from X to the actual nondegenerate dual
of M, with exactly `NonUnitalModuleDual.dualAction hR hM` on that target.

The additional input `hc` is exactly
`NonUnitalBimoduleTensorScalars.InputCompatible ℂ (S := S) hR hRX`: the scalar
tower on X recovered from its original right-R action. The bridge
`inputCompatible_iff_rightSourceCompatible` proves that this is the same
published sufficient input for the right-source Hom adapter. This assumption
is stronger than commuting additive actions. The issue and the conjugation
obstruction are explained in
[the coefficient-convention note](../../notes/renard/duality-coefficient-conventions.md).

`tensorModule_eq` retains the published equality between the complex Module
recovered from the residual S-action on the tensor and exactly
`NondegenerateTensorScalars.module ℂ R X M hR hM`. `coefficientFunctional`
keeps the same entire additive functional while proving its linearity for this
latter Module using the published scalar equality. Its underlying additive map
is literally unchanged.

## Implemented construction

`evaluate ell x` is the complex-linear functional
`m ↦ ell (tmul R X M x m)` on exactly the recovered Module of M. The whole
function identity and the additive/scalar refinements are stated separately.
Linearity follows from additivity of pure tensors and the published right
scalar formula, after the proved tensor coefficient comparison.

`exists_right_idempotent` obtains an actual original R-idempotent e fixing x
on the right from hRX. `evaluate_fixed` uses balancing to show that the same e
fixes the evaluated functional under the published full dual action.
`evaluate_mem` applies the published membership characterization, so it never
assumes that the full dual of M is nondegenerate. `curry` packages these actual
functionals as an original right-R intertwiner. Its right action law is the
balancing relation; `curry_function` and `curry_apply` give the entire
included evaluation function and its literal values.

For an original right intertwiner h, `pairing` is the biadditive pairing
`(x,m) ↦ (h x).val m`. Its balancing is proved directly from h's original
right-R intertwining law. `bilinearPairing` uses exactly the right-recovered
Module of X and the left-recovered Module of M. Automatic coefficient linearity
of original intertwiners, together with
`NonUnitalModuleDual.canonical_smul_val`, proves the first variable's scalar
law; this retains the proved agreement between recovered target coefficients
and the named dual Module.

`uncurryAdd` is exactly `NonUnitalModuleTensor.lift R` of this pairing and
its intrinsic balancing proof. `uncurryCoefficient` is exactly the published
`NondegenerateTensorScalars.linearLift` of `bilinearPairing`; the entire
underlying additive maps agree by reflexivity. `uncurry` keeps this additive
map and transfers its coefficient linearity by the proved tensor scalar
equality. The entire additive map, entire function, and literal pure-tensor
formula are exposed by `uncurry_toAddMonoidHom`, `uncurry_function` and
`uncurry_tmul`.

This pair constructs the two ambient maps. Their preservation laws and actual
nondegenerate-part restrictions are a separate focused pair in the same task.
No inverse identities, comparison equivalence, categorical naturality, actual
F/P specialization, or full-source I.4.2 coefficient-convention conclusion is
claimed. None of these is an input certificate to these constructions.
