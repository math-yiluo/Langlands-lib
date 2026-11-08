# Compact differentiation on actual automorphic operator quotients

This internal construction proves that compact translation on an actual
automorphic operator subquotient is differentiated by the quotient complex
Lie action, measured against every complex linear functional on the
quotient. It then derives the infinitesimal compact consequences for
compact fixed vectors and for full compact equivariant quotient-valued
cochains, in parallel with the published numerator modules
`OperatorCompactDifferentiation`, `CochainCompactDifferentiation` and
`ReducedCochainCompactDifferentiation`.

Throughout, `F : Type uF` is a number field, `n` is any natural rank and
coefficients are complex. Write `K = standardInfiniteCompact F n`, including
every component, `L = ComplexLieAlgebra F n = ℂ ⊗[ℝ] RealLieAlgebra F n`,
`k𝕔 = CompactComplexLieAlgebra F n`, `j = compactComplexInclusion F n`, and
`complexify F n X = 1 ⊗ X`. No topology is placed on any coefficient space:
every derivative below is the derivative at `0` of a complex-valued function
of a real variable.

## The generic predicate

For any complex module `V` (in any universe), representation
`ρ : Representation ℂ K V` and complex Lie homomorphism
`A : L →ₗ⁅ℂ⁆ Module.End ℂ V`, the Prop-valued definition
`CompactDualDerivative ρ A` states: for every real Lie algebra element `X`,
every curve `c : ℝ → K` with `c 0 = 1` whose actual archimedean matrix
coordinates have derivative `realLieAlgebraToMatrix F n X` at `0`, every
complex linear functional `μ : V →ₗ[ℂ] ℂ` and every `v : V`,

```text
HasDerivAt (fun t => μ (ρ (c t) v)) (μ (A (complexify F n X) v)) 0.
```

This is a hypothesis-free definition of a property; it is not assumed for
any actual space. It is proved below for actual realizations and actual
quotients. Its consequences are proved once over the abstract `V`:

- `real_eq_zero_of_fixed`: if `v` lies in `ρ.invariants` (fixed by every
  element of `K`) and `X` lies in `compactLieSubalgebra F n`, then
  `A (complexify F n X) v = 0`. The proof takes the published compact
  tangent curve `compactTangentCurve` for `X`; each functional of the
  translated vector is constant, and uniqueness of derivatives together
  with `Module.forall_dual_apply_eq_zero_iff` gives the vector identity.
- `compact_eq_zero_of_fixed`: under the same hypothesis,
  `A (j Y) v = 0` for every `Y : k𝕔`, by tensor induction using
  `z ⊗ X = z • complexify F n X`.
- `cochain_compact_real`: for an alternating cochain
  `f : L [⋀^Fin q]→ₗ[ℂ] V` in
  `HorizontalAlternating.equivariant (complexCompactRepresentation F n) ρ q`,
  a compact real direction `Y` and real tuple `X`,

  ```text
  A (complexify Y) (f (complexify ∘ X))
    = ∑ i, f (Function.update (complexify ∘ X) i (complexify ⁅Y, X i⁆)).
  ```

  The proof compares, for every functional `μ`, the derivative of
  `μ (ρ (c t) (f …))` from the predicate with the published scalar cochain
  derivative `compactCurve_scalarCochain_deriv`; full compact equivariance and
  `complexLieConjugation_complexify` identify the two scalar curves.
- `cochain_compact_real_complex`: the same identity for arbitrary complex
  tuples, by the published `complexCochainInsertion_of_real`.
- `cochain_compact_complex`: for every `Y : k𝕔` and complex tuple `X`,

  ```text
  A (j Y) (f X) = ∑ i, f (Function.update X i ⁅j Y, X i⁆),
  ```

  by tensor induction in `k𝕔`, complex linearity and linearity of `f` in
  the replaced argument.

## Actual realizations

For an actual `S : OperatorRealization F n`, `S.pointEvaluation x` is the
complex-linear functional `v ↦ evaluate F n (S.toContinuous v) x` at an
adelic point `x : AdelicGL F n`; `pointEvaluation_apply` states this.
`eq_zero_of_pointEvaluation` proves that a vector at which every point
evaluation vanishes is zero, by injectivity of the published
`S.toContinuous` and function extensionality.

`span_pointEvaluation_eq_top` proves that for every finite-dimensional
subspace `W` of `S.Space`, the restrictions of all point evaluations to `W`
span the whole dual `Module.Dual ℂ W`. Their common kernel
(`dualCoannihilator`) is zero by the previous lemma, and
finite-dimensional duality (`Subspace.dualCoannihilator_dualAnnihilator_eq`)
then identifies the span with the annihilator of zero.

`hasDerivAt_dual_of_pointEvaluation` proves that if a curve `g : ℝ → W` in
such a `W` has, under every point evaluation, derivative equal to the
evaluation of `w : W` at `0`, then `μ ∘ g` has derivative `μ w` at `0` for
every complex linear functional `μ` on `S.Space`. The proof is induction
over the span of restricted point evaluations, which is all of the dual.

`compactCurve_dual_deriv` applies this to the finite-dimensional subspace
spanned by the compact orbit of `f` together with
`S.complexLieAction (complexify F n X) f`. The orbit span is
finite-dimensional by the published `compactRepresentation_isFiniteVector`.
Every point derivative is the published
`S.compactCurve_evaluate_deriv`, evaluated at the actual infinite and finite
projections of `x`, combined with `AdelicGL.pair_projections`. Hence
`S.compactDualDerivative` proves
`CompactDualDerivative S.compactRepresentation S.complexLieAction`.

## Actual quotients

Let `Q : OperatorSubquotient F n`, with quotient carrier `Q.Space`, its
published compact representation `Q.compactRepresentation`, and its complex
and compact Lie actions `Q.complexLieAction` and `Q.compactLieAction` from
`OperatorSubquotientLieAction`. No further hypothesis is imposed on `Q`.

`compactCurve_dual_deriv_projection` proves the predicate's derivative on a
projected representative: for a functional `μ` on `Q.Space`, it is the
numerator statement for `μ ∘ Q.projection`, because projection intertwines
compact translation and the complex Lie action definitionally.
`compactCurve_dual_deriv` extends it to every quotient vector by quotient
induction, and `Q.compactDualDerivative` proves
`CompactDualDerivative Q.compactRepresentation Q.complexLieAction`.

Specializing the generic consequences gives:

- `complexLieAction_compact_real_eq_zero`: a quotient vector fixed by all of
  `K` is killed by `Q.complexLieAction (complexify F n X)` for every compact
  real direction `X`;
- `compactLieAction_eq_zero_of_fixed`: such a vector is killed by
  `Q.compactLieAction Y` for every `Y : k𝕔`;
- `compactFixedLieInclusion`: the complex-linear identity map from
  `Q.compactRepresentation.invariants` into Mathlib's
  `LieModule.maxTrivSubmodule ℂ k𝕔 Q.Space` for the published quotient
  compact Lie module, with `compactFixedLieInclusion_coe` and injectivity;
- `cochain_compact_real`, `cochain_compact_real_complex` and
  `cochain_compact_complex`: the three insertion identities above for
  quotient-valued alternating cochains on `L` that are equivariant for the
  full compact group, the last one written with `Q.compactLieAction Y`.

`infinitesimalCompactCochains q` is the submodule of all
`f : L [⋀^Fin q]→ₗ[ℂ] Q.Space` satisfying, for every `Y : k𝕔` and
`X : Fin q → L`,

```text
Q.compactLieAction Y (f X) = ∑ i, f (Function.update X i ⁅j Y, X i⁆).
```

`mem_infinitesimalCompactCochains` is its exact membership predicate.
`compactEquivariantLieInclusion q` sends a full compact equivariant
quotient-valued cochain to the same cochain with this proved membership; it
is complex-linear and injective and preserves the underlying cochain.

## Reduced horizontal quotient cochains

With `[NeZero n]`, `reducedCochain_compact_complex` proves, for every full
compact equivariant `f : ReducedComplexLieAlgebra F n [⋀^Fin q]→ₗ[ℂ] Q.Space`
(for `reducedCompactRepresentation F n`), every `Y : k𝕔` and reduced tuple `X`,

```text
Q.compactLieAction Y (f X)
  = ∑ i, f (Function.update X i ⁅compactToReducedComplex F n Y, X i⁆).
```

As in the published `ReducedCochainCompactDifferentiation`, it applies the
ambient quotient identity to the published extension
`reducedCochainExtension F n q f` along the normalized projection, whose
equivariance is `reducedCochainExtension_equivariant`, and restores the
reduced tuple using `reducedCochainExtension_inclusion`, the Lie
homomorphism property of `reducedComplexProjection` and its compact and
inclusion identities.

`reducedInfinitesimalCompactCochains q` is the submodule of reduced
quotient-valued cochains satisfying exactly this identity, with exact
membership lemma; it is defined for every rank. The complex-linear injective
identity inclusion `reducedCompactEquivariantLieInclusion q` sends full
compact equivariant reduced cochains into it.
`infinitesimalHorizontalCochains q` is the intersection of the published
horizontal submodule `HorizontalAlternating.horizontal
(compactInReducedSubmodule F n) q` with that submodule, and
`horizontalCompactLieInclusion q` is the complex-linear injective identity
inclusion of the published `horizontalEquivariantSubmodule F n
Q.compactRepresentation q` into it, retaining horizontality and deriving
the infinitesimal condition. All three inclusions have `_coe` lemmas stating
that the underlying cochain is unchanged.

## Scope and provenance

The degree `q` is unrestricted; in degree zero the insertion sums are empty.
Only the implication from full compact group equivariance or invariance to
the infinitesimal identity is proved; no converse is claimed for the
possibly disconnected group `K`. This module constructs no quotient
evaluation as a function, no (g,K)-module structure, no relative
differential or relative cohomology, and no local factor, admissibility or
existence statement.

The provenance is internal. The numerator differentiation is the published
pointwise theorem `compactCurve_evaluate_deriv`, upgraded to all linear
functionals by finite-dimensional linear duality; the quotient statements
follow from the published quotient compact representation, finiteness and
Lie actions. No external source assertion is introduced.

The inherited additive group instances have explicit names specific to
this module, as in the published neighbouring modules; their definitions
are unchanged. `LieRing.ofAssociativeRing` is a local instance only for the
commutator Lie algebra on `Module.End ℂ V`, as in the imported Lie action
modules. Some numerator declarations disable
`backward.isDefEq.respectTransparency` locally, as in the published
`OperatorCompactDifferentiation`.
