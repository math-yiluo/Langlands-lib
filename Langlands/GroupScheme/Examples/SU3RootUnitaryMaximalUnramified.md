# The models `X_{r,s}` over the maximal unramified extension

Module `Langlands.GroupScheme.Examples.SU3RootUnitaryMaximalUnramified`, namespace
`Langlands.GroupScheme.SU3Root`.

The module `Langlands.GroupScheme.Examples.SU3RootUnitaryIntegralModel` builds the integral
models `X_{r,s}` (`IsRamifiedQuadraticValuation.latticeModel`) of Kaletha–Prasad (KP)
Appendix C.4 under two hypotheses on a separable quadratic extension `L / K` with valuation
`ω : L → ℝ ∪ {∞}`:

- `IsRamifiedQuadraticValuation K L ω`: `ω` is invariant under the conjugation `σ` of `L / K`,
  `ω(K^×) ⊆ ℤ`, and some `π ∈ L` has `ω(π) = 1/2`;
- `IsValuationIntegers O K ω`: the image of `O → K` is `{a ∈ K | ω(a) ≥ 0}`.

This module proves these hypotheses in the setting of KP C.4: the base field is the actual
maximal unramified extension `inertiaFixedField F` of a nonarchimedean local field `F`, with
ring of integers `fixedFieldIntegers F`. It then specializes the models and their properties
to this field.

The proofs are internal. The ramification argument below is an elementary replacement for
KP's appeal to strict Henselianity. It is not KP's argument.

## Ramification from residue roots

Here `K` and `L` are fields, `L / K` is a separable quadratic extension, `σ = conjugation K L`,
and `ω` is an additive valuation on `L` with values in `WithTop ℝ`.

- **`HasResidueQuadraticRoots K ω`** (a `Prop`): for all `t, n ∈ K` with `ω(t) ≥ 0` and
  `ω(n) ≥ 0` there is `b ∈ K` with `ω(b² − t b + n) > 0`. Here `ω` is evaluated on the images
  of elements of `K` in `L`. This says that every monic quadratic polynomial with integral
  coefficients has a root modulo the maximal ideal. It holds when the residue field is
  algebraically closed.
- **`exists_half_of_hasResidueQuadraticRoots`**: assume `ω(σ z) = ω(z)` for all `z ∈ L`,
  `ω(a) ∈ ℤ` for all nonzero `a ∈ K`, `ω(ϖ) = 1` for some `ϖ ∈ K`, and
  `HasResidueQuadraticRoots K ω`. Then some `π ∈ L` has `ω(π) = 1/2`.
- `IsRamifiedQuadraticValuation.of_hasResidueQuadraticRoots`: the same hypotheses give
  `IsRamifiedQuadraticValuation K L ω`.

Proof of `exists_half_of_hasResidueQuadraticRoots`, as implemented:

1. Every nonzero `x ∈ L` has value in `(1/2)ℤ`: `x σ(x)` lies in `K`, is nonzero, and has value
   `2 ω(x)`.
2. Choose `θ ∈ L` with `σ(θ) ≠ θ` (`exists_conjugation_ne`). For `c ∈ K`, the element
   `θ − σ(θ)` is `(θ − c) − σ(θ − c)`. Its value is therefore at least `ω(θ − c)`. So the
   values `ω(θ − c)`, `c ∈ K`, are half-integers bounded above by `ω(θ − σ(θ))`.
   `Int.exists_greatest_of_bdd` gives `c₀ ∈ K` for which `m₀ = 2 ω(θ − c₀)` is maximal.
3. If `m₀ = 2k + 1` is odd, then `ϖ^{−k}(θ − c₀)` has value `1/2`.
4. If `m₀ = 2k` is even, put `y = ϖ^{−k}(θ − c₀)`, so `ω(y) = 0`. For every `c ∈ K`,
   `y − c = ϖ^{−k}(θ − (c₀ + ϖ^k c))`, so maximality gives `ω(y − c) ≤ 0`. The trace
   `t = y + σ(y)` and the norm `n = y σ(y)` lie in `K` and have nonnegative value. A residue
   root `b ∈ K` of `X² − t X + n` gives `ω(b² − t b + n) > 0`. But
   `b² − t b + n = (b − y) σ(b − y)` has value `2 ω(b − y) ≤ 0`. This is a contradiction, so
   this case does not occur.

## Henselian fields with algebraically closed residue field

Here `v : Valuation K ℤₘ₀` (`ℤₘ₀ = WithZero (Multiplicative ℤ)`) has a Henselian valuation
subring (`hH`). The Library defines `henselianQuadraticValuation K L v hH`, the
conjugation-invariant additive valuation on `L` whose value on a nonzero `a ∈ K` is the
integer `−log v(a)`.

- `henselianQuadraticValuation_nonneg_iff`: for `a ∈ K`, `0 ≤ ω(a)` if and only if `v(a) ≤ 1`.
- `henselianQuadraticValuation_pos_iff`: for `a ∈ K`, `0 < ω(a)` if and only if `v(a) < 1`.
- `henselianQuadraticValuation_hasResidueQuadraticRoots`: if the residue field of
  `v.valuationSubring` is algebraically closed, `HasResidueQuadraticRoots K ω` holds. The proof
  takes a root of the reduction of `X² − t X + n` in the residue field and lifts it to `K`.
- **`henselianQuadraticValuation_isRamified`**: if, in addition, `v` is surjective, then
  `IsRamifiedQuadraticValuation K L (henselianQuadraticValuation K L v hH)`. So every separable
  quadratic extension of such a field is ramified. The element `ϖ` with `ω(ϖ) = 1` comes from
  the Library's `exists_henselianQuadraticValuation_base_eq`.
- `isValuationIntegers_valuationSubring`: `v.valuationSubring` is the ring of integers of
  `henselianQuadraticValuation K L v hH` in the sense of `IsValuationIntegers`.

## The maximal unramified extension of a local field

Let `F` be a nonarchimedean local field (`[Field F] [ValuativeRel F] [TopologicalSpace F]
[IsNonarchimedeanLocalField F]`). Let `L` be a field in the same universe as `F`, with a
separable quadratic extension `L / inertiaFixedField F`. The Library supplies the
integer-normalized valuation `MaximalUnramified.valuation F` of `inertiaFixedField F`. The
Library also proves that this valuation is surjective (`MaximalUnramified.valuation_surjective`),
that its valuation subring is Henselian (`MaximalUnramified.valuationSubring_isHenselian`), that
its residue field is algebraically closed (`MaximalUnramified.residueField_isAlgClosed`), and
that its valuation subring is `fixedFieldIntegers F`
(`MaximalUnramified.mem_valuationSubring_iff`).

- **`maximalUnramifiedValuation F L`** is
  `henselianQuadraticValuation (inertiaFixedField F) L (MaximalUnramified.valuation F) _`.
- **`maximalUnramifiedValuation_isRamified`**:
  `IsRamifiedQuadraticValuation (inertiaFixedField F) L (maximalUnramifiedValuation F L)`.
  Every separable quadratic extension of the maximal unramified extension is ramified.
- **`maximalUnramifiedValuation_isValuationIntegers`**: `fixedFieldIntegers F` is the ring of
  integers of `maximalUnramifiedValuation F L`.
- **`maximalUnramifiedModel F L r s`** is the model
  `IsRamifiedQuadraticValuation.latticeModel` of these two facts, for arbitrary real `r` and
  `s`. It is an
  `IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) (unitaryParameterGroup (inertiaFixedField F) L)`.
- `maximalUnramifiedModel_isSmooth`, `maximalUnramifiedModel_hasGeometricallyConnectedFibres`:
  the model is smooth and its structure morphism has geometrically connected fibres.
- **`maximalUnramifiedModel_integralPoints_map`**: the image of its integral points under
  `unitaryRationalPointsEquiv (inertiaFixedField F) L` is
  `filtrationProduct r s = X(K)_r · Z(K)_s`, for the valuation `maximalUnramifiedValuation F L`.
- **`maximalUnramifiedTransition hr hs`**: for `r₁ ≤ r₂` and `s₁ ≤ s₂`, the transition
  homomorphism `X_{r₂,s₂} → X_{r₁,s₁}` over the identity of `U_{L/K}`
  (`IsRamifiedQuadraticValuation.latticeTransition`).

The model depends on the choices made in `latticeModel`: the element `λ = traceOneMax`, the
bases and generators, and the chosen preimages in `O`. These choices are the same as in
`SU3RootUnitaryIntegralModel`.

## Relation to the literature

KP Appendix C.4 works over a strictly Henselian field `K` with `ω(K^×) = ℤ`. It recalls the jump
sets from Corollary 3.2.4, "using that the separable quadratic `L/K` is ramified, as `K` is
strictly Henselian". KP do not prove the ramification at this point. The standard reason is
that a strictly Henselian field has no nontrivial unramified separable extension.

This module proves the ramification differently, by the elementary argument above. It uses
only the Henselian valuation subring, the surjective integer valuation, and the algebraically
closed residue field supplied by the Library. It does not use the classification of
unramified extensions or separability of the residue field extension. The Henselian property
enters only through the Library's construction of the invariant valuation
`henselianQuadraticValuation`.

The field `inertiaFixedField F` is the fixed field of the inertia subgroup inside the separable
closure of `F`. By the Library results above, its ring of integers `fixedFieldIntegers F` is
Henselian with algebraically closed residue field. The specialization therefore realizes KP's
setting with `K` the maximal unramified extension of `F` and `O` its ring of integers.

## Sources

- KP, Appendix C.4, printed p. 699 (PDF p. 730): the standing hypotheses of C.4 and the
  ramification of `L / K`.
- KP, Corollary 3.2.4 (cited there for the jump sets).
