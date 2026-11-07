# Native equivariant split-kernel integral

This internally derived construction extends the published complex
split-kernel covariance and equivariant-integral interface to native
modules over a commutative complex algebra `R`. It uses the native
relative integral of `CoefficientSplitKernelIntegral`, the published
continuous inverse-conjugation automorphisms, and their published
positive Haar character. All group, coefficient-ring and carrier
universes remain independent.

Let `r : G →* L`, `s : L →* G`, and `H ≤ G`, with `s(L) ⊆ H`.
Write `N = ker r`, `I = H ∩ N`, `a(l) = s(l)` viewed in `H`,
and `σI` for the original representation restricted to `I`.
The published automorphism is

```text
α(l)(n) = s(l)⁻¹ n s(l).
```

## The original section action

The first constructions work over any commutative ring `R`, without
topological or complex-scalar hypotheses on the coefficient module.
`splitKernelCoefficientMap l` is the actual operator `σ(a(l))`.
It intertwines the pullback of `σI` along `α(l)|I` with `σI`;
the proof is the group identity
`s(l) α(l)(i) = i s(l)` followed by the representation law.

`splitKernelCoefficientLinearMap l` descends this intertwiner after
the inverse of the canonical identity-on-vector-classes automorphism
transport. Its representative formula is exactly

```text
[v] ↦ [σ(a(l)) v].
```

`splitKernelCoefficientAction` packages these original operators as
an `R`-linear representation of `L` on the actual quotient `σI_I`.
The identity and multiplication laws are proved on original vector
classes by quotient surjectivity. Its `_natural` theorem says that
every native inducing intertwiner commutes with this action.

Now assume `G` is locally compact, `r` and `s` are continuous,
`r(s(l)) = l`, `H` is closed and `σ` is smooth.
`splitKernelCompactEquiv_section` identifies restriction of the
original section translate with forward precomposition by `α(l)`
followed by `σ(a(l))`. The evaluation theorem records the literal
function identity at each `n ∈ N`:

```text
f(n s(l)) = σ(a(l)) f(α(l)(n)).
```

## Covariance of the native integral

Give `R` its complex algebra structure and the coefficient carrier its
compatible complex module structure. Assume `G` is Hausdorff and `N`
is locally compact, with the displayed Borel structures. Supply
regular Haar measures `μN`, `μI`, right invariance of `μI`, and a
quotient measure `ν` finite on compact sets, satisfying the published
`IsCompatible I μN μI ν`. Closedness of `I` supplies its local
compactness.

If `δ` denotes the published Haar automorphism factor, the scalar is

```text
c_R(l) = algebraMap ℂ R ((δ(α(l)|I) / δ(α(l)) : ℝ) : ℂ).
```

`splitKernelCompactIntegral_section` proves
`J(ρ(s(l)) f) = c_R(l) • A(l)(J(f))`, where `J` is the actual
relative integral and `A` is the section action just constructed.
It combines the original-function section identity, naturality of the
native absolute integral, and its proved forward-precomposition
covariance. The quotient automorphism transport cancels its inverse
in the definition of `A`. The scalar-tower instance on the native
quotient identifies the complex factor with the displayed native scalar.
The ratio is subgroup over kernel because the precomposition uses
`α(l)` itself.

`splitKernelCompactCoinvariantDesc_section` proves the same identity
on every native kernel-coinvariant class. Its source action is the
actual full-group action `toCoinvariants N` evaluated at `s(l)`;
the proof reduces to original compact-function representatives.

## Equivariant equivalence

Finally assume the literal compact open subgroup basis on `N` and
right invariance of `μN`, as required by relative integral bijectivity.
The published `splitKernelHaarRatio` is a positive character `χ`.
Its coefficient-algebra image is the units-valued character
`χR = Units.map (algebraMap ℂ R) ∘ complexCharacter χ`.
The definition `splitKernelCompactEquivariantEquiv` has type

```text
((c-Ind_H^G σ)_N, action through s)
  ≃[R,L] twist χR (splitKernelCoefficientAction r s H hsH σ).
```

Its underlying `R`-linear equivalence is exactly
`splitKernelCompactCoinvariantEquiv`, as the
`_toLinearEquiv` theorem states. The intertwining proof rewrites
the character value as the preceding Haar ratio and applies the
proved native descended covariance formula. Its `_mk` formula gives
the same finite-fiber integral of the original restricted function,
followed by the identity-on-classes complex-to-native comparison.
Its `_natural` theorem commutes with all native coefficient
intertwiners between independent carrier universes.

No compatibility data, bijectivity or equivariance is assumed as an
unproved representation comparison: the supplied hypotheses are
topological, smoothness and compatible Haar/quotient measure data,
and the maps and their properties are constructed. Existence of the
measure data, compact induction in stages, normalization cancellation,
actual rational orbit geometry and native compact-open fixed-module
finiteness remain separate obligations. This unit does not prove the
host rational supercuspidal Jacquet-family finiteness statement.
