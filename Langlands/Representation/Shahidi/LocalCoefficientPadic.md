# Shahidi's local coefficient over a p-adic field

This module defines the relation "`C` is the local coefficient
`C_χ(s, π₁ ⊗ π₂)`" for the p-adic induced representation `I(s, π₁ ⊗ π₂)`.
The source is F. Shahidi, *Fourier transforms of intertwining operators and
Plancherel measures for GL(n)*, American Journal of Mathematics 106 (1984),
67–111, printed pages 72–73:

\[
\lambda^{-s}_{\pi'}\bigl(A(s,\pi,w_{m,n})f\bigr)=C_\chi(s,\pi)^{-1}\,\lambda^s_\pi(f)
\qquad (0.3)
\]

for all `f ∈ I(s,π)`, where `π = π₁ ⊗ π₂` and `π' = π₂ ⊗ π₁`.

The registered original is `shahidi-1984-fourier`, SHA256
`a10d5c605d94d4e85d0e5f453d6a8c233d91e3cb60d538f430d8ad900cbb6b29`.
The author is Worker 11.

The unit specializes the published function-level relation
`IsLocalCoefficient` of `Langlands.Representation.Shahidi.LocalCoefficient`.
There, `f` is an arbitrary function with values in a space `V`, and two
arbitrary functionals `ℓ` and `ℓ'` stand in for `λ₁ ⊗ λ₂` and `λ₂ ⊗ λ₁`.
Here:

- `f` runs over the actual p-adic `I(s, π₁ ⊗ π₂)` of
  `Langlands.Representation.Shahidi.Induction`;
- the intertwining integral is the one of the published p-adic operator
  `shahidiIntertwining` of `Langlands.Representation.Shahidi.IntertwiningPadic`;
- `ℓ` and `ℓ'` are built from Whittaker functionals `λ₁` of `π₁` and `λ₂`
  of `π₂`.

## Setting in the source

On page 72, `π₁` and `π₂` are irreducible admissible representations of
`GL_m(F)` and `GL_n(F)`, and both are non-degenerate. The source then says
"Fix two `χ`-Whittaker functionals `λ₁` and `λ₂` for `π₁` and `π₂`". The
functional `λ^s_π` of (0.2) integrates `⟨f(w_{m,n} u'), λ₁ ⊗ λ₂⟩` against
`χ(u')` conjugated. The functional `λ^{-s}_{π'}` of `I(-s, π')` integrates
`⟨f(w_{m,n}⁻¹ u), λ₂ ⊗ λ₁⟩` against `χ(u)` conjugated. Page 73 says that
"`λ₁ ⊗ λ₂` denotes the map induced by `λ₁ × λ₂` on the tensor product of the
spaces `V₁` and `V₂`". Page 73 also remarks that `C_χ(s, π)` depends on the
measures defining `A(s, π, w_{m,n})`, `λ^s_π` and `λ^{-s}_{π'}`.

## The functional λ₁ ⊗ λ₂

These declarations lie in `Langlands.Shahidi`. `V₁` and `V₂` are complex
vector spaces. `V₁ ⊗ V₂` is the published two-factor carrier
`PiTensorProduct ℂ (pairCarrier V₁ V₂)` of `Induction`, with factor `0`
equal to `V₁` and factor `1` equal to `V₂`.

- `pairFactorFunctional ℓ₁ ℓ₂ i` is `ℓ₁` on factor `0` and `ℓ₂` on
  factor `1`.
- `pairFunctional ℓ₁ ℓ₂` is the linear functional `λ₁ ⊗ λ₂` on `V₁ ⊗ V₂`.
  It is the linear map induced (`PiTensorProduct.lift`) by the multilinear
  map `v ↦ ℓ₁(v₀) ℓ₂(v₁)`. This is the page-73 description.
- `pairFunctional_tprod` and the simp lemma `pairFunctional_pairTensor`:
  `(λ₁ ⊗ λ₂)(v₁ ⊗ v₂) = λ₁(v₁) λ₂(v₂)`.
- `pairFunctional_pairFlip`: `(λ₂ ⊗ λ₁)(flip x) = (λ₁ ⊗ λ₂)(x)` for every
  `x ∈ V₁ ⊗ V₂`. Here `flip : V₁ ⊗ V₂ ≃ V₂ ⊗ V₁` is the published `pairFlip`
  of `IntertwiningInduced`. The proof is induction on `x`: on pure tensors
  `pairSwap_tprod` computes `flip`, and the two products agree by
  commutativity of `ℂ`.
- `pairFunctional_smul_left` and `pairFunctional_smul_right`:
  `(a λ₁) ⊗ λ₂ = a (λ₁ ⊗ λ₂)` and `λ₁ ⊗ (b λ₂) = b (λ₁ ⊗ λ₂)`. The proofs
  compare the two sides on pure tensors (`PiTensorProduct.ext`).
- `swappedJacquetIntegrand_pairFlip_symm`: for a function `B` with values in
  `V₂ ⊗ V₁`, the swapped Jacquet integrand of `g ↦ flip⁻¹ (B g)` for
  `λ₁ ⊗ λ₂` equals the swapped Jacquet integrand of `B` for `λ₂ ⊗ λ₁`. This
  is `pairFunctional_pairFlip` at each point.

## The relation for fixed functionals

The remaining declarations lie in `Langlands.PadicField.TopologicalData`, for
`F : PadicField p` and a supplied realization `T : F.TopologicalData`. The
field carries `T.topology`, and the absolute value is the published
`T.shahidiAbsoluteValue`, with `|ϖ| = q⁻¹`.

The ranks are written `m+1` and `n+1`. So `π₁` is a complex representation
of `GL_{m+1}(F)` on `V₁`, and `π₂` is one of `GL_{n+1}(F)` on `V₂`. This
covers all positive ranks, and the induced representation lives on
`GL_{(m+1)+(n+1)}(F)`, the group of the published Jacquet integrals.
No irreducibility, admissibility or smoothness is assumed in the
definitions.

- `shahidiSourceFunctions π₁ π₂ s` is the set of functions `g ↦ f(g)`, with
  values in `V₁ ⊗ V₂`, for `f` in the p-adic `I(s, π₁ ⊗ π₂)`. It is the range
  of the published `shahidiSourceEval`. These are the Library's smooth induced
  functions. The source uses `K_r`-finite functions; `Induction` leaves that
  comparison open.
- `IsShahidiLocalCoefficientFor ψ μ μJ μJ' ℓ₁ ℓ₂ C` is the published
  `IsLocalCoefficient` with the following data:
  - `ρ` is the published `pairRepresentation` of the Levi
    `GL_{m+1}(F) × GL_{n+1}(F)` on `V₁ ⊗ V₂`, acting by `π₁ ⊗ π₂`;
  - `ℓ = ℓ' = pairFunctional ℓ₁ ℓ₂`, that is, `λ₁ ⊗ λ₂` on both sides;
  - `q` is the residue cardinality `T.residueCardinality`;
  - the family is `s ↦ shahidiSourceFunctions π₁ π₂ s`.

  `ψ` is a unitary additive character of `F` for `T.topology`. It defines the
  Whittaker character `χ` of the published Jacquet integrals, the standard
  character `u ↦ ψ(Σᵢ u_{i,i+1})`. `μ` is a measure on the `(n+1)` by `(m+1)`
  matrices, the measure `du'` of (0.1). `μJ` is a measure on the same matrices,
  the measure `du'` of (0.2). `μJ'` is a measure on the `(m+1)` by `(n+1)`
  matrices, the measure `du` of `λ^{-s}_{π'}`. As in `LocalCoefficient`, the
  three measures are independent arguments, no Haar property or normalization
  is assumed, and `F.Carrier` carries an arbitrary measurable structure.

Unfolding `IsLocalCoefficient`: there is a real `a` such that for every `s`
with `a < Re s`, the denominator of `C` does not vanish at `q^(-s)`, some
`f ∈ I(s, π₁ ⊗ π₂)` has a nonzero Jacquet integral, and every
`f ∈ I(s, π₁ ⊗ π₂)` satisfies (0.3) with `c = C(q^(-s))`. In particular
`c ≠ 0`, and the intertwining integral of `f` against `μ` exists at every
`g`. The published Markdown of `LocalCoefficient` explains each condition.

**Why `ℓ' = λ₁ ⊗ λ₂`.** In the generic relation, the intertwining integral
`A` of `f` is the weak integral of `a ↦ f(w_{m,n} u'(a) g)`, so it takes
values in `V₁ ⊗ V₂`. The p-adic operator `shahidiIntertwining` takes values
in `V₂ ⊗ V₁`. By the published `hasIntegral_shahidiIntertwining`, the generic
`A` is `flip⁻¹` of `shahidiIntertwining f`. By `pairFunctional_pairFlip`,
applying `λ₁ ⊗ λ₂` after `flip⁻¹` is applying `λ₂ ⊗ λ₁`. So the generic
swapped Jacquet integral with `ℓ' = λ₁ ⊗ λ₂` is the source's `λ^{-s}_{π'}`,
built from `λ₂ ⊗ λ₁`, applied to `A(s, π, w_{m,n}) f`. The theorem
`satisfiesLocalCoefficientEquation_shahidiSourceEval_iff` below proves this.

## The relation quantified over admissible choices

The Library's standard Whittaker functionals of `π₁` form the submodule
`glFunctionals ψ m π₁` of `Module.Dual ℂ V₁`. It consists of the `λ` with
`λ(π₁(u) v) = χ(u) λ(v)` for the standard character `χ` of the upper
unipotent subgroup of `GL_{m+1}(F)`. On a block-diagonal unipotent matrix,
the superdiagonal entry joining the two blocks is `0`. So the standard
character of `GL_{(m+1)+(n+1)}(F)` restricts on the Levi to the product of
the standard characters of the two blocks. This computation explains the
choice and is not formalized here. With it, these are the source's
`χ`-Whittaker functionals, for `χ` the standard character of `ψ`.

`IsShahidiLocalCoefficient ψ μ μJ μJ' C` means:

1. `π₁` and `π₂` have nonzero standard Whittaker functionals: some
   `λ₁ ∈ glFunctionals ψ m π₁` and some `λ₂ ∈ glFunctionals ψ n π₂` are
   nonzero;
2. for all nonzero `λ₁ ∈ glFunctionals ψ m π₁` and nonzero
   `λ₂ ∈ glFunctionals ψ n π₂`,
   `IsShahidiLocalCoefficientFor ψ μ μJ μJ' λ₁ λ₂ C` holds.

The source fixes one pair of functionals. Condition 2 asks for every pair, so
the relation does not depend on a choice. When the Whittaker functionals of
`π₁` and of `π₂` are unique up to scalars, the two readings agree, by
`IsShahidiLocalCoefficientFor.isShahidiLocalCoefficient` below and by
definition. Condition 1 is the source's non-degeneracy. It also makes
condition 2 nonvacuous, so uniqueness needs no further hypothesis.

## Results

Let `π₁` and `π₂` be smooth, in the Library's sense `IsSmooth` for
`T.topology`.

- `IsShahidiLocalCoefficientFor.unique`: for fixed `λ₁` and `λ₂`, at most
  one rational function `C` satisfies `IsShahidiLocalCoefficientFor`. The
  proof is the published `IsLocalCoefficient.unique`. Its inputs are compact
  open cofinality of the Levi (`T.leviCompactOpenCofinal`), smoothness of
  `π₁ ⊗ π₂` (`isSmooth_pairRepresentation`), and `1 < q`
  (`T.residueCardinality_gt_one`).
- `IsShahidiLocalCoefficient.unique`: at most one rational function `C`
  satisfies `IsShahidiLocalCoefficient`. Condition 1 supplies nonzero
  functionals, and the previous result applies to them.

The next two results need no smoothness.

- `IsShahidiLocalCoefficientFor.smul`: if `C` is the local coefficient for
  `λ₁` and `λ₂`, it is the local coefficient for `a λ₁` and `b λ₂` whenever
  `a ≠ 0` and `b ≠ 0`. By the two scaling lemmas,
  `(a λ₁) ⊗ (b λ₂) = (b a)(λ₁ ⊗ λ₂)`, and the published
  `IsLocalCoefficient.smul` applies with the scalar `b a`.
- `IsShahidiLocalCoefficientFor.isShahidiLocalCoefficient`: let `C` be the
  local coefficient for nonzero `λ₁ ∈ glFunctionals ψ m π₁` and
  `λ₂ ∈ glFunctionals ψ n π₂`. Assume every standard Whittaker functional of
  `π₁` is a multiple of `λ₁`, and every one of `π₂` is a multiple of `λ₂`.
  Then `IsShahidiLocalCoefficient ψ μ μJ μJ' C` holds. A nonzero functional is
  a nonzero multiple, so the previous result applies. The multiplicity-one
  hypotheses are explicit; the module does not prove multiplicity one.

The last result checks that the relation is (0.3) read literally. Assume
`F.Carrier` has `MeasurableAdd₂` and `MeasurableMul`, `μ` is invariant under
left translation, and `hμ : IsModulusScaling … T.shahidiAbsoluteValue μ`, as
required by `shahidiIntertwining`. For an additive Haar measure `μ`, the
published `isModulusScaling_padic` supplies `hμ`.

- `satisfiesLocalCoefficientEquation_shahidiSourceEval_iff`: let `π₁` and
  `π₂` be smooth, let `ℓ₁` and `ℓ₂` be arbitrary linear functionals, let `f`
  lie in the convergence domain `shahidiSourceDomain` of (0.1), and let
  `c ∈ ℂ`. Then the generic relation `SatisfiesLocalCoefficientEquation` at
  `f`, with `λ₁ ⊗ λ₂` on both sides, holds if and only if:
  - `c ≠ 0`, and
  - for some `z` and `z'`, the Jacquet integral of `f` for `λ₁ ⊗ λ₂`
    stabilizes to `z`, the swapped Jacquet integral of
    `A(s, π, w_{m,n}) f = shahidiIntertwining f ∈ I(-s, π₂ ⊗ π₁)` for
    `λ₂ ⊗ λ₁` stabilizes to `z'`, and `z' = c⁻¹ z`.

  The proof identifies the generic intertwining integral with
  `flip⁻¹ ∘ shahidiIntertwining f`. It uses `hasIntegral_shahidiIntertwining`
  and the published `HasIntertwiningIntegral.unique`, whose inputs are the
  cofinality and smoothness above. It then rewrites the swapped integrand by
  `swappedJacquetIntegrand_pairFlip_symm`.

## What is not claimed

This unit does not claim the following:

- that a local coefficient exists, for any `π₁` and `π₂`. Existence is a
  separate obligation of the parent task;
- that the intertwining or Jacquet integrals converge or stabilize on
  `I(s, π₁ ⊗ π₂)`, or that the Jacquet functional is nonzero there;
- multiplicity one of Whittaker functionals;
- any normalization of the measures `μ`, `μJ` and `μJ'`;
- the comparison of the Library's smooth induction with Shahidi's
  `K_r`-finite functions;
- Theorem 5.1.
