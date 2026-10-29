# Existence of a rational skew twist with the Kottwitz Hodge sign

Authors: Worker 217 wrote the Lean proof and its documentation and checked
them. Worker 57 is a coauthor. They designed the simultaneous
compact-sphere route stated in the task contract. The proof also reuses the
finite-dimensionality lines of the final theorem, which come from Worker 57's
snippet in the earlier joint proof `PositiveRationalTwistProof`.

`Langlands.Shimura.CentralSimpleUnitaryData.rationalHodgePolarizingTwistExists`
proves the exact proposition `D.RationalHodgePolarizingTwistExists C` from
`Langlands.Shimura.PEL.RationalHodgeTwistStatement`. The inputs are the
actual central simple unitary datum `D` and any supplied
`HarrisSignatureCharts D.toSecondKindInvolution n Φ` object `C`. Put
`h₀ = D.realPositiveKottwitzHom C` and `J = h₀(i)`. The theorem produces
one unit `β` of the rational algebra `A` together with a proof `hβ` that
`D.involution β = -β`. For this same `β` it proves three facts:

- the real scalar extension of the rational involution of
  `D.skewTwist β hβ` satisfies `AlgebraInvolution.IsPositive`;
- for the actual form `ψ = (D.skewTwist β hβ).tracePairingBaseChange ℝ β⁻¹`,
  `ψ x (y * J) = ψ y (x * J)` for all `x, y` in `ℝ ⊗[ℚ] A`;
- `0 < ψ x (x * J)` for every nonzero `x`.

The theorem keeps the whole target telescope: the universes `u`, `v`, `w`,
both `IsScalarTower E K A` and `IsScalarTower ℚ E A`, and every other
instance and implicit argument. The homomorphism `h₀` is the one already
constructed from `D` and `C`. The proof chooses only `β`, and it neither
assumes nor supplies any form, positivity or approximation hypothesis.

## Notation

In what follows `tr` is `Langlands.Algebra.regularTrace ℝ`, the unnormalized
real trace of left multiplication (`regularTrace_apply` is definitional).
`V = ℝ ⊗[ℚ] A` and `ρ = σ.baseChange ℝ` for a rational involution `σ`. The
proof uses two real expressions in a real element `v` and a vector `y`:

    Q(v, y) = tr(-(v ρ(y) v y)),
    R(v, y) = tr(v y J ρ(y)).

For fixed `v` both are homogeneous of degree 2 in `y`, because `ρ` is
real-linear. Neither involves an inverse.

## Helper theorems

The five helpers are stated in the namespace
`Langlands.Shimura.AlgebraInvolution`.

**`PositiveComplexHom.apply_hom_neg_I`.** For a real algebra `B` with
involution `τ` and `h : PositiveComplexHom τ`, `τ(h(-i)) = -h(-i)`. This
follows from the star compatibility of `h`, because the conjugate of `-i`
is `i`.

**`PositiveComplexHom.skew_trace_pos`.** For the same `h`, with the explicit
element `v = h(-i)`, `tr(-(v τ(y) v y)) > 0` for every nonzero `y`. The
proof does not use an existential witness. From `h(i) = -v` and
`h(i) h(-i) = 1` it gets `v v = -1`. Then `x = v y` is nonzero, since
`y = -(v v) y`. The published twist is `x ↦ h(-i) τ(x) h(i)`, so

    twist(x) x = v (τ(y) (-v)) (-v) (v y) = v τ(y) v (v v) y = -(v τ(y) v y),

and the positivity field of `h` at `x` gives the claim.

**`exists_rational_skew_trace_pos_and_signed_pos`.** Let `A` be a
finite-dimensional rational algebra with involution `σ` and let `J` be any
element of `V`. Suppose a real element `v₀` has `ρ(v₀) = -v₀`, and that
`Q(v₀, y) > 0` and `R(v₀, y) > 0` for every nonzero `y`. The theorem then
gives one rational `a` with `σ a = -a` such that `Q(1 ⊗ a, y) > 0` and
`R(1 ⊗ a, y) > 0` for every nonzero `y ∈ V`. The proof adapts the published
argument for the single form `Q`:

* `V` gets Mathlib's module topology over `ℝ`. This makes it a topological
  ring and every real-linear map out of it continuous. Hence
  `F(v, k) = min(Q(v, k), R(v, k))` is continuous on `V × V`.
* The finite rational basis `Module.finBasis ℚ A` extends to a real basis
  of `V`. This gives a continuous linear isomorphism `Φ : (Fin d → ℝ) ≃ V`.
  The image `S` of the unit sphere (sup norm) under `Φ` is compact and
  avoids `0`. Since `F(v₀, k) > 0` on `S`,
  `IsCompact.eventually_forall_of_forall_eventually` gives one
  neighbourhood of `v₀` on which `F(v, k) > 0` for all `k ∈ S`. So both
  forms stay positive on that common neighbourhood.
* The continuous skew projection `s = ½ (id - ρ)` fixes `v₀`. Hence
  `F(s w, k) > 0` for all `k ∈ S` and all `w` near `v₀`.
* Elements `1 ⊗ c` with `c ∈ A` are dense in `V`, since `Φ` maps rational
  coordinate vectors to them (`DenseRange.piMap`, `Rat.denseRange_cast`).
  Choose such a `1 ⊗ c` near `v₀` and put `a = (1/2 : ℚ) • (c - σ c)`.
  This `a` is skew because `σ` is involutive, and `s(1 ⊗ c) = 1 ⊗ a`.
* A nonzero `y` equals `t • Φ(t⁻¹ • Φ⁻¹ y)` with `t = ‖Φ⁻¹ y‖ > 0`, and
  `Φ(t⁻¹ • Φ⁻¹ y) ∈ S`. Homogeneity gives `Q(1 ⊗ a, y) = t² Q(1 ⊗ a, k)`
  and `R(1 ⊗ a, y) = t² R(1 ⊗ a, k)` for this `k ∈ S`, and both are
  positive.

**`isUnit_of_skew_trace_pos`.** If `a ∈ A` has `Q(1 ⊗ a, y) > 0` for every
nonzero `y`, then `a` is a unit. Suppose `a c = 0` with `c ≠ 0`. Then
`1 ⊗ c ≠ 0` (`Algebra.TensorProduct.includeRight_injective`), but
`Q(1 ⊗ a, 1 ⊗ c)` is the trace of `-(1 ⊗ (a σ(c) a c)) = 0`, which is a
contradiction. So left multiplication by `a` is injective. It is surjective
by finite dimensionality, and `IsUnit.isUnit_iff_mulLeft_bijective`
concludes. This helper keeps the given element `a`: it exports `IsUnit a`
rather than an unrelated unit.

**`isPositive_skewAdjoint_of_trace_pos`.** For a given unit `β` with
`σ β = -β` and `Q(1 ⊗ β, y) > 0` for every nonzero `y`, the real base change
of `σ.skewAdjoint β hβ` is positive. Write `b = 1 ⊗ β` and `b' = 1 ⊗ β⁻¹`.
Every `x ≠ 0` equals `b y` with `y = b' x ≠ 0`. The published
`baseChange_skewAdjoint_apply` and `ρ(b) = -b` give

    b ρ(b y) b' (b y) = -(b ρ(y) b (b' b) y) = -(b ρ(y) b y),

whose trace is `Q(b, y) > 0`. Unlike the published existential
`exists_isPositive_skewAdjoint_of_trace_pos`, this helper concludes
positivity for the unit `β` that it is given.

## The final theorem

The proof derives `FiniteDimensional K A` from `D.finite`, then
`FiniteDimensional ℚ A` by `FiniteDimensional.trans ℚ K A`. Let
`σ = D.toSecondKindInvolution.rationalInvolution`. The proof applies
`exists_rational_skew_trace_pos_and_signed_pos` with `J = h₀(i)` and the
explicit `v₀ = h₀(-i)`, and supplies its three hypotheses as follows:

- `ρ(v₀) = -v₀` by `apply_hom_neg_I`;
- `Q(v₀, ·) > 0` by `skew_trace_pos`;
- `R(v₀, ·) > 0` by the published `PositiveComplexHom.signed_trace_pos` of
  `HodgeTraceForm`, whose expression is literally
  `tr(h₀(-i) y h₀(i) ρ(y))`.

So one rational skew `a` carries both positivities. `isUnit_of_skew_trace_pos`
makes `a` a unit, and the proof sets `β = hunit.unit`, keeping the identity
`(β : A) = a` (`IsUnit.unit_spec`). Rewriting along this identity transfers
the skewness of `a` and both positivities from `a` to `β`. The three clauses
are then proved as follows.

- **Auxiliary positivity.** `isPositive_skewAdjoint_of_trace_pos` gives it,
  since the rational involution of `D.skewTwist β hβ` is definitionally
  `σ.skewAdjoint β hβ`.
- **Symmetry.** This is the published `kottwitzTraceHodgeForm_isSymm`.
  `kottwitzTraceHodgeForm β hβ C x y` is definitionally `ψ x (y * J)`.
- **Hodge positivity.** Write a nonzero `x` as `b y` with `b = 1 ⊗ β` and
  `y = (1 ⊗ β⁻¹) x ≠ 0`. The published `kottwitzTraceHodgeForm_diagonal_mul`
  gives `ψ (b y) (b y J) = (1/n) R(b, y)`. Here `R(b, y) > 0` by the choice
  of `a = β`, and `1/n > 0` because `D.rank_gt_one` gives `n > 1`.

## Provenance and scope

The target's conventions come from its statement module. It uses Kottwitz
(1992), printed p.374, for positivity of `(v, h(i) w)`, the conjugated
Kottwitz homomorphism `h₀` of `RealPositivity`, and the Harris–Taylor (2001)
I.7 skew-unit trace form. The proof follows the route proposed in the task
contract. It is an internal adaptation of the compact-sphere and density
argument of `PositiveRationalTwistProof` to two forms at the same explicit
real point `h₀(-i)`, in the spirit of the openness and rational approximation
of Kottwitz's Lemma 2.8 and Harris–Taylor I.7. It does not transcribe either
source's argument.

The file adds only theorems, no definitions, and imports
`RationalHodgeTwistStatement`, `HodgeTraceForm` and
`PositiveRationalTwistProof` unchanged. Its axioms are `propext`,
`Classical.choice` and `Quot.sound`. It stops at this rational existence
theorem. It does not specialize the witness for the parent task or compare
adelic groups, and it does not treat coefficient descent, lattices,
abelian-scheme polarizations or PEL moduli.
