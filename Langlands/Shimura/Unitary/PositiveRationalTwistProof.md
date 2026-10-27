# Existence of a rational positive skew twist

Authors: Worker 217 (proof, documentation and verification); Worker 57
(the three finite-dimensionality lines in the final theorem, supplied as a
feasibility snippet in the task context).

`Langlands.Shimura.CentralSimpleUnitaryData.positiveRationalSkewTwistExists`
proves the exact proposition `D.PositiveRationalSkewTwistExists C` from
`Langlands.Shimura.Unitary.PositiveRationalTwistStatement`. For the actual
central simple unitary datum `D` and every supplied
`HarrisSignatureCharts D.toSecondKindInvolution n Φ` object `C`, it produces
a unit `β` of the rational algebra `A`, a proof that `D.involution β = -β`,
and a proof that the real scalar extension of
`D.tracePairingAdjoint β hβ`, the involution `x ↦ β σ(x) β⁻¹`, satisfies the
existing `AlgebraInvolution.IsPositive`. That predicate requires the real
regular trace of `τ(x) x` to be strictly positive for every nonzero `x` in
`ℝ ⊗[ℚ] A`.

The theorem keeps every hypothesis of the target telescope and its three
universes `u`, `v`, `w`. Like the target, it does not assume
`IsScalarTower E K A`; it keeps `IsScalarTower ℚ E A`. No finite-place
condition is claimed. The witness `β` is selected by the proof. It is not an
input, and no openness or density property is assumed.

## The skew trace form

All four helper theorems are stated in the namespace
`Langlands.Shimura.AlgebraInvolution`. The proof uses one quantity
throughout. For a real algebra `B` with involution `τ`, a skew element `v`
and an element `y`, it is

    q(v, y) = tr(left multiplication by -(v τ(y) v y)),

where `tr` is the real trace (`LinearMap.trace ℝ B` of `LinearMap.mulLeft ℝ`).
For fixed `v`, `q(v, ·)` is a quadratic function: `q(v, t y) = t² q(v, y)`
for real `t`, since `τ` is real-linear. Positivity of a twist is rewritten as
positivity of this quantity by substituting `x = v y`. The substitution
avoids inverses, so `q` is a polynomial expression in `v`.

## Step 1: a real skew element from the positive complex homomorphism

`PositiveComplexHom.exists_skew_trace_pos` holds for an arbitrary real
algebra `B`, involution `τ` and `h : PositiveComplexHom τ`. It sets
`v = h(-i)`. The star compatibility of `h` gives
`τ(v) = h(conj(-i)) = h(i) = -v`, and `h(i) h(-i) = 1` gives `v v = -1`.
For `y ≠ 0`, the element `x = v y` is nonzero, because `y = -(v v) y`. The
published twist of `h` is `x ↦ h(-i) τ(x) h(i)`, so

    twist(x) x = v τ(y) τ(v) (-v) v y = v τ(y) v (v v) y = -(v τ(y) v y).

The positivity certificate of `h` at `x` therefore gives `q(v, y) > 0` for
every nonzero `y`. This real element `h(-i)` is only the starting point.
The objective's `h(i)` is its negative and gives the same twist.

## Step 2: rational selection by openness and density

`exists_rational_skew_trace_pos` assumes a finite-dimensional rational
algebra `A` with involution `σ`. Write `V = ℝ ⊗[ℚ] A` and
`ρ = σ.baseChange ℝ`. Suppose a skew `v₀ ∈ V` (`ρ v₀ = -v₀`) has
`q(v₀, y) > 0` for all nonzero `y`. The theorem then constructs `a ∈ A` with
`σ a = -a` and `q(1 ⊗ a, y) > 0` for all nonzero `y ∈ V`.

* **Topology.** `V` gets Mathlib's module topology over `ℝ`. This makes it a
  topological ring (`IsModuleTopology.isTopologicalRing`) and every real
  linear map out of it continuous (`IsModuleTopology.continuous_of_linearMap`).
  Hence the regular trace `T(z) = tr(mulLeft z)`, the map `ρ` and
  `F(v, k) = T(-(v ρ(k) v k))` are continuous.
* **Compactness.** `Module.finBasis ℚ A` extends to a real basis of `V`
  (`Algebra.TensorProduct.basis`), giving a continuous linear isomorphism
  `Φ : (Fin d → ℝ) ≃ V`. The image `S` of the unit sphere (sup norm) under
  `Φ` is compact and avoids `0`. Since `F(v₀, k) > 0` on `S`,
  `IsCompact.eventually_forall_of_forall_eventually` shows that
  `F(v, k) > 0` for all `k ∈ S` and all `v` in a neighbourhood of `v₀`.
* **Skew projection.** The real-linear map `s = ½ (id - ρ)` is continuous
  and fixes the skew element `v₀`. Thus for all `w` near `v₀`, `F(s w, k) > 0`
  for every `k ∈ S`.
* **Density.** The elements `1 ⊗ c` with `c ∈ A` are dense in `V`. The image of
  `ℚ^d` in `ℝ^d` is dense (`DenseRange.piMap` with `Rat.denseRange_cast`),
  `Φ` is continuous and surjective, and `Φ` maps a rational vector `r` to
  `1 ⊗ (∑ rᵢ bᵢ)`. Hence some `1 ⊗ a` lies in the neighbourhood above.
* **Witness.** Then `s(1 ⊗ a) = 1 ⊗ ((1/2 : ℚ) • (a - σ a))`. The proof takes
  the rational element `(1/2) • (a - σ a)`, which is skew because `σ` is
  involutive. A nonzero `y` is written as `t • Φ(t⁻¹ • c)` with
  `c = Φ⁻¹ y` and `t = ‖c‖ > 0`. The point `Φ(t⁻¹ • c)` lies in `S`, and
  homogeneity of degree 2 gives `q(1 ⊗ ((1/2)(a - σ a)), y) = t² F(…) > 0`.

## Step 3: invertibility and positivity of the twist

`exists_isPositive_skewAdjoint_of_trace_pos` again assumes a
finite-dimensional rational algebra. It starts from a skew `a ∈ A` with
`q(1 ⊗ a, y) > 0` for all nonzero `y ∈ V`.

* **`a` is a unit.** Suppose `a c = 0` with `c ≠ 0`. Then `1 ⊗ c ≠ 0`
  (`Algebra.TensorProduct.includeRight_injective`), but
  `q(1 ⊗ a, 1 ⊗ c)` is the trace of left multiplication by
  `-(1 ⊗ (a σ(c) a c)) = 0`, a contradiction. So left multiplication by `a`
  on `A` is injective. Finite dimensionality makes it surjective
  (`LinearMap.injective_iff_surjective`). `IsUnit.isUnit_iff_mulLeft_bijective`
  then makes `a` a unit `β`, and `σ β = -β` is the skewness of `a`.
* **Positivity.** `baseChange_skewAdjoint_apply` shows, by induction on
  tensors, that the real base change of `σ.skewAdjoint β hβ` is
  `x ↦ (1 ⊗ β) ρ(x) (1 ⊗ β⁻¹)`. Write `b = 1 ⊗ a` and `b' = 1 ⊗ β⁻¹`, so
  `b b' = b' b = 1`. Every `x ≠ 0` equals `b y` with `y = b' x ≠ 0`. Using
  `ρ(b) = -b`,

      b ρ(b y) b' (b y) = b ρ(y) (-b) (b' b) y = -(b ρ(y) b y),

  whose trace is `q(b, y) > 0`. Hence the conjugated involution is positive.

## The final theorem

The final theorem first derives `FiniteDimensional K A` from `D.finite`, then
`FiniteDimensional ℚ A` by `FiniteDimensional.trans ℚ K A`, then
`FiniteDimensional E A` by `Module.Finite.of_restrictScalars_finite ℚ E A`.
These three lines are Worker 57's feasibility snippet. None of them uses an
`E`/`K`/`A` scalar tower. The theorem applies the chart-level
`C.realPositiveComplexHom (Module.finBasis E A)`, a
`PositiveComplexHom` for
`D.toSecondKindInvolution.rationalInvolution.baseChange ℝ`, to Step 1.
It then applies Steps 2 and 3 to the rational involution
`D.toSecondKindInvolution.rationalInvolution`. The result matches the
target's `D.involution` and `D.tracePairingAdjoint β hβ` definitionally,
since `tracePairingAdjoint` is defined as `skewAdjoint` of this rational
involution. The datum-level constructors, which use `D.totallyRealBasis`
and assume `IsScalarTower E K A`, are not used.

## Provenance and scope

The statement Markdown cites Harris–Taylor (2001), Section I.7, which uses
rational approximation in the symmetric subspace. It also cites Kottwitz
(1992), Lemma 2.8, on the open positive cone. The implemented proof is an
internal variant of that idea for the derived skew-unit target. It proves
openness directly for the skew trace form `q` by compactness of a sphere
image. It uses the skew projection `(a - σ a)/2` and density of rational
points, then deduces invertibility from positivity. It does not transcribe
the positive-symmetric-cone lemma.

The file adds no definitions, only the theorems above. Its axioms are
`propext`, `Classical.choice` and `Quot.sound`. The proof stops at the
existence of the rational positive skew twist. It does not construct the
PEL datum, compare the inverse-unit twist with the original Harris group,
or address coefficient descent, lattices, levels or moduli.
