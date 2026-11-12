# One spin cover suffices for the two spin inputs

Module `Langlands.GroupScheme.Quaternionic.SpinCoverModelTransport`. The per-cover definitions
and transport lemmas are in namespace
`Langlands.GroupScheme.Quaternionic.FirstKindInvolution.Eichler`. The model statement and the
final reductions are in `Langlands.GroupScheme.Quaternionic`.

## Setting

* `D` is a finite-dimensional central division algebra over a field `K`, with an involution
  of the first kind `σ`. `q : σ.QuadraticForms n` is a `σ`-quadratic form.
* `π : S ⟶ σ.isometryGroup q` is a homomorphism of group schemes over `Spec K`.
* `isometryRationalMatrix σ q` is the matrix of a rational point of `O(q)` (`EichlerDynamic`).
  For a hyperbolic pair `h : σ.IsHyperbolicPair q e f`, `levi σ q _ a` is the Levi element
  `ℓ(a)` (`HyperbolicLevi`, with `isHyperbolic_of_isHyperbolicPair` from `SpinEichlerLift`).

## Definitions (per cover)

* `LeviReducedNormSquare π` (a `Prop`): for all `e f : n → D`, all
  `h : σ.IsHyperbolicPair q e f`, all `s : rationalPoints S` and all `a : Dˣ`, if
  `isometryRationalMatrix σ q (rationalPoints.map π s) = levi σ q _ a`, then
  `∃ t : K, reducedNorm K D K (1 ⊗ₜ a) = t ^ 2`.
* `KernelElementary π` (a `Prop`): every `s : rationalPoints S` with
  `rationalPoints.map π s = 1` lies in `parabolicElementarySubgroup S`.

For `n = Fin m` and the hypotheses of the target, these are the instances, at one cover, of
`SpinLeviReducedNormSquareStatement` and `SpinKernelElementaryStatement`
(`LocalSpinKneserTitsReduction`).

## Results

* `rationalPoints_map_iso_hom`: let `e : S ≅ S'` and `π' : S' ⟶ O(q)` with
  `e.hom ≫ π' = π`. Then `π'(e(s)) = π(s)` on rational points.
* `LeviReducedNormSquare.of_iso`: under the same data, `LeviReducedNormSquare π'` implies
  `LeviReducedNormSquare π`. Apply the hypothesis to `e(s)`.
* `KernelElementary.of_iso`: under the same data, and if `S` and `S'` are connected
  reductive, `KernelElementary π'` implies `KernelElementary π`. If `π(s) = 1` then
  `π'(e(s)) = 1`, so `e(s) ∈ S'(K)⁺`. Then
  `s = e⁻¹(e(s)) ∈ S(K)⁺` by `parabolicElementarySubgroup_map_le_of_hom`.
* **`leviReducedNormSquare_and_kernelElementary_of_isSpinCover`**: let `π₀` and `π` be spin
  covers with `O(q)⁰` semisimple. If `π₀` satisfies both conditions, so does `π`. The proof uses
  the Library's uniqueness `IsSpinCover.exists_iso` (an isomorphism `S ≅ S₀` over `O(q)`).
  Spin covers are connected reductive because they are simply connected, hence semisimple.

## Statement and reductions

* `SpinCoverModelStatement` (a `Prop`). Assume the setting of `LocalSpinKneserTitsStatement`
  (nonarchimedean local `K`, central `D` with `dim_K D = 4`, `dim_K D^σ = 3`, `m ∈ {4, 5}`,
  `q` nondegenerate of Witt index `1`), and let `hsm` be a proof that `O(q)` is smooth. Then:
  - `O(q)⁰` is semisimple; and
  - some spin cover `π₀ : S₀ ⟶ O(q)` satisfies `LeviReducedNormSquare π₀` and
    `KernelElementary π₀`.
* `spinInputs_of_spinCoverModel`: `SpinCoverModelStatement` implies both
  `SpinLeviReducedNormSquareStatement` and `SpinKernelElementaryStatement`. A given spin cover
  `π` supplies the smoothness that the model statement needs.
* **`localSpinKneserTits_of_spinCoverModel`**: `SpinCoverModelStatement` implies
  `LocalSpinKneserTitsStatement`. This combines `spinInputs_of_spinCoverModel` with
  `localSpinKneserTits_of_spinInputs`.

## Provenance

Internal, for Task 5398. It reduces the spin-cover inputs to a single model cover through the
Library's uniqueness of spin covers (`SpinCoverReduction`). A construction of an explicit spin
cover, together with semisimplicity of `O(q)⁰`, then only has to verify the two conditions for
that one cover.
