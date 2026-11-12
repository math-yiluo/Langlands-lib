# Reduction of the quaternionic Kneser–Tits statement to two spin-cover inputs

Module `Langlands.GroupScheme.Quaternionic.LocalSpinKneserTitsReduction`, namespace
`Langlands.GroupScheme.Quaternionic`.

## Setting

These are the hypotheses of the Library's `LocalSpinKneserTitsStatement`:

* `K` is a nonarchimedean local field.
* `D` is a central division `K`-algebra with `dim_K D = 4`.
* `σ` is an involution of the first kind with `dim_K D^σ = 3`.
* `m ∈ {4, 5}`, and `q : σ.QuadraticForms (Fin m)` is nondegenerate of Witt index `1`.
* `π : S ⟶ O(q)` is a spin cover (`σ.IsSpinCover q π`).

Notation from other modules:

* `isometryRationalMatrix σ q` is the matrix of a rational point of `O(q)` (`EichlerDynamic`).
* For a hyperbolic pair `(e, f)`, `levi σ q _ a` is the Levi element `ℓ(a)`: `e ↦ a e`,
  `f ↦ σ(a)⁻¹ f`, the identity on `{e, f}^⊥` (`HyperbolicLevi`).
* `reducedNorm K D K (1 ⊗ a)` is the reduced norm of `a`.

## Statements

* `SpinLeviReducedNormSquareStatement` (a `Prop`). Take the setting above, any hyperbolic pair
  `h : σ.IsHyperbolicPair q e f`, any rational point `s` of `S` and any `a ∈ Dˣ`. If the matrix
  of `π(s)` equals `levi σ q (isHyperbolic_of_isHyperbolicPair h) a`, then
  `∃ t : K, reducedNorm K D K (1 ⊗ₜ a) = t ^ 2`.
* `SpinKernelElementaryStatement` (a `Prop`). In the setting above, every rational point `s` of
  `S` with `rationalPoints.map π s = 1` lies in `parabolicElementarySubgroup S`.

Both are statements about the spin cover, and neither is proved here. The first is a
condition on the Levi elements that lift to rational points of `S`, of spinor-norm type. The
second says that the rational kernel points of the spin cover lie in `S(K)⁺`.

## Results

* The imported `Langlands.LocalField.infinite_of_isNonarchimedeanLocalField` supplies
  infinitude of the local field.
* **`localSpinKneserTits_of_spinInputs`**: `SpinLeviReducedNormSquareStatement` and
  `SpinKernelElementaryStatement` together imply `LocalSpinKneserTitsStatement`.

  *Proof.* Fix the data of the statement.
  1. Witt index `1` gives a hyperbolic pair `(e, f)`
     (`exists_hyperbolicPair_of_quadraticWittIndex_pos`).
  2. `{e, f}^⊥` is anisotropic (`eq_zero_of_ortho_of_quadraticWittIndex_le_one`).
  3. `σ` has a nonzero alternating element (`exists_ne_zero_mem_alternatingSubspace`).
  4. Since `m ≥ 3`, some nonzero `x₀` is orthogonal to `e` and `f` (`exists_ne_zero_ortho`).
     By anisotropy, `q(x₀) ≠ 0`.
  5. Apply `parabolicElementarySubgroup_eq_top_of_levi_of_kernel` (`SpinEichlerLift`). Its
     hypothesis `hker` is the second statement. Its hypothesis `hlevi` comes from the first
     statement: a square reduced norm gives `ℓ(a) ∈ E` by
     `mem_eichlerLeviSubgroup_of_reducedNorm_eq_sq` (`EichlerReducedNorm`, with
     `reducedDegree_eq_two`).

## Provenance

Internal. This is the final reduction step for Task 5398. The two statements isolate the
spin-cover-specific inputs of the classical proof. All other ingredients are proved in
`HyperbolicLevi`, `EichlerReducedNorm`, `WittIndexOneInputs`, `EichlerDynamic` and
`SpinEichlerLift`.
