# Landherr's theorem over number fields: the proof

Module: `Langlands.Algebra.CentralSimple.NumberFieldLandherr`.

The theorem `Langlands.CentralSimple.numberFieldLandherr` proves
`Langlands.CentralSimple.NumberFieldLandherrStatement.{u}` (module
`Langlands.Algebra.CentralSimple.NumberFieldLandherrStatement`) for every universe `u`: for a
separable quadratic extension `E/F` of a number field, a finite-dimensional central simple
`E`-algebra `B` (an `F`-algebra through `E`) and an `F`-linear involution `τ` of `B` acting on
`E` by the nontrivial automorphism, every `τ`-symmetric unit `y` of `B` which is of the form
`x_v τ_v(x_v)` with `x_v` a unit of `F_v ⊗_F B` at every place `v` (archimedean and finite) is
of the form `x τ(x)` with `x ∈ Bˣ`.

## Proof

1. **Reduction to relative reduced norm one.** `exists_relNorm_eq_one` (module
   `Langlands.Algebra.CentralSimple.LandherrEichlerGlobal`) gives `b ∈ Bˣ` such that
   `y₂ = b⁻¹ y τ(b⁻¹)` has relative reduced norm one. It uses the Hasse norm theorem for
   `E/F`, local Hilbert 90, weak approximation and the Hasse–Schilling norm theorem for `B`.
2. **The new element.** `y₂` is a unit (`involutionUnit`) and `τ`-symmetric. At every place
   `v`, if `1 ⊗ y = x_v τ_v(x_v)`, then `1 ⊗ y₂ = c x_v τ_v(c x_v)` with `c = 1 ⊗ b⁻¹`, using
   `τ_v(1 ⊗ b⁻¹) = 1 ⊗ τ(b⁻¹)`.
3. **The case of reduced norm one.** `exists_eq_mul_of_relNorm_eq_one` (module
   `Langlands.Algebra.CentralSimple.LandherrMain`), applied with the local solutions at the
   finite places (`Global.Place F` of the form `.inr v`) and at the infinite places (`.inl w`),
   gives `x₂ ∈ Bˣ` with `y₂ = x₂ τ(x₂)`.
4. **Recombination.** Since `τ(b⁻¹) τ(b) = τ(b b⁻¹) = 1`, `y = b y₂ τ(b)`, so
   `y = (b x₂) τ(b x₂)`.

## Supporting modules by role

- algebraic preliminaries: `LandherrQuadraticData` (the skew generator `r = √d` of `E`),
  `LandherrTensorQuadratic` (coordinates on `E ⊗_F R`, Hilbert 90), `LandherrCancellation`
  and `LandherrNormOneUnit` (cancellation of a unit summand), `LandherrElementary`
  (elementary matrices, commutators, determinant one), `LandherrHermitianUnitary`
  (unitary matrices of prescribed determinant), `LandherrArtinianNorm` (norm equations in
  Artinian rings), `LandherrIntegrality`, `LandherrGoodPlaces` and `LandherrMainLemmas`;
- local theory: `LandherrNonsplit`, `LandherrNonsplitChart` and `LandherrNonsplitLocal`
  (nonsplit completions, local solutions of reduced norm one), `LandherrNormSemilinear` and
  `LandherrNumberFieldNorm` (`Nrd(τ x) = σ(Nrd x)`), `LandherrRealSplitting` (archimedean
  places), `LandherrHensel` (unramified places), `LandherrSquareRoot` and
  `LandherrPowNeighborhood` (roots near `1`), `LandherrLocalTarget`, `LandherrContinuity`;
- global theory: `LandherrSplitPlace` (split places via Chebotarev), `LandherrStrongApprox`
  (strong approximation away from one finite place), `LandherrNormGlobal` (norm equations in
  `F[y']`), `LandherrEichlerLocal`, `LandherrEichlerStep`, `LandherrEichlerGlobal`
  (reduction to reduced norm one), `LandherrFinish`, `LandherrAssembly` and `LandherrMain`
  (the case of reduced norm one).

All modules are in `Langlands/Algebra/CentralSimple/`; each has its own page.

## Provenance

The statement is Landherr's theorem in Platonov and Rapinchuk, *Algebraic Groups and Number
Theory* (1994), §6.7, Theorem 6.27, printed p. 359 (PDF p. 369), and in its second
formulation in Kneser, *Lectures on Galois Cohomology of Classical Groups* (1969), §5.5,
printed p. 77 (PDF p. 83). The proof follows Kneser's structure: reduction to reduced norm
one by the Hasse and Hasse–Schilling norm theorems (printed p. 77), then Lemma 1 of §5.5
(printed pp. 71–76, PDF pp. 77–82) for elements of reduced norm one. In the second step the
Library's proof replaces strong approximation for the group of elements of reduced norm one
by additive strong approximation of elementary `2 × 2` matrices over `B` together with Witt
cancellation; see the page of `Langlands.Algebra.CentralSimple.LandherrMain`.
