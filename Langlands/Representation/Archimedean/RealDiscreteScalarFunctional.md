# Evaluation functionals of `O(n)`-equivariant maps into real standard modules

Lean module: `Langlands.Representation.Archimedean.RealDiscreteScalarFunctional`. Author:
Worker 380, for Task 6749 (`5dd3db87-6f14-4d0f-b9a7-3d0065415fd8`). It is the first module of
the proof of `Langlands.Archimedean.RealTiedDiscreteSeparatedScalarCommutantStatement` (module
`RealTiedDiscreteScalarCommutantCases`); the chain of modules ends in
`RealDiscreteSeparatedProof`. All declarations are in the namespace
`Langlands.Archimedean.RealDiscreteScalar`.

## Purpose and provenance

The module proves no statement of record. It supplies four facts about the value at the
identity of `L u`, where `L` is an `O(n)`-equivariant linear map into the `O(n)`-finite
functions of a real standard module. The later modules use these facts in the scalar step of
the discrete-series case. All declarations are internal and are proved here. The method (the
value at `1` of an `O(n)`-equivariant image determines the image, and is controlled by
rotations and sign matrices) is the elementary part of the minimal-`K`-type argument. It
follows the complex analogue `ComplexTemperedStandardIrreducibleProof.md` (Library).

## Notation

* `KF n ds` (Library, `RealTemperedCommutantReduction`) is the space of `O(n)`-finite vectors
  of `realStandardModule n ds`. Its elements are functions on `GL_n(ℝ)`.
* `realStandardRep n ds k` is right translation by `k ∈ O(n)`.
* `IsKEquivariant L` says that `L (R(k) v) = R(k) (L v)` for all `k ∈ O(n)` and all `v`.
* `ev f` is `f(1)`.
* `rot n p θ` is the Library `blockRotation n p θ` (module `StandardModule`), the rotation by
  `θ` in the coordinate plane `(p, p+1)`, as an element of `O(n)`.

## Declarations

* `ev_rep`: `ev (R(k) f) = f(k)`.
* `apply_toUnits`: for `IsKEquivariant L`, `(L u)(k) = ev (L (R(k) u))`. Proof: equivariance
  and `ev_rep`.
* `eq_zero_of_toUnits`: an element of `KF n ds` that vanishes on `O(n)` is zero. Proof: the
  Library lemma `RealTemperedCommutantReduction.eq_zero_of_compact_eval` (a vector whose
  translates all vanish at `1` is zero), with `ev_rep`.
* `exists_smul_family` (**scalar step**). Data: an `O(n)`-equivariant `Φ : KF n es → KF n ds`,
  a finite family `u_i` in `KF n es`, scalars `ε_i` and an index `i₀`. Hypothesis: for every
  `O(n)`-equivariant `L : KF n es → KF n ds` and every `i`,
  `ev (L u_i) = ε_i · ev (L u_{i₀})`. Conclusion: every endomorphism `E` of `KF n ds` that
  commutes with `O(n)` has one scalar `a` such that `E (Φ w) = a Φ w` for every `w` whose
  translates are combinations `R(k) w = Σ_i c(k, i) u_i`.

  Proof. For such `w` and every equivariant `L`, `apply_toUnits` and the hypothesis give
  `(L w)(k) = (Σ_i c(k, i) ε_i) · ev (L u_{i₀})`. Apply this to `L = Φ` and `L = E ∘ Φ`. If
  `ev (Φ u_{i₀}) = 0`, then `Φ w` vanishes on `O(n)`, so `Φ w = 0` and `a = 0` works.
  Otherwise put `a = ev (E Φ u_{i₀}) / ev (Φ u_{i₀})`. Then `E Φ w − a Φ w` vanishes on `O(n)`,
  so it is zero by `eq_zero_of_toUnits`.
* `ev_eq_zero_of_rotation` (**Fourier vanishing**). Let the block at position `p` of `ds` be the
  induction block of `d` (`realInducedBlockAt ds p = some d`, `realRank ds = n`). Let `u`
  satisfy `R(rot n p θ) u = e^{i w θ} u` for all `θ`, with `|w| ≤ |d.weight|`. Then
  `ev (L u) = 0` for every equivariant `L`.

  Proof. Let `f = L u`. Then `f(rot n p θ) = e^{i w θ} f(1)`, so the Library block Fourier
  coefficient `blockFourierCoefficient n p w f 1` equals `2π f(1)`. If `|w| < |d.weight|`, this
  coefficient vanishes by the defining Fourier condition of the standard module (the second
  component of membership in `realStandardModule`). If `|w| = |d.weight|`, then
  `w − (|d.weight| + 1)` is odd. The two characters of the block give the sign
  `(−1)^{|d.weight| + 1}` (Library `RealKTypeTransport.realInducedBlockAt_eq_some`), so the
  coefficient vanishes by the Library parity lemma
  `RealBlockJacquet.blockFourierCoefficient_eq_zero_of_not_even`.
* `ev_rep_sign` (**sign law**). If `s ∈ O(n)` is the diagonal matrix of a sign vector `a`, then
  `ev (L (R(s) u)) = χ_ds(a) · ev (L u)`, where `χ_ds = principalSeriesCharacter ℝ n
  (realPositionCharacter ds)`. Proof: `apply_toUnits` and the left-equivariance of `L u` under
  the diagonal torus.
