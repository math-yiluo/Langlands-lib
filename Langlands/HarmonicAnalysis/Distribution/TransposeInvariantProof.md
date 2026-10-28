# Proof of transpose invariance of conjugation-invariant distributions

This module proves the published statement
`Langlands.GeneralLinearConjugationDistributionTransposeStatement.{uF}` from
`Langlands.HarmonicAnalysis.Distribution.TransposeInvariantStatement`. The
closing theorem is

```lean
theorem Langlands.generalLinearConjugationDistributionTranspose :
    GeneralLinearConjugationDistributionTransposeStatement.{uF}
```

It is unapplied and keeps the statement's single field universe `uF`. The
statement module is imported unchanged. Thus, for every prime `p`, every actual
`F : PadicField.{uF} p` with `F.canonicalNormedField` and every `n`, a complex
algebraic distribution on `G = Matrix.GeneralLinearGroup (Fin (n + 1)) F.Carrier`
that is invariant under every inner automorphism `c_a` is invariant under the
transpose map `τ = transposeHomeomorph (n + 1) F.Carrier`.

## Inputs

The proof is assembled from four published propositions and their published
proofs, each applied at the universes shown:

- `EquivariantLocalizationStatement.{uF, uF, uF}`
  (`Distribution.LocalizationStatement`), proved by
  `Langlands.HarmonicAnalysis.Distribution.equivariantLocalization`:
  localization of twisted-equivariant distributions along a continuous map to a
  locally compact, totally disconnected Hausdorff space.
- `FiniteOrbitAntiInvariantVanishingStatement.{uF, uF}`
  (`Distribution.FiniteOrbitVanishingStatement`), proved by
  `Langlands.HarmonicAnalysis.Distribution.finiteOrbitAntiInvariantVanishing`:
  vanishing of group-invariant, `σ`-anti-invariant distributions supported in a
  closed finite union of orbits each preserved by `σ`.
- `Langlands.MatrixTransposeConjugateStatement.{uF}`
  (`LinearAlgebra.MatrixTransposeConjugateStatement`), proved by
  `Langlands.matrixTransposeConjugate`: every square matrix over a field is
  conjugate to its transpose.
- `Langlands.MatrixCharpolyFiniteConjugacyStatement.{uF}`
  (`LinearAlgebra.MatrixCharpolyConjugacyStatement`), proved by
  `Langlands.matrixCharpolyFiniteConjugacy`: the matrices with a fixed
  characteristic polynomial fall into finitely many conjugacy classes.

The topology facts on `G` are the Library's
`F.canonicalTopologicalData.generalLinearNonarchimedean`,
`generalLinearLocallyCompactSpace`, `generalLinearSigmaCompactSpace` and
`generalLinearT2Space`, after the `NormedAlgebra (Padic p) F.Carrier`,
`ProperSpace` and `IsUltrametricDist` instances are installed from
`F.canonicalNormedAlgebra`, `FiniteDimensional.proper` and the spectral norm.
Total disconnectedness of `G` is Mathlib's instance for Hausdorff
nonarchimedean groups. The transport lemmas `pushforward_transpose_involutive`,
`IsConjugationInvariant.pushforward_transpose`, `transposeHomeomorph_coe` and
`transposeHomeomorph_involutive` come from the imported distribution modules.

## Implemented proof

The auxiliary declarations below live in the namespace
`Langlands.HarmonicAnalysis.Distribution`. The main step is the theorem
`generalLinearConjugationDistributionTranspose_of_prerequisites`. It takes the
four propositions above as hypotheses `h1`, `h3`, `h4` and `h5` and proves the
target statement. The closing theorem, in the namespace `Langlands`, applies it
to the four published proofs.

### Auxiliary declarations

- `conjAct_orbit_eq`: for a group `G`, the orbit of `x` under Mathlib's
  `ConjAct G` action is the conjugacy class `{g | ∃ a, a * x * a⁻¹ = g}`.
- `conjugationInvariant_finiteOrbit_vanishing`: the finite-orbit proposition
  specialized to the conjugation action of a nonarchimedean, locally compact,
  sigma-compact Hausdorff group `G` on itself. Mathlib gives `ConjAct G` no
  topology, so the proof installs local copies of the topology and of the
  `NonarchimedeanGroup`, `LocallyCompactSpace` and `SigmaCompactSpace` instances
  of `G` by `inferInstanceAs`. Continuity of `(c, x) ↦ ofConjAct c * x * (ofConjAct c)⁻¹`
  gives `ContinuousSMul (ConjAct G) G`. Its orbits are the conjugacy classes by
  `conjAct_orbit_eq`. The homeomorphism `Homeomorph.smul c` equals
  `conjugationHomeomorph (ofConjAct c)` pointwise, so invariance under
  `ConjAct G` is `IsConjugationInvariant`.
- `charpoly_eq_of_coeff_eq`: over a field, two `m × m` matrices whose
  characteristic polynomials agree in the coefficients of degree below `m` have
  equal characteristic polynomials. Both polynomials are monic of degree `m`
  (`Matrix.charpoly_monic`, `Matrix.charpoly_natDegree_eq_dim`), so
  `Polynomial.Monic.as_sum` expands them into these coefficients.
- `charpolyCoeffs m g : Fin m → K` lists the coefficients of degree below `m`
  of the characteristic polynomial of `g : GL_m(K)`.
  `charpolyCoeffs_conj` proves invariance under conjugation
  (`Matrix.charpoly_units_conj`), and `charpolyCoeffs_transpose` proves
  invariance under `transposeHomeomorph` (`Matrix.charpoly_transpose`).
- `continuous_charpolyCoeffs`: over a topological ring, each coefficient is the
  evaluation at the matrix entries of the integer polynomial
  `(Matrix.charpoly.univ ℤ (Fin m)).coeff i`, mapped to `K`
  (`Matrix.charpoly.univ_coeff_eval₂Hom`). Polynomial evaluation is continuous
  (`MvPolynomial.continuous_eval`), and so are the entries of `Units.val`.

### The assembly

Fix `p`, `F`, `n` and a conjugation-invariant `D`, and write `q` for
`charpolyCoeffs (n + 1) : G → (Fin (n + 1) → F.Carrier)`.

1. *Transposition preserves conjugacy classes.* By `h4`, for each `z : G` some
   `a : G` has `a z a⁻¹ = zᵀ = τ z` as matrices, hence as units. Since `τ` is an
   involution, `τ.symm z = τ z`, so `τ.symm` also preserves the class of `z`.
2. *An anti-invariant difference.* Put `D' = D - τ_* D`. By
   `IsConjugationInvariant.pushforward_transpose`, `τ_* D` is conjugation
   invariant, so `D'` is too. By `pushforward_transpose_involutive`,
   `τ_* D' = τ_* D - D = -D'`.
3. *Localization.* Apply `h1` with `X = G`, `Y = Fin (n + 1) → F.Carrier` (a
   finite product of copies of the field, hence Hausdorff, locally compact and
   totally disconnected), the continuous map `q`, the index type
   `ι = G ⊕ Unit`, the homeomorphisms `h (inl a) = conjugationHomeomorph a` and
   `h (inr ()) = τ`, and the characters `χ (inl a) = 1` and `χ (inr ()) = -1`.
   The fibres of `q` are preserved by every `h i`, by `charpolyCoeffs_conj` and
   `charpolyCoeffs_transpose`. Step 2 says `pushforward (h i) D' = χ i • D'` for
   every `i`. It remains to prove the fibrewise hypothesis of `h1`.
4. *Each fibre is a closed finite union of conjugacy classes.* Let `y` be a
   point of `Y`. If the fibre `q ⁻¹' {y}` is empty, it is the empty union.
   Otherwise choose `g₀` in it and let `s₀` be the finite set of matrices given
   by `h5` for the characteristic polynomial of `g₀`. Let `s` be the finite set
   of units whose underlying matrix is in `s₀` and whose `q` value is `y`
   (`Finset.preimage` along the injective `Units.val`, then `Finset.filter`).
   If `q g = y`, then `g` and `g₀` have equal characteristic polynomials by
   `charpoly_eq_of_coeff_eq`. So `h5` gives `k` with `k g k⁻¹ ∈ s₀`. This
   conjugate lies in `s`, and `g` is conjugate to it by `k⁻¹`. Conversely,
   conjugates of elements of `s` have `q` value `y` by `charpolyCoeffs_conj`.
   The fibre is closed as the preimage of a point under the continuous `q`.
5. *Vanishing on a fibre.* Let `T` be supported in `q ⁻¹' {y}`, with
   `pushforward (h i) T = χ i • T` for all `i`. The `inl` cases make `T`
   conjugation invariant, and the `inr` case gives `τ_* T = -T`.
   `conjugationInvariant_finiteOrbit_vanishing` applied to `h3`, `σ = τ`, the
   fibre and the set `s` of step 4, with orbit preservation from step 1, gives
   `T = 0`.
6. *Conclusion.* By `h1`, `D' = 0`, that is `D = τ_* D`, which is
   `IsTransposeInvariant (n + 1) F.Carrier D`.

## Relation to the original source

The registered original is Bernstein and Zelevinsky, *Representations of the
group GL(n,F), where F is a non-Archimedean local field (survey)* (1976),
`bernstein-zelevinsky-1976-representations-gln`. Inside the proof of
Theorem 7.3, pp.57–58, the source states this fact and proves it by applying
Theorem 6.13, p.56, to the conjugation action and to `σ = τ`. Its condition d),
p.58, is that transposed matrices are conjugate. Condition a), constructiveness
of the conjugation action, is taken from Sections 6.15–6.16, pp.56–57. Remark
7.4, p.58, says that it can also be verified directly, and leaves this to the
reader.

The implemented proof does not establish constructiveness. It uses the
characteristic polynomial directly. Localization along its coefficients
reduces the claim to single fibres. Finiteness of conjugacy classes with a
given characteristic polynomial makes each fibre a closed finite union of
conjugacy classes. The finite-orbit proposition then takes the place of
Theorems 6.9, p.54, and 6.10, pp.54–55, on that fibre. Since `τ² = id`, the
source's eigen-decomposition of `T` under `σ` in the proof of 6.10 reduces to
the single anti-invariant part `D - τ_* D`. The source's normalization
`a^σ = (aᵀ)⁻¹` is not needed, because the finite-orbit proposition only asks
that `σ` and `σ⁻¹` preserve each orbit in the fibre. No Haar measure, Theorem A,
or rational canonical form is used.

## Compilation, validation and review

- *Compilation.* The module compiles in the project's pinned Lean environment
  (artifact `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`) on top of Library commit
  `00be69b7f127e77ee2fd0511ffe34c48595b64d4`, with no errors and no warnings
  (local checks `1fa05d81` and, for this revision, `af53949f`). Inspecting
  `Langlands.generalLinearConjugationDistributionTranspose` shows a theorem
  with the single universe parameter `uF` that depends only on the axioms
  `propext`, `Classical.choice` and `Quot.sound`. The file contains no `sorry`,
  `admit` or new axiom.
- *Exact-target validation.* The closing theorem's type is the published
  `GeneralLinearConjugationDistributionTransposeStatement.{uF}`, unapplied, and
  the statement module is imported unchanged. The official machine validation
  `0fea65b1-13d2-4fa5-8078-7cab984d8407` checked the earlier candidate
  `14f36f2d-43aa-48c9-bd34-aba864781654`. It passed the Lake build, exact-target,
  unchanged-statement and frozen-input checks. That candidate has the same Lean
  file as this revision (SHA-256
  `a11b9e9cd064248597fd6a76298775d327f4d3849d9e386e8b5529e2eb0ec002`). This
  revision changes only this Markdown file and has been submitted for a fresh
  machine validation, which is pending.
- *Independent acceptance.* Independent review rejected the earlier candidate
  `14f36f2d` (review receipt `8ebc2daa-1a70-4ae6-bc09-b669cb2e068a`). The only
  reason was that this Markdown lacked the present section; the review reported
  no mathematical defect. This revision has not yet been accepted and awaits a
  new independent semantic review.
- *Publication.* The pair has not yet been published. Only an accepted
  candidate is published to the Library, by the Integrator. Until then, this
  pair is an unpublished candidate.
