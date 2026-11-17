# From the Lie algebra to `U(n)`, and the spherical vector

Lean module: `Langlands.Representation.Archimedean.ComplexSphericalLieGroup`.

Worker 5677 wrote this module, with Worker 728 as coauthor. It is part of Task 7064
(`e4a22cc7-0a28-44a3-afc6-38bb7c243851`): pieces (a) and (b) of step M4 of Worker 728's route
to the Library statement `ComplexTemperedStandardIrreducibleStatement`. Worker 728 fixed the
interface of both pieces. Piece (a) passes from the Lie algebra to the group for linear maps out
of a finite-dimensional `U(n)`-representation. Piece (b) gives a `U(n)`-fixed vector with
value `1` at the identity in the standard module of weight-zero characters.

Notation. `U(n)` is `Matrix.unitaryGroup (Fin n) ℂ`. A `(𝔤𝔩_n(ℂ), U(n))`-module on a complex
vector space `V` is a pair `(ρ, π)` of a representation `ρ` of `U(n)` and a Lie algebra map
`π : ℂ ⊗_ℝ 𝔤𝔩_n(ℂ) → End V` satisfying the Library predicate `IsComplexGKModule n ρ π`. Among
other conditions, that predicate requires: for every curve `γ` in `U(n)` with `γ(0) = 1` whose
entries have derivatives `X i j` at `0`, and every `v ∈ V` and linear functional `ℓ` on `V`, the
function `t ↦ ℓ(ρ(γ t) v)` has derivative `ℓ(π(1 ⊗ X) v)` at `0`.

For a list `ds` of complex characters, `X(ds)` is the space of `U(n)`-finite functions of
`complexStandardModule n ds` (the principal series of the position characters
`complexPositionCharacter ds i`). `U(n)` acts on it by `complexStandardRep n ds` (right
translation), and `kFiniteEval (complexStandardModule n ds) 1` evaluates a function at the
identity matrix.

## The statement

`Langlands.Archimedean.ComplexSphericalLieGroupStatement` (universe parameters `uV`, `uF`) is the
conjunction of the following two claims.

1. **Lie algebra to group.** Let `n ∈ ℕ`, and let `(ρ, π)` be a `(𝔤𝔩_n(ℂ), U(n))`-module on `V`
   (`V` in universe `uV`). Let `F` be a finite-dimensional complex vector space (universe
   `uF`), `σ` a representation of `U(n)` on `F`, and `σ' : M_n(ℂ) → End F` any function. Assume
   `hσ`: for every curve `γ : ℝ → U(n)` with `γ(0) = 1` whose entries have derivatives `X i j`
   at `0` for a skew-Hermitian matrix `X` (`star X = -X`), every `w ∈ F` and every linear
   functional `ℓ` on `F`, the function `t ↦ ℓ(σ(γ t) w)` has derivative `ℓ(σ'(X) w)` at `0`.
   Let `ψ : F → V` be linear with `ψ(σ'(Y) w) = π(1 ⊗ Y)(ψ w)` for every skew-Hermitian `Y` and
   every `w ∈ F`. Then `ψ(σ(k) w) = ρ(k)(ψ w)` for every `k ∈ U(n)` and every `w ∈ F`.

   No linearity, bracket or continuity condition on `σ'` is assumed; only its values on
   skew-Hermitian matrices matter.

2. **Spherical vector.** Let `n ∈ ℕ` and let `ds` be a list of complex characters with
   `d.weight = 0` for every `d ∈ ds`. Then there is `T ∈ X(ds)` with
   `complexStandardRep n ds k T = T` for every `k ∈ U(n)` and `T(1) = 1`.

It is proved here as `Langlands.Archimedean.complexSphericalLieGroup`, with no hypotheses.

Provenance. These are internal lemmas of the tempered-irreducibility route. Claim 1 is the
standard fact that on a connected compact group a Lie algebra intertwiner between a
finite-dimensional representation and a `K`-finite module is a group intertwiner. Claim 2 is
the standard existence of the spherical vector in an unramified principal series. The exact
formulation (the derivative hypothesis `hσ` modelled on `IsComplexGKModule`, and evaluation
through `kFiniteEval`) is ours.

## Further exported results (namespace `Langlands.Archimedean.ComplexSphericalLieGroup`)

* `exists_skew_exp_eq`: every unitary matrix `u` equals `NormedSpace.exp Y` for a
  skew-Hermitian `Y`.
* `exists_skewExp_eq`: every `k ∈ U(n)` equals `skewExp Y hY` (Library, `ComplexJacquetTorus`)
  for some skew-Hermitian `Y`.
* `hasDerivAt_shift`: for a representation `σ` of `U(n)` on `F`, a skew-Hermitian `Y` and a map
  `D : F → F`, if `t ↦ ℓ(σ(exp(tY)) w)` has derivative `ℓ(D w)` at `0` for every `w` and every
  linear functional `ℓ`, then it has derivative `ℓ(σ(exp(sY)) D w)` at every `s`.
* `eq_zero_of_hasDerivAt_vecMul`: if `r : ℝ → ℂ^m` satisfies `r'(t) = r(t) A` (row vector times
  matrix) for every `t` and `r(0) = 0`, then `r = 0`.
* `map_rho_skewExp_of_map_pi`: claim 1 for `k = skewExp Y hY`.
* `map_rho_of_map_pi`: claim 1.
* `complexPositionCharacter_phaseUnit`, `principalSeriesCharacter_phaseUnit`: if every
  character of `ds` has weight `0`, then the position characters of `ds`, and the
  principal-series character of `complexPositionCharacter ds`, take the value `1` on
  `phaseUnit` arguments (complex numbers of absolute value `1`).
* `exists_spherical`: claim 2.

## Proof

**Exponentials.** `exists_skew_exp_eq` uses the continuous functional calculus of the
C⋆-algebra `M_n(ℂ)` (with the `L²` operator norm, scope `Matrix.Norms.L2Operator`). A unitary
`u` is normal, with finite spectrum (`Matrix.finite_spectrum`), so every function is continuous
on its spectrum. Put `Y = cfc (z ↦ i · arg z) u`. Then `star Y = cfc (z ↦ −i · arg z) u = −Y`
(`cfc_star`, `cfc_neg`, `cfc_congr`). By `CFC.exp_eq_normedSpace_exp` and `cfc_comp'`,
`exp Y = cfc (z ↦ exp(i · arg z)) u`. On the spectrum, `‖z‖ = 1`
(`spectrum.norm_eq_one_of_unitary`), so `i · arg z = log z` and `exp(log z) = z`. Hence
`exp Y = cfc id u = u`. `exists_skewExp_eq` restates this in `U(n)`.

**Lie algebra to group.** Fix a skew-Hermitian `Y` and put `k(t) = skewExp (tY)`. For a linear
functional `μ` on `V` and `x ∈ F`, let `D_t(μ)(x) = μ(ψ(σ(k t) x)) − μ(ρ(k t)(ψ x))`.

* Derivative. `t ↦ μ(ψ(σ(k t) x))` has derivative `μ(ψ(σ(k s) σ'(Y) x))` at `s`. This follows
  from `hσ` applied to the curve `k` (`skewExp_zero_smul`, `hasDerivAt_skewExp_entry`) and the
  shift lemma `hasDerivAt_shift`. By the Library lemma `hasDerivAt_skewExp` (from
  `IsComplexGKModule`), `t ↦ μ(ρ(k t)(ψ x))` has derivative `μ(ρ(k s) π(1 ⊗ Y)(ψ x))` at `s`,
  and `π(1 ⊗ Y)(ψ x) = ψ(σ'(Y) x)` by the hypothesis on `ψ`. Hence `D_t(μ)(x)` has
  derivative `D_s(μ)(σ'(Y) x)` at `s`.
* Initial value. `k(0) = 1`, so `D_0(μ) = 0`.
* ODE. Choose a basis `b` of `F` (`Module.finBasis`) and let `A` be the matrix of `σ'(Y)`, with
  entries `A i j = b.repr(σ'(Y) b_j) i`. The row vector `r(t)_j = D_t(μ)(b_j)` satisfies
  `r' = r A`, because `D_t(μ)(σ'(Y) b_j) = ∑_i D_t(μ)(b_i) A i j`. It also satisfies
  `r(0) = 0`. `eq_zero_of_hasDerivAt_vecMul` gives `r = 0`. It is proved from Mathlib's
  `ODE_solution_unique_univ` with the Lipschitz vector field `x ↦ x A`. Hence `D_t(μ) = 0` for
  every `t` (`Basis.ext`).
* Conclusion. At `t = 1`, `k(1) = skewExp Y`. Then `μ(ψ(σ(k 1) w) − ρ(k 1)(ψ w)) = 0` for every
  `μ`, so the vector vanishes (`Module.forall_dual_apply_eq_zero_iff`). This is
  `map_rho_skewExp_of_map_pi`. `map_rho_of_map_pi` follows from `exists_skewExp_eq`.

**Spherical vector.** If all weights are `0`, every `complexPositionCharacter ds l` is `1` on
`phaseUnit z`: this is proved by induction on `ds` from `ComplexCharacterData.character_eq` and
`norm_phaseUnit`. The constant function `1` on `U(n)` is therefore continuous, has
finite-dimensional span of right translates, and satisfies the equivariance condition of the
Library theorem `complexPrincipalSeriesExtension` (module `ComplexPrincipalSeriesExtension`).
That theorem gives `f ∈ X(ds)` with `f(κ) = 1` for every `κ ∈ U(n)`. Hence `f(1) = 1`. For
`k ∈ U(n)`, the right translate of `f` by `k` lies in the principal series
(`rightTranslation_mem_principalSeries`). The translate agrees with `f` on `U(n)`, since both
are `1` there. By the Library lemma `ComplexPrincipalSeriesExtension.eq_of_eqOn_unitary` (two functions in the
same principal series that agree on `U(n)` are equal), the translate equals `f`. Hence
`complexStandardRep n ds k f = f`.
