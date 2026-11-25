# Complements of submodules of tempered complex standard modules

Lean module: `Langlands.Representation.Archimedean.ComplexTemperedComplement`.

This module was written for the proof of
`ComplexStandardLanglandsQuotientStatement`. That proof (the reduction
`complexBlockLanglandsQuotient`) takes as a hypothesis the Library statement
`ComplexTemperedStandardIrreducibleStatement` (written U below): the complex standard modules whose
exponents all have the same real part are irreducible. The Library proves U as
`complexTemperedStandardIrreducible` (module `ComplexTemperedStandardIrreducibleProof`). This
module supplies supporting lemmas for U. It proves that every
`(𝔤𝔩_n(ℂ), U(n))`-submodule has a stable complement. From this it derives U from each of three
statements that are only stated here: `ComplexTemperedEndScalarStatement`,
`ComplexTemperedCommonVectorStatement` and `ComplexTemperedJacquetUniqueStatement` (statements
2, 3 and 5 below). Separately, it proves the conditional criterion
`ComplexTemperedCyclicVectorStatement` (statement 4): a module with a nonzero cyclic vector whose
image under every `U(n)`-endomorphism is a multiple of itself is irreducible. The criterion does
not by itself give U. To use it for U one must still construct, for each tempered list, a nonzero
vector that is cyclic and has this scalar-image property; this module constructs no such vector.
The proof of U takes this form: `complexTemperedIrreducible_of_minorMonomial` (module
`ComplexLowestKTypeMultOne`) applies `complexTemperedCyclicVector` to a cyclic vector whose
`U(n)`-type occurs once.

## Notation

* `GL_n(ℂ)` is `Langlands.GeneralLinear n ℂ`. `U(n)` is `unitaryCompact ℂ n`, with Haar
  probability measure `ComplexDuality.unitaryHaar n`.
* `X(ds)` is `KF n ds` (`ComplexPermutation`), the space of `U(n)`-finite functions of
  `complexStandardModule n ds`.
* `ρ = complexStandardRep n ds` is right translation by `Matrix.unitaryGroup (Fin n) ℂ`, and
  `R = complexStandardLie n ds` is the action of `ℂ ⊗[ℝ] 𝔤𝔩_n(ℂ)`. For `X ∈ 𝔤𝔩_n(ℂ)`, `R(1 ⊗ X)` is
  the right derivative along `X`.
* A *`(𝔤, K)`-submodule* is a subspace stable under every `ρ(k)` and every `R(Z)`.
* `B = ComplexPermutation.unitaryForm n ds` is the form `B(f, h) = ∫_{U(n)} f(k) conj(h(k)) dk`.
  The Library shows it is `ρ`-invariant (`unitaryForm_invariant`) and positive definite
  (`unitaryForm_self_eq_zero`).
* The *tempered hypothesis* on `ds`: `ds.length = n` and
  `∀ d ∈ ds, ∀ e ∈ ds, d.exponent.re = e.exponent.re`.

Unprefixed names below are in the namespace `Langlands.Archimedean.ComplexTemperedComplement`.

## Statements

All five statements quantify over `n`, over lists `ds` satisfying the tempered hypothesis, and
over the data named below.

1. `ComplexTemperedComplementStatement`: every `(𝔤, K)`-submodule `W` of `X(ds)` has a complement
   `W'` that is also a `(𝔤, K)`-submodule, with `IsCompl W W'`.
   Proved as `Langlands.Archimedean.complexTemperedComplement`.
2. `ComplexTemperedEndScalarStatement`: every linear endomorphism `E` of `X(ds)` that commutes
   with every `ρ(k)` and every `R(Z)` is a scalar (`∃ c, ∀ f, E f = c • f`). This is only
   stated. `complexTemperedIrreducible_of_endScalar` proves
   `ComplexTemperedEndScalarStatement → ComplexTemperedStandardIrreducibleStatement`.
3. `ComplexTemperedCommonVectorStatement`: there is `f₀ ≠ 0` in `X(ds)` that lies in every
   nonzero `(𝔤, K)`-submodule. This is only stated. `complexTemperedIrreducible_of_commonVector`
   proves `ComplexTemperedCommonVectorStatement → ComplexTemperedStandardIrreducibleStatement`.
4. `ComplexTemperedCyclicVectorStatement`: take `f₀ ≠ 0` in `X(ds)` with two properties. First,
   `f₀` is cyclic: every `(𝔤, K)`-submodule containing `f₀` is `⊤`. Second, every linear
   endomorphism `E` of `X(ds)` that commutes with every `ρ(k)` satisfies `E f₀ = c • f₀` for some
   `c`. Then `(ρ, R)` is irreducible (`IsIrreducibleGKModule`). Proved outright as
   `Langlands.Archimedean.complexTemperedCyclicVector`.
5. `ComplexTemperedJacquetUniqueStatement`: let `ℓ : X(ds) → ℂ` be linear and satisfy
   `IsComplexJacquetFunctional n R ℓ a b` with `a_j = κ_j(1)` and `b_j = κ_j(i)`, where
   `κ = ComplexSwapJacquet.kappa ds hn`. Explicitly, `κ_j(1) = 2 t_j + (n - 1) - 2j` and
   `κ_j(i) = i l_j`, where `t_j` is the exponent and `l_j` the weight of the `j`-th character
   of `ds`. These are the exponents of evaluation at `1`. Then `ℓ = c • ev₁` for some `c`, where
   `ev₁ = kFiniteEval (complexStandardModule n ds) 1`. This is only stated.
   `complexTemperedEndScalar_of_jacquetUnique` proves
   `ComplexTemperedJacquetUniqueStatement → ComplexTemperedEndScalarStatement`.

The second property in statement 4 holds whenever `f₀` lies in a `U(n)`-isotypic component that
is irreducible, that is, of multiplicity one. Schur's lemma then makes every `U(n)`-endomorphism a
scalar on that component. For principal series this is the expected use with the lowest
`U(n)`-type. Statement 4 itself does not use these facts: they appear only in its hypotheses.

Provenance. These are derived, internal reductions; no literature statement is claimed. U is
Badulescu–Renard 2010, Theorem 3.1 with §9.1, as the Library's
`ComplexTemperedIrreducibleStatement` module records. Statements 2, 3 and 5 are standard
consequences of that irreducibility. Under U, Schur's lemma gives statement 2 and any nonzero
vector serves in statement 3. Statement 5 follows by Casselman–Frobenius reciprocity:
Jacquet functionals with the exponents of `ev₁` correspond to `(𝔤, K)`-maps `X(ds) → X(ds)`.
This module proves none of these converse directions. The complement theorem is the usual
argument for unitarizable modules, carried out with the form `B` on `U(n)`. `B` is not
`𝔤`-invariant when the common real part `r` of the exponents is nonzero. It is invariant up to a
scalar multiple of `B`, which still makes `W^⊥` stable.

## Definitions

* `orth B U`: the vectors `x` with `B x y = 0` for every `y ∈ U` (any sesquilinear `B`).
* `orthProj B hBpos V`: for positive definite `B` and finite-dimensional `V`, the orthogonal
  projection onto `V`. It sends `x` to the unique `p ∈ V` with `x - p ∈ orth B V`.
* `saturation ρ h`: the sum of the ranges of all `ρ`-equivariant linear maps from the orbit span
  `FiniteVectors.orbitSpan ρ h` into the space. The space of such maps is
  `ComplexPermutation.eqvHom`.
* `detWeight c g = ((|det g|²)^c : ℝ)`, viewed in `ℂ`.
* `dualPartner r h g = detWeight (-(2r)) g · conj (h g)`, that is, `|det g|^{-4r} conj(h(g))`.

## Proof

### Abstract part (section `Abstract`)

Fix a group `G` acting on a complex vector space by `ρ`, a sesquilinear form `B`, a linear
functional `ev`, and these hypotheses:

* `hBinv`: `B` is `ρ`-invariant.
* `hBpos`: `B x x = 0 → x = 0`.
* `hsep`: if `ev (ρ g w) = 0` for all `g`, then `w = 0`.
* `hfin`: every vector is a finite vector.

The lemmas:

* `mem_orth_of_basis`: orthogonality to a basis of a finite-dimensional `V` gives orthogonality
  to `V`.
* `orth_invariant`: `orth B U` is invariant if `U` is.
* `inf_orth_eq_bot`: `U ⊓ orth B U = ⊥`, by positivity.
* `exists_orthProj`, `orthProj_unique`: existence and uniqueness of orthogonal projections. The
  map `v ↦ (B v bᵢ)ᵢ` from `V` to `ℂ^{dim V}` is injective by positivity, hence surjective. The
  projection of `x` is the preimage of `(B x bᵢ)ᵢ`.
* `orthProj_equivariant`: the projection onto an invariant `V` is equivariant, by uniqueness.
* `self_mem_saturation`, `map_mem_saturation`: `h ∈ saturation ρ h`, and the saturation is stable
  under every equivariant endomorphism of the whole space.
* `finiteDimensional_saturation`: the saturation is finite-dimensional. The space of equivariant
  maps out of the finite-dimensional orbit span is finite-dimensional
  (`ComplexPermutation.finiteDimensional_eqvHom`, which uses `hsep`). So the saturation is
  contained in the sum of the ranges of a basis of that space.
* `sup_orth_eq_top`: `U ⊔ orth B U = ⊤` for every invariant `U`. Given `h`, let `S` be its
  saturation and `u` the orthogonal projection of `h` onto the finite-dimensional `U ⊓ S`. To see
  that `h - u ⊥ U`, take `f ∈ U`. Let `P` be the orthogonal projection onto the orbit span
  `V ⊆ U` of `f`; it is equivariant. Then `P(h - u) ∈ U ⊓ S`, so `B(h - u, P(h - u)) = 0`. Hence
  `B(P(h - u), P(h - u)) = 0` and `P(h - u) = 0`. Therefore `B(h - u, f) = 0`. No isotypic
  decomposition is used.
* `isCompl_orth`: `IsCompl U (orth B U)`.

### Calculus on `GL_n(ℂ)` (section `Calculus`)

* `detWeight_mul`, `detWeight_unitary` (`= 1` on `U(n)`), `detWeight_borel`: `detWeight c` takes
  the value `∏ᵢ (|aᵢ|²)^c` on `diag(a) · u` with `u` upper unipotent.
* `contMDiff_detWeight`: smoothness.
* `rightDerivative_mul_fun`: the product rule for right derivatives, through the extension to
  all matrices (`unitsExtension`) and `fderiv_fun_mul`.
* `contMDiff_conj`, `rightDerivative_conj`: right derivatives are real derivatives, so they
  commute with `conj` (`fderiv_star`).
* `rightDerivative_detWeight`: `R_X detWeight c` at `k` equals `detWeight c k` times its value at
  `1`, by left multiplicativity (`rightDerivative_mul_left_of_eq`).

### The tempered standard module (section `Concrete`)

* `exists_mem_exponent`, `re_exponent`: under the tempered hypothesis, every
  `complexPositionExponent ds l` with `l < n` has the real part `r` of the one at index `0`.
* `dualPartner_mem`: if `h ∈ complexStandardModule n ds`, then `dualPartner r h` lies in
  `principalSeries ℂ n (dualChar (complexPositionCharacter ds))`. It is smooth by the product
  rule. Its equivariance comes from `detWeight_borel` and
  `ComplexDuality.normSq_mul_star_principalSeriesCharacter`. That lemma gives
  `(|a|²)^{-2 Re e} conj χ(a) = χ(a)⁻¹`. The common real part lets one product over `i` replace
  the per-index exponents.
* `unitaryForm_lie_add`: for `f, h ∈ X(ds)` and `X ∈ 𝔤𝔩_n(ℂ)`,
  `B(R(X) f, h) + B(f, R(X) h) = -c_X · B(f, h)`, where `c_X` is the right derivative of
  `detWeight (-(2r))` at `1` along `X`.
  `ComplexDuality.integral_rightDerivative_mul_add_eq_zero` is the infinitesimal invariance of the
  pairing between the principal series of `χ` and of `χ⁻¹`. Apply it to `f` and to
  `P = dualPartner r h`. On `U(n)`, `P = conj h`. By the product rule and
  `rightDerivative_detWeight`, `R_X P = c_X conj h + conj(R_X h)` there. Splitting the integral
  gives the identity.
* `orth_lie_mem`: if `W` is stable under `R`, then so is `orth B W`. By `TensorProduct.inductionOn`
  it suffices to treat `Z = z ⊗ X`, and `R(z ⊗ X) = z • R(1 ⊗ X)`. Then for `x ⊥ W` and `y ∈ W`,
  `unitaryForm_lie_add` gives `B(R(X) x, y) = -c_X B(x, y) - B(x, R(X) y) = 0`.
* `isComplexJacquetFunctional_eval_comp`: for an `R`-equivariant `E`, `ev₁ ∘ E` is a Jacquet
  functional with exponents `κ(1)`, `κ(i)`. Use
  `ComplexSwapJacquet.rightDerivative_one_strictUpper` and
  `ComplexSwapJacquet.rightDerivative_one_diag` applied to `E v`.
* `projection_comm`: the projection `W.projection W' hc` along a complement commutes with every
  endomorphism that preserves both `W` and `W'`.

### The theorems

* `complexTemperedComplement`: take `W' = orth B W`. It is `ρ`-stable by `orth_invariant` and
  `R`-stable by `orth_lie_mem`. `IsCompl` follows from `isCompl_orth` with `ev = ev₁`, using
  `kFiniteEval_one_separating` and `isFiniteVector_complexStandardRep`.
* `complexTemperedIrreducible_of_endScalar`: the projection onto `W` along the stable complement
  `W'` commutes with `ρ` and `R` (`projection_comm`), so it is `c • id`. If `c = 0`, then
  `W' = ⊤` and `W = ⊥`. Otherwise every `f` equals `c⁻¹ • P f ∈ W`. Nontriviality of `X(ds)` is
  `complexStandardNontrivial`.
* `complexTemperedIrreducible_of_commonVector`: if `W ≠ ⊥` and `W' ≠ ⊥`, then `f₀ ∈ W ⊓ W' = ⊥`,
  a contradiction. So `W = ⊥`, or `W' = ⊥` and `W = ⊤`.
* `complexTemperedCyclicVector`: the projection `P` onto `W` along `W'` commutes with `ρ`, so
  `P f₀ = c f₀`. If `c = 0`, then `f₀ ∈ W'`; cyclicity gives `W' = ⊤`, so `W = ⊥`. Otherwise
  `f₀ = c⁻¹ P f₀ ∈ W`, and cyclicity gives `W = ⊤`.
* `complexTemperedEndScalar_of_jacquetUnique`: by `isComplexJacquetFunctional_eval_comp` and the
  hypothesis, `ev₁ ∘ E = c • ev₁`. For every `k`,
  `ev₁(ρ(k)(E f - c f)) = ev₁(E(ρ(k) f)) - c ev₁(ρ(k) f) = 0`, using that `E` commutes with
  `ρ(k)`. So `E f = c f` by `kFiniteEval_one_separating`.

The module has no `sorry` and adds no axioms.

The abstract orthogonal-complement, saturation and projection declarations
are implemented once in `GKModuleOrthogonal`, imported here with their original
`ComplexTemperedComplement` names and unchanged mathematical definitions.
