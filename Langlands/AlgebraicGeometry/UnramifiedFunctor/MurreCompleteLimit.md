# Inverse limits of compatible algebras over a complete local ring

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCompleteLimit`, namespace
`Langlands.AlgebraicGeometry.UnramifiedFunctor.CompleteLocal`. A supporting module of the proof
of Step 2a of Murre's induction (`MurreCompleteLocalStepStatement`). In Murre's outline
(Bourbaki exp. 294, Case I, Step 2a) the representing scheme of `F` over `Spec (R/m^(n+1))` is a
disjoint union of spectra `Spec B_{n,i}`, and `B_i = lim_n B_{n,i}` is "unramified and finite"
over `R`. This module proves the commutative algebra behind that sentence for an abstract tower.

Let `R` be a local noetherian ring complete for its maximal ideal `m`, and `A : ℕ → Type u` a
family of `R`-algebras with `R`-algebra maps `t n : A (n+1) → A n`.

## Definitions

* `limitAlg A t`: the subalgebra of `∀ n, A n` of compatible sequences
  (`t n (x (n+1)) = x n`), the inverse limit.
* `limitProj A t n : limitAlg A t →ₐ[R] A n`, the projections; `limitMk` builds an element from
  a compatible sequence; `limit_ext`, `limitProj_compat`, `limitProj_limitMk` are the basic
  identities.

## Results

Assume every `t n` is surjective with kernel `m^(n+1) A (n+1)` (as `R`-submodule,
`m^(n+1) • ⊤`) and `A 0` is finite over `R`.

* `limit_spec`: the limit is a finite `R`-module, the projections are surjective, and the kernel
  of `limitProj n` is `m^(n+1) • ⊤`. Proof: the ported Anthropic FLT theorem
  `AdicCompletion.exists_module_finite_forall_comp_eq_and_ker_eq_pow_smul_top_of_forall_surjective`
  gives an `R`-module `L`, finite over the completion `R̂`, with compatible surjections
  `p n : L → A n` such that `L` is separated and complete for the tower and
  `ker (p n) = m^(n+1) • ⊤`. The map `x ↦ (p n x)_n` is an `R`-linear bijection
  `L ≃ limitAlg A t`. Since `R` is complete, `R → R̂` is surjective
  (`AdicCompletion.of_surjective`), so `R̂` and hence `L` are finite over `R`
  (`Module.Finite.trans`). The kernel of `limitProj n` is the image of `ker (p n)` under the
  bijection, and the image of `m^(n+1) • ⊤` is `m^(n+1) • ⊤` (`Submodule.map_smul''`).
* `limit_ker_eq`: the same kernel as an ideal: `ker (limitProj n) = (m · limit)^(n+1)`
  (`Ideal.smul_top_eq_map`, `Ideal.map_pow`).
* `limit_isAdicComplete`: the limit is complete for the ideal `J = m · limit`. Separated: an
  element of every `J^(n+1)` has all projections zero. Complete: for a Cauchy sequence `f`, the
  sequence `k ↦ limitProj k (f (k+1))` is compatible, and its element is a limit of `f`.

Assume moreover that `A 0` is a field (`h0`).

* `limit_isMaximal`: `J = ker (limitProj 0)` is maximal, the quotient being `A 0`.
* `limit_isLocalRing`: the limit is local. `J` is contained in the Jacobson radical because the
  limit is `J`-adically complete (`IsAdicComplete.le_jacobson_bot`), so `J` is contained in, hence
  equal to, every maximal ideal.
* `limit_maximalIdeal`: the maximal ideal is `J = m · limit`.
* `limit_formallyUnramified`: if `A 0` is formally unramified over `R`, so is the limit. By
  Mathlib's `Algebra.FormallyUnramified.of_map_maximalIdeal` it suffices that the maximal ideal is
  `m · limit` (previous item) and that the residue field extension is separable. The projection
  to the field `A 0` is a local homomorphism and induces an algebra map from the residue field of
  the limit to the residue field of `A 0`, which is separable over the residue field of `R`
  (Mathlib's instance for formally unramified local algebras essentially of finite type);
  separability descends along this map (`Algebra.IsSeparable.of_algHom`).
* `limit_isNoetherianRing`: the limit is noetherian, being finite over the noetherian `R`.
