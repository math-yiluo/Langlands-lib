# Joint admissibility from an energy-controlled separation property

Module: `Langlands.Automorphic.CuspidalAdmissible.AdmissibilityReduction`. Provenance:
internal. This is the algebraic skeleton of the proof of joint admissibility of unitary
cuspidal realizations (Harish-Chandra finiteness): the analytic input is isolated as a
separation property.

- `finiteDimensional_of_separating E lam h`: a subspace on which finitely many linear
  functionals `lam p` separate points (`∀ p, lam p e = 0 → e = 0`) is finite-dimensional
  (it injects into `Fin P → ℂ`).
- `finiteDimensional_of_forall_mem E hE M hM`: linear maps `ℂ^m → V` with values in a
  finite-dimensional `E` form a finite-dimensional space (evaluation at the standard basis is
  injective into `Fin m → E`).
- `imageSpan ρ κ L σ`: the span of all values `φ v` of maps `φ` in the Library's
  `jointMultiplicitySpace ρ κ L σ`; `imageSpan_le_fixedVectors` (it consists of `L`-fixed
  vectors) and `imageSpan_le_ker` (it is killed by any operator killing every `φ v`).
- `isJointlyAdmissible_of_separating hS b H`: let `S` be irreducible with a unitary form `b`
  and suppose that for every open subgroup `L` and constant `C` there are finitely many
  functionals separating the `L`-invariant `e` with `energy b e ≤ C · re b(e, e)`. Then
  `S.IsJointlyAdmissible`. Proof: for given `L`, `m`, `σ`, take `q` from
  `exists_casimir_annihilator` (irreducibility) and `p` from
  `exists_compactCasimir_annihilator S σ`; every vector of `imageSpan` is `L`-fixed and
  killed by `q(Ω)` and `p(Ω_K)`, hence satisfies the energy bound `energy_le` with
  `C = rootBound q + 2 rootBound p`. The separation property makes `imageSpan`
  finite-dimensional, and the multiplicity space maps injectively into maps with values there.
