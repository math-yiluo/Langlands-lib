# Finite action quotients of central subgroups

This module collects elementary facts about the action quotient
`actionQuotient ρ = ℂ[B] ⧸ ker(ℂ[B] → End V)` of a representation `ρ` of a commutative
group `B` (namespace `Langlands.PQFiniteActionRegularity`). These facts feed the spectral
criterion `pqRegularity_of_disjoint_generalizedCharacters`, which needs finite-dimensional
action quotients. The provenance is internal. These are standard linear-algebra steps used
in the proof of Renard VII.3, and the module makes no literature claim of its own.

All declarations are in the namespace `Langlands.CentralActionQuotient`.

- `groupAlgebraKernel_le_of_jointlyInjective`: let `F x : ρ → σ` be a family of
  `B`-equivariant maps that is jointly injective, meaning `F x v = 0` for every `x`
  forces `v = 0`. Then every group-algebra element that kills `σ` also kills `ρ`. The
  proof uses `intertwining_groupAlgebra_apply`: the element commutes with each `F x`.
- `finite_actionQuotient_of_kernel_le`: if `ker ρ ≤ ker σ` in `ℂ[B]` and `ρ` has a
  finite action quotient, then so does `σ`. The proof uses the surjection
  `Ideal.Quotient.factorₐ`.
- `finite_actionQuotient_of_scalar`: if `ρ b = c b • 1` for every `b`, the action quotient
  is finite. The span of the image of `ρ` lies in the line `ℂ · 1`, and
  `finite_actionQuotient_of_finite_span` applies.
- `eq_of_isGeneralizedEigencharacter_of_scalar`: if `ρ` acts through the scalar character
  `c`, the only generalized eigencharacter is `c`. A witness `v ≠ 0` with
  `(ρ b − χ b)^k v = 0` gives `(c b − χ b)^k v = 0`, so `c b = χ b`.
- `finite_generalizedEigencharacters`: a finite action quotient has only finitely many
  generalized eigencharacters. Each one factors through an algebra map
  `actionQuotient ρ →ₐ[ℂ] ℂ` (`PQKernelCharacters.kernel_le_characterKernel`). That map
  determines the character on group elements. A finite-dimensional algebra has finitely
  many such maps (`FiniteActionSpectrum.finite_algHom`).
- `finite_actionQuotient_of_locallyFinite`: let `ρ` be a representation of a group `H`, and
  let `ι : B →* H` take values in the center of `H`. Suppose `ρ` is finitely generated
  over `ℂ[H]` and every vector lies in a finite-dimensional `B`-stable subspace. Then
  `ρ ∘ ι` has a finite action quotient. The proof takes a finite generating set `S` and
  the finite-dimensional `B`-stable subspace `U₀` spanned by the subspaces through the
  generators. It shows that the `B`-action kernel on `ρ` equals the kernel of the action
  on `U₀`. An element killing `U₀` gives the `H`-equivariant central operator
  `centralGroupAlgebraAction ρ ι hι c`, which kills the generators and so kills all of
  `ρ`. The action quotient then embeds in `End U₀` (`Ideal.kerLiftAlg_injective`).
