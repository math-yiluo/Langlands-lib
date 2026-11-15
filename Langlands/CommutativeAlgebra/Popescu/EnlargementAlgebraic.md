# The algebraic case of the unit enlargement

Namespace `Langlands.CommutativeAlgebra.Popescu.Enlargement`. All proofs are complete and use only
the standard axioms.

- `isMaximal_map_adjoinRoot`: if `H ∈ D[X]` reduces to an irreducible polynomial over `κ_D`, then
  `𝔪_D · D[X]/(H)` is maximal. The quotient is `κ_D[X]/(H̄)`
  (`AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot`), which is a field.
- `isLocalRing_adjoinRoot`: if moreover `𝔪_D` is nilpotent, `D[X]/(H)` is local. Every maximal
  ideal contains the nilpotent ideal `𝔪_D · D[X]/(H)`, which is itself maximal.
- `residue_aeval`: for a local `D → L`, `res(F(x)) = F̄(x̄)`.
- `caseA`: the enlargement when the residue `α` of the unit `ℓ` is algebraic over `κ_D`. It is
  stated for an algebra `D → L` (local, flat) with `ψ = IsScalarTower.toAlgHom k D L`.
  1. A `p`-power `β = α^{p^n}` is separable over `κ_D`. The minimal polynomial of `α` is
     `g(X^{p^n})` with `g` separable (`exists_separable_of_irreducible`), so `g(β) = 0`.
  2. Take a monic lift `H ∈ D[X]` of the minimal polynomial of `β`. Hensel's lemma in the
     complete local ring `L` gives a root `θ` of `H` lifting `β`.
  3. Set `D' = D[X]/(H)`. It is local with `𝔪_D D' = 𝔪_{D'}` (the lemmas above), finite over
     `D` (power basis), hence Artinian, and essentially of finite type over `k`. Its map to `L`
     is `root ↦ θ`. That map is local, and `L` is flat over `D'` by `flat_of_map_maximalIdeal`.
  4. `u = w^p`, from `exists_pth_power_preimage` with `x = root`, `e = p^n`. Then `ψ'(u) = ℓ^Q`
     and `dū = 0`.
  5. `κ_{D'} = κ_D(γ)`, `γ = res(root)`, is separable over `κ_D`, since `γ` is a root of the
     separable minimal polynomial of `β`. So it is formally étale, and the images of the basis
     `d(b̄_i)` form a basis of `Ω_{κ_{D'}/k}` (`kaehler_basis_of_formallyEtale`). Here `r = 0`.
