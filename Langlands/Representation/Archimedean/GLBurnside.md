# Families, representations, Schur's lemma and Burnside's theorem

Module `Langlands.Representation.Archimedean.GLBurnside`, namespace
`Langlands.Archimedean.GLReynolds`. It imports `GLLowestWeight` (families of operators,
stable subspaces) and the Library module `LowerVerma` (the universal enveloping algebra
`VermaGL.glU n` of `𝔤𝔩_n(ℂ)`, its matrix units `VermaGL.unitU n p q`, its center
`VermaGL.center n`, and `VermaGL.HasIntegralWeights`), and the Library module
`Langlands.Algebra.SandwichDimensionBoundProof` (Burnside's theorem for finite-dimensional
simple modules, `SandwichDimensionBound.action_surjective`).

This module is part of a planned proof of Kostant's multiplicity bound
(`VermaGL.KostantMultiplicityStatement`, Library module `LowerVerma`). It contains no Library
statement and proves only the results listed below; no new axioms are used.

## Setting

A family `e : Fin n → Fin n → Module.End ℂ V` with `IsGlFamily e` satisfies the commutation
relations of the matrix units `E_pq` of `𝔤𝔩_n(ℂ)` (see `GLReynolds`). A family is
*irreducible* if every nonzero stable subspace (`IsStable e Z`, see `GLLowestWeight`) is `⊤`;
the theorems below take this as the hypothesis
`hirr : ∀ Z, IsStable e Z → Z ≠ ⊥ → Z = ⊤`.

## Results

### Families and Lie algebra representations

* `famOf σ`: for a Lie algebra representation
  `σ : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ V`, the family `p q ↦ σ(E_pq)`, where
  `E_pq = Matrix.single p q 1`.
* `isGlFamily_famOf`: this family satisfies the relations, because `σ` preserves brackets and
  `E_ab E_cd = δ_bc E_ad` (`single_mul_single_one`).
* `intWeights_famOf`: if `σ` has integral weights (`VermaGL.HasIntegralWeights σ`), then so does
  `famOf σ` (`IntWeights`, see `GLReynolds`). The two definitions agree.
* `lieLin e`, `lieOf e he`: conversely, a family satisfying the relations gives the
  representation `Y ↦ Σ_{p,q} Y_pq e_pq`. Its compatibility with brackets (`lieLin_lie`) is
  checked on matrix units (`Matrix.induction_on'` in both arguments) using the relations.
  `lieOf_single` and `famOf_lieOf` show that `famOf (lieOf e he) = e`.
* `envOf e he : VermaGL.glU n →ₐ[ℂ] Module.End ℂ V`: the action of the universal enveloping
  algebra induced by `lieOf e he` (`UniversalEnvelopingAlgebra.lift`). By `envOf_unitU`, it
  sends `VermaGL.unitU n p q` to `e p q`.

### Schur and Burnside

* `exists_eq_smul_of_commute` (**Schur's lemma**): let `V` be nonzero and finite-dimensional
  and the family irreducible. An operator `T` commuting with every `e_pq` is a scalar.
  Proof: `T` has an eigenvalue `μ` (`Module.End.exists_eigenvalue`, using that `ℂ` is
  algebraically closed). The eigenspace of `μ` is stable and nonzero, hence everything.
* `envOf_surjective` (**Burnside's theorem**): under the same hypotheses every linear operator
  on `V` is `envOf e he u` for some `u ∈ U(𝔤𝔩_n(ℂ))`.
  Proof: make `V` a module over `U` through `envOf` (`Module.compHom`). It is a simple
  `U`-module: a `U`-submodule is a complex subspace (scalars act through `algebraMap`) stable
  under every `e_pq = envOf(unitU p q)`, hence `⊥` or `⊤`. Scalars act compatibly
  (`IsScalarTower ℂ U V`, since `algebraMap c` acts as `c`). The Library's Burnside theorem
  `Langlands.SandwichDimensionBound.action_surjective` (module
  `Langlands.Algebra.SandwichDimensionBoundProof`; Schur's lemma for simple modules plus
  Mathlib's `jacobson_density`) applied to the simple `U`-module `V` and a complex linear
  operator `t` gives `r ∈ U` acting as `t`, i.e. `envOf e he r = t`.
* `exists_envOf_center`, `cScal`, `envOf_center_eq`: a central element `z` of `U` acts by a
  scalar `cScal he hirr z` (Schur's lemma, since `z` commutes with each `unitU n p q`).
* `centChar he hirr : VermaGL.center n →ₐ[ℂ] ℂ`: the central character `z ↦ cScal he hirr z`.
  It is an algebra homomorphism because `envOf` is one and `a • 1 = b • 1` in `End V` forces
  `a = b` when `V` is nonzero (`smul_one_injective`).
* `envOf_center_apply`: `envOf e he z v = centChar he hirr z • v` for central `z`.

Schur's lemma and Burnside's theorem are standard (for example, Lang, *Algebra*, XVII §3). The
proof of Schur's lemma above is the usual eigenvalue argument, stated for operators commuting
with the family `e` rather than for `U`-linear maps; Burnside's theorem is the Library result
cited above, applied after the simple-module construction.
