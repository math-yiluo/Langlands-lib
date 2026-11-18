# Injectivity of coefficient tensor maps of irreducible admissible representations

Module `Langlands.Representation.Plancherel.CoefficientTensorInjectivity`,
namespace `Langlands.Plancherel`.

## Statements

Let `G` be a topological group, `V` a complex vector space and `ρ` a
representation of `G` on `V` that is admissible (`IsAdmissible ρ`) and
irreducible (`ρ.IsIrreducible`, Mathlib's notion).

- `exists_asAlgebraHom_eq ρ ha hi f s`: for every complex linear map
  `f : V →ₗ[ℂ] V` and every finite set `s` of vectors, there is an element
  `r` of the group algebra `MonoidAlgebra ℂ G` whose action
  `ρ.asAlgebraHom r` agrees with `f` on `s`. This is the Jacobson density
  theorem in the form needed here.
- `coefficientTensorMap_injective A ha hi`: for an admissible irreducible
  smooth complex representation `A` (a `SmoothRep` at field universe `0`),
  the Library's coefficient tensor map
  `coefficientTensorMap A : A ⊗[ℂ] SmoothDual A.representation → LocallyConstant G ℂ`,
  `v ⊗ ℓ ↦ (g ↦ ℓ(π(g) v))`, is injective.

## Provenance

These are standard facts of representation theory: the Jacobson density
theorem, and linear independence of matrix coefficients of an irreducible
representation with scalar commutant. The Lean formulation for the Library's
`coefficientTensorMap` and the proof below are internal. No literature
statement is formalized.

## Proof

`exists_asAlgebraHom_eq`. Irreducibility makes `ρ.asModule` a simple module
over `MonoidAlgebra ℂ G` (Mathlib `irreducible_iff_isSimpleModule_asModule`).
Every group-algebra endomorphism `φ` of this module, restricted to complex
scalars, is an intertwining endomorphism of `ρ`. The group element `g` acts
as `MonoidAlgebra.of ℂ G g` (`asModuleEquiv_map_smul`, `asAlgebraHom_of`).
By the Library's admissible Schur lemma `admissibleSchur_scalarEndomorphism`,
`φ` is a scalar `c`. Hence `f (φ m) = c • f m = φ (f m)`, so `f` is linear
over the endomorphism ring of the module. Mathlib's `jacobson_density`
(simple modules are semisimple) then gives `r` with `f m = r • m` for all
`m ∈ s`, and `r • m = ρ.asAlgebraHom r m` by definition of the module
structure.

`coefficientTensorMap_injective`. Take a basis `b` of `V`
(`Module.Basis.ofVectorSpace`) and write a kernel element as
`t = ∑ i, b i ⊗ c i` with finitely supported `c`
(`TensorProduct.eq_repr_basis_left`). For every group-algebra element `r`,
`∑ i ∈ c.support, (c i)(ρ.asAlgebraHom r (b i)) = 0`. Induct on `r`
(`MonoidAlgebra.induction_linear`): on `single g a` the sum is `a` times
the value of the coefficient of `t` at `g`, which is zero. For a fixed index
`j` in the support and a vector `w`, take `f = b.constr ℂ (Pi.single j w)`,
which sends `b j` to `w` and the other basis vectors to `0`. Applying
`exists_asAlgebraHom_eq` on the finite set `b '' c.support` gives `r`, and the
sum above reduces to `(c j) w = 0`. So every `c j` vanishes and `t = 0`.
