# Simple modules over a tensor product of algebras (Renard III.1.14, Scholium): statements

Module `Langlands.Algebra.AlgebraTensorSimpleModuleStatements`. Namespace `Langlands`.
Universe parameters `u₁`, `u₂` (the algebras) and `v`, `v₁`, `v₂`, `w₁`, `w₂` (the modules).
The module contains four **statements**, the `Prop`-valued definitions
`AlgebraExternalTensorSimpleStatement`, `AlgebraTensorSimpleFactorizationStatement`,
`AlgebraTensorFactorUniquenessStatement` and their conjunction `AlgebraTensorScholiumStatement`.
It proves nothing.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`. Renard recalls the Scholium from Bump and uses it with
III.1.5 for the irreducibility and factorization assertions of the III.1.14 Proposition. The
Library states and proves those group-level assertions directly (`FlathTwoFactorStatement`, and
`FiniteTensor.isIrreducible_external` for the irreducibility of external tensor products of
group representations). It has no statement of the algebra-level Scholium.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read III.1.14, printed pp.66–67 / PDF pp.72–73:

> Le reste découle alors facilement du théorème III.1.5 et du résultat suivant, dont on trouvera
> une démonstration dans [16], Prop. 3.4.1.
>
> Scholium. Soient `A₁` et `A₂` des algèbres unitaires et soient `(τ₁, V₁)`, `(τ₂, V₂)` des
> représentations irréductibles de dimension finie de `A₁` et `A₂` respectivement. Alors la
> représentation `(τ₁ ⊠ τ₂, V₁ ⊗ V₂)` de `A₁ × A₂` est irréductible. Réciproquement, toute
> représentation irréductible de dimension finie de `A₁ × A₂` s'écrit sous cette forme, de
> manière unique à isomorphisme près.

Reference [16] of the source is Daniel Bump, *Automorphic forms and representations*
(Cambridge Studies in Advanced Mathematics 55). Worker 1222 did not consult it. The statements
follow the Scholium as printed, read as below.

**Reading of `A₁ × A₂`.** The direct product `A₁ × A₂` does not act on `V₁ ⊗ V₂` by
`(a₁, a₂) ↦ τ₁(a₁) ⊗ τ₂(a₂)`, because this map is not additive. The action is one of the tensor
product algebra `A₁ ⊗ A₂`, as in the Proposition's proof just above, where
`H(G, K) = H(G₁, K₁) ⊗ H(G₂, K₂)`. The statements use `A₁ ⊗[ℂ] A₂` (Mathlib's
`Algebra.TensorProduct`).

## Mathlib objects used

- Algebra representations follow Mathlib's convention
  (`Mathlib.RepresentationTheory.AlgebraRepresentation.Basic`): a representation of a complex
  algebra `A` on `V` is a module `[Module A V]` with `[Module ℂ V] [IsScalarTower ℂ A V]`. It is
  irreducible when `IsSimpleModule A V`. Simple modules are nonzero.
- `Algebra.lsmul ℂ ℂ V : A →ₐ[ℂ] Module.End ℂ V`, `a ↦ (v ↦ a • v)`.
- `Algebra.TensorProduct.map` and `Module.endTensorEndAlgHom`, which sends `f ⊗ g` to the
  tensor product map `f ⊗ g`.

## The statements

Let `A₁`, `A₂` be unital complex algebras. For `A₁`-module `V₁` and `A₂`-module `V₂` as above,
let `σ : A₁ ⊗ A₂ →ₐ[ℂ] End_ℂ(V₁ ⊗ V₂)` be the composite of `Algebra.TensorProduct.map` of the
two `Algebra.lsmul` maps with `Module.endTensorEndAlgHom`. So
`σ(a₁ ⊗ a₂)(v₁ ⊗ v₂) = a₁ v₁ ⊗ a₂ v₂`: this is the representation `τ₁ ⊠ τ₂`.

**`AlgebraExternalTensorSimpleStatement`.** If `V₁` and `V₂` are finite-dimensional simple
modules, then `V₁ ⊗ V₂` is nontrivial, and every complex subspace `U` of `V₁ ⊗ V₂` with
`σ(a) U ⊆ U` for all `a ∈ A₁ ⊗ A₂` is `0` or `V₁ ⊗ V₂`.

**`AlgebraTensorSimpleFactorizationStatement`.** If `W` is a finite-dimensional simple
`A₁ ⊗ A₂`-module (with `[IsScalarTower ℂ (A₁ ⊗ A₂) W]`), then there are finite-dimensional simple
modules `V₁` over `A₁` and `V₂` over `A₂`, in the universe of `W`, and a complex-linear
bijection `e : V₁ ⊗ V₂ ≃ W` with `e(σ(a) x) = a • e(x)` for all `a ∈ A₁ ⊗ A₂`.

**`AlgebraTensorFactorUniquenessStatement`.** Let `V₁`, `W₁` be finite-dimensional simple
`A₁`-modules and `V₂`, `W₂` finite-dimensional simple `A₂`-modules, with `σ` and `σ'` the
representations on `V₁ ⊗ V₂` and `W₁ ⊗ W₂`. If a complex-linear bijection
`e : V₁ ⊗ V₂ ≃ W₁ ⊗ W₂` satisfies `e(σ(a) x) = σ'(a) e(x)`, then `V₁ ≅ W₁` as `A₁`-modules and
`V₂ ≅ W₂` as `A₂`-modules.

**`AlgebraTensorScholiumStatement`** is the conjunction of the three.

## Formalization choices

- **Irreducibility of `τ₁ ⊠ τ₂`.** Mathlib has no `A₁ ⊗ A₂`-module instance on `V₁ ⊗ V₂`. The
  first statement therefore states irreducibility of `σ` directly: nonzero space, no stable
  subspaces other than `0` and the whole space. Stable complex subspaces are exactly the
  `A₁ ⊗ A₂`-submodules for the module structure defined by `σ`, so this is `IsSimpleModule` for
  that structure.
- **Isomorphisms.** In the second statement, an isomorphism of representations
  `V₁ ⊗ V₂ ≅ W` is a complex-linear bijection intertwining `σ` with the module action. In the
  third, it intertwines `σ` and `σ'`. Taking `a = a₁ ⊗ 1` or `a = 1 ⊗ a₂` shows that such a
  bijection is linear for `A₁` and for `A₂`.
- **Field.** The source's algebras are complex, and the statements are over `ℂ`.
- **Universes.** In the existence statement the factors live in the universe of `W`. They can be
  taken inside `W` and inside `Hom_ℂ(V₁, W)`. The other two statements allow independent
  universes.

## Why the statements are true

Since `V_i` is finite-dimensional and simple over the algebraically closed field `ℂ`,
`End_{A_i}(V_i) = ℂ` by Schur's lemma. Burnside's theorem (Jacobson density) then makes
`A_i → End_ℂ(V_i)` surjective. So `σ(A₁ ⊗ A₂)` contains `End_ℂ(V₁) ⊗ End_ℂ(V₂) = End_ℂ(V₁ ⊗ V₂)`,
and `V₁ ⊗ V₂ ≠ 0` has no proper nonzero stable subspace.

For existence, `A₁` acts on `W` through `a₁ ↦ a₁ ⊗ 1` and `A₂` through `a₂ ↦ 1 ⊗ a₂`, and the two
actions commute. Since `W` is finite-dimensional, it contains a simple `A₁`-submodule `V₁`. Put
`V₂ = Hom_{A₁}(V₁, W)`. It is finite-dimensional and is an `A₂`-module through the action on
`W`. Evaluation `V₁ ⊗ V₂ → W`, `v ⊗ f ↦ f(v)`, intertwines the actions. It is nonzero, hence
onto because `W` is simple. Hence `W` is a sum of copies of `V₁` as an `A₁`-module. Then the
evaluation map is injective, because `End_{A₁}(V₁) = ℂ`. A nonzero proper `A₂`-submodule `U` of
`V₂` would give the proper nonzero submodule `V₁ ⊗ U` of `W`, so `V₂` is simple.

For uniqueness, as an `A₁`-module `V₁ ⊗ V₂` is a direct sum of `dim V₂ ≥ 1` copies of `V₁`, and
`W₁ ⊗ W₂` is a direct sum of copies of `W₁`. An `A₁`-linear isomorphism between them forces
`V₁ ≅ W₁` (Jordan–Hölder, or `Hom_{A₁}(V₁, W₁ ⊗ W₂) ≠ 0` and Schur). The same argument with `A₂`
gives `V₂ ≅ W₂`.

## Remaining obligations

The proofs are a separate obligation.

## Imports

| Module | Used for |
| --- | --- |
| `Mathlib.RingTheory.TensorProduct.Maps` | `Algebra.TensorProduct.map`, `Module.endTensorEndAlgHom`; through its imports `Algebra.lsmul` |
| `Mathlib.RingTheory.SimpleModule.Basic` | `IsSimpleModule` |
| `Mathlib.LinearAlgebra.FiniteDimensional.Defs` | `FiniteDimensional` |
| `Mathlib.Basic.Complex.Basic` | `ℂ` |
