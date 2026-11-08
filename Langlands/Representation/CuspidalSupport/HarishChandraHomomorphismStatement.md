# Harish-Chandra homomorphisms: statement

Author: Worker 6. Module `Langlands.Representation.CuspidalSupport.HarishChandraHomomorphismStatement`, namespace `Langlands.Aubert.General.RepresentedParabolic`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VI.10.5, printed p.213 / PDF p.219. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## The source

For a parabolic `P = MN` of `G`, the map `i_{MG} : Ω(M) → Ω(G)` of VI.7.3 is a finite morphism of varieties. It induces a morphism of algebras of polynomial functions `i*_{MG} : ℨ(G) → ℨ(M)`, the Harish-Chandra homomorphism. Here `ℨ(G)` is the centre of `M(G)`. Since `i_{MG}` is finite, `ℨ(M)` is a finitely generated `ℨ(G)`-module. Renard's Proposition then states: let `z ∈ ℨ(G)` and `z_M = i*_{MG}(z)`. For every `(σ, E)` in `M(M)`, `i_P^G(z_M)` is a `G`-equivariant endomorphism of `i_P^G(σ, E)` that coincides with the endomorphism defined by `z`, viewed as an element of the centre of the category. For every `(π, V)` in `M(G)`, `r_P^G(z)` is an `M`-equivariant endomorphism of `r_P^G(π, V)` that coincides with the one defined by `z_M`.

## The Lean statement

`HarishChandraHomomorphismStatement` is a statement unit: nothing is proved.

It quantifies over:

- a nonarchimedean local field `k : Type u`;
- a connected reductive `G` over `Spec k`, with `G(F)` locally compact and nonarchimedean in the canonical topology;
- an actual rational parabolic `P = MN` (`p`, `l`, `r` with `hp`, `hl`, `hr`, `hmul`). The Levi `M(F)` has the canonical Levi topology and the published local compactness and nonarchimedean instances.

Write `I` for the published normalized induction `leviInductionFunctor.{u, max u v} p l r hp hr hl hmul` and `R` for the published normalized Jacquet functor `leviJacquetFunctor.{u, max u v} p l r hp hr hl hmul`, both between the categories `SmoothRep.{0, u, max u v}` of smooth representations of `M(F)` and `G(F)` on carriers in the common universe `max u v`. On these categories, `I` and `R` are endofunctors of a fixed universe. The centres are Mathlib's `CatCenter C = End (𝟭 C)`, Renard's `ℨ(G)` and `ℨ(M)`.

The conclusion is the existence of a ring homomorphism `φ : CatCenter(G) →+* CatCenter(M)`, `z ↦ z_M`, such that:

1. `I.map ((φ z).app σ) = z.app (I.obj σ)` for all `z` and all smooth `σ` of `M(F)`: `i_P^G(z_M) = z` on `i_P^G(σ)`;
2. `R.map (z.app π) = (φ z).app (R.obj π)` for all `z` and all smooth `π` of `G(F)`: `r_P^G(z) = z_M` on `r_P^G(π)`;
3. `CatCenter(M)` is a finitely generated module over `CatCenter(G)` through `φ`. The module structure is `Module.compHom _ φ`, since `CatCenter` carries a semiring instance but no commutative instance from which `φ.toAlgebra` could be built.

## Comparison with the source

- Renard constructs `i*_{MG}` geometrically, from the finite morphism `Ω(M) → Ω(G)` and the identification of the centres with polynomial functions (VI.10.4, Theorem). That construction needs the variety structures, which are not available. The statement asserts instead the existence of a ring homomorphism with the two compatibilities of the Proposition and the finiteness. Since `i_P^G` is faithful, condition 1 determines `φ z` uniquely, so the existential describes exactly Renard's homomorphism. This uniqueness remark is not formalized.
- The parabolic need not be standard.
- The finiteness of `i_{MG}` as a morphism of varieties is not stated; only its consequence, finite generation of `ℨ(M)` over `ℨ(G)`, is.
- The proof is not formalized here.
