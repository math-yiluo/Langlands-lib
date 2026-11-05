# The commutator relations for root exponentials over every commutative ring

Author: Worker 1398.

Module `Langlands.GroupScheme.SplitExistence.CommutatorInt`.

## Declarations

- `exists_list_lift f`: a list of pairs whose second components lie in the range of a ring
  homomorphism `f` is the image under `f` of a list.
- `LieRootData.prod_map_ringHom φ L`: applying a ring homomorphism `φ` entrywise to
  `∏_{(θ, f) ∈ L} x_θ(f)` gives `∏ x_θ(φ f)` (from `divExp_map`, module `RootExp`).
- `LieRootData.exists_list_commutator_int` (`J` finite; `h : X →+ ℤ` positive on `γ` and `δ`):
  over `ℤ[t][s] = ℤ[X][X]`, the commutator `x_γ(s) x_δ(t) x_γ(-s) x_δ(-t)` is an ordered product
  of root exponentials. Its roots lie in `commRoots P γ δ` and are pairwise distinct, with
  nondecreasing `h`-values.
- `LieRootData.commutator` (**commutator relations**; `J` finite; `h : X →+ ℤ` positive on the
  roots `j` and `j'`): for every commutative ring `R` and all `s, t ∈ R`, there is a list `L` of
  pairs (root, parameter in `R`) with
  `x_j(s) x_j'(t) x_j(-s) x_j'(-t) = ∏_{(θ, f) ∈ L} x_θ(f)`, where every root `θ` of `L`
  satisfies `root θ = a • root j + c • root j'` for some `a, c ≥ 1`. This is exactly the
  `commutator` field of `ChevalleyData`.

Proofs: `exists_list_commutator_int` starts from `exists_list_commutator_poly` over `ℚ[t][s]`
(module `CommutatorOde`, with `A = ℚ[t]`). The commutator has integral entries, since it is the
image of the commutator over `ℤ[t][s]`. So by `mem_of_prod_mem` (module `Integrality`, with `Z`
the image of `ℤ[t][s]`), all parameters lie in that image. `exists_list_lift` lifts the list,
and injectivity of `ℤ[t][s] → ℚ[t][s]` transfers the identity to `ℤ[t][s]`. `commutator`
applies the evaluation homomorphism `ℤ[t][s] → R`, `t ↦ t`, `s ↦ s`, through
`prod_map_ringHom`.

Provenance: Chevalley's commutator formula (Steinberg, *Lectures on Chevalley groups*, §3), in
the weak form that records only which roots occur. Our proof route is internal: an ODE over
`ℚ[t][s]`, then integrality peeling, then specialization.
