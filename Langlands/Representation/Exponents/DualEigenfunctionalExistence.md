# Dual eigenfunctionals from generalized eigencharacters

Author: Worker 23.

This module shows that a generalized eigencharacter of a family of central
elements acting on an admissible representation is also the eigencharacter of
a nonzero functional on the whole carrier, for the transposed action. The
character is not inverted. The functional is a dual eigenvector on a
finite-dimensional space of fixed vectors, composed with the Hecke projection
onto that space. The module supports the adapter
`Langlands.glProductLeviDualOppositeTemperedSufficiency_of_core`
([`ProductLeviDualOppositeAdapter`](../Classification/ProductLeviDualOppositeAdapter.md)).

All declarations are in the namespace `Langlands.DualEigenfunctional`.

## Common kernels of commuting nilpotent maps

`exists_ne_zero_forall_apply_eq_zero g hc hn`: let `M` be a nonzero
finite-dimensional vector space over a field `K`, and let
`g : ι → Module.End K M` be a family of pairwise commuting nilpotent
endomorphisms, for an arbitrary index type `ι`. Then some `v ≠ 0` satisfies
`g i v = 0` for every `i`.

The proof is `exists_ne_zero_forall_apply_eq_zero_aux`, by strong induction
on `Module.finrank K M`. If every `g i` is zero, any nonzero vector works.
Otherwise choose `g i ≠ 0` and let `W = ker (g i)`. Then `W ≠ ⊥`, since an
injective nilpotent map on a nonzero space is impossible. `W ≠ ⊤`, since
`g i ≠ 0`, so `W` has smaller dimension. Commutation makes `W` stable under
every `g j`. The restrictions of the `g j` to `W` again commute and are
nilpotent, and the induction hypothesis gives the common kernel vector in `W`.

`dualMap_pow_apply N k φ w` records `((N.dualMap ^ k) φ) w = φ ((N ^ k) w)`.

## Dual eigenvectors in finite dimension

`exists_dual_eigenvector f hc χ hy0 hy`: let `Y` be a finite-dimensional
complex vector space and `f : ι → Module.End ℂ Y` a commuting family. Suppose
some `y ≠ 0` lies in the maximal generalized eigenspace of `f i` for the
eigenvalue `χ i`, for every `i`. Then there is a nonzero `φ : Module.Dual ℂ Y`
with `φ (f i w) = χ i * φ w` for all `i` and `w`.

The proof uses the joint generalized eigenspaces
`E χ' = ⨅ i, (f i).maxGenEigenspace (χ' i)`. By Mathlib, for a commuting
family these subspaces are independent, and they span `Y` because each single
`f i` has spanning generalized eigenspaces over `ℂ`. Hence `W = E χ`, which
contains `y`, has the complement `C`, the span of all other `E χ'`. Both
`W` and `C` are stable under every `f i`. On `W` the restrictions
`N i = (f i - χ i)|_W` commute and are nilpotent. Their transposes on the
nonzero space `Module.Dual ℂ W` therefore also commute and are nilpotent.
The common kernel lemma gives `ψ₀ ≠ 0` with `ψ₀ ∘ N i = 0`, that is
`ψ₀ (f i w) = χ i * ψ₀ w` on `W`. The required functional is `ψ₀` composed
with the projection of `Y` onto `W` along `C`. It restricts to `ψ₀` on `W`,
so it is nonzero. The projection kills `C` and `f i (C)`, and it fixes `W`
and `f i (W)`. This gives the eigen-equation on `W ⊔ C = Y`.

## The admissible case

`exists_dualEigenfunctional_of_isGeneralizedEigencharacter ρ hρ hG z hz χ h`:
let `G` be a topological group and `ρ : Representation ℂ G X` admissible
(`IsAdmissible ρ`, which includes smoothness). Assume
`hG : CompactOpenCofinal G`: every open subgroup contains a compact open
subgroup. Let `A` be a monoid, `z : A →* G` with every `z a` in the centre of
`G`, and `χ : A →* ℂˣ`. If `χ` is a generalized eigencharacter of `ρ.comp z`
(`IsGeneralizedEigencharacter`), then some nonzero `φ : Module.Dual ℂ X`
satisfies

```text
φ (ρ (z a) x) = χ(a) * φ(x)    for all a and x.
```

The full algebraic dual is used. No continuity of `χ` is assumed.

Proof. `isGeneralizedEigencharacter_iff` gives `k` and `y ≠ 0` with
`(ρ (z a) - χ(a))^k y = 0` for every `a`. Smoothness fixes `y` by an open
subgroup `H`, and `hG` gives a compact open `K ≤ H`. So `y` lies in the fixed
space `X^K`, which is finite-dimensional by admissibility. Each `ρ (z a)` is an
intertwining operator of `ρ`, because `z a` is central. It therefore restricts
to an endomorphism `f a` of `X^K`; these commute, again by centrality. The
vector `y` lies in the maximal generalized eigenspace of each `f a` for the
eigenvalue `χ(a)`. `exists_dual_eigenvector` gives a nonzero dual eigenvector
`φ₀` on `X^K`.

Choose the Borel σ-algebra on `G` and the Haar measure normalized on the
positive compact set `K`. Then `Hecke.fixedProjection` is a linear projection
`P : X → X^K`. It is the identity on `X^K`, so `φ₀ ∘ P ≠ 0`. By
`Hecke.fixedProjection_intertwiner`, it carries `ρ (z a)` to `f a`, so
`φ₀ ∘ P` satisfies the eigen-equation. The measure is auxiliary and does
not occur in the statement.

## Provenance

This is internal, derived support. The route is the one outlined in the
section "Relation between the two forms" of
[`ProductLeviTemperedSufficiencyStatement`](../Classification/ProductLeviTemperedSufficiencyStatement.md):
a generalized eigencharacter is visible on a finite-dimensional invariant
space, and a dual eigenvector there extends by compact-open averaging. The
linear-algebra inputs are Mathlib's results on joint generalized
eigenspaces of commuting endomorphisms. The Hecke projection and its
intertwining property come from the published module
`Langlands.Representation.Hecke.ActionProjection`.
