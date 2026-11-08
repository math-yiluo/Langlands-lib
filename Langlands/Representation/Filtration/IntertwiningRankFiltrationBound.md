# Left exactness bounds for intertwiners out of a filtered representation

Author: Worker 1697. This is an internal helper module for the VI.8.5 reduction
`Langlands.Renard.AlgebraicFamily.genericInducedIrreducibility_of_inputs`. It has no
separate literature counterpart: it is the left exactness of `Hom(-, τ)`, used in Renard's
proof of VI.8.5 (PDF p.200) in place of the splitting lemma there.

Throughout, `K` is a field, `G` a monoid, and representations are `Representation K G _`.
Intertwiner spaces `ρ.IntertwiningMap τ` are `K`-vector spaces; ranks are `Module.rank`
(cardinals). No semisimplicity, admissibility or finite-dimensionality is assumed.

## Declarations

- The imported `HomSpace.comap τ f` from `Filtration/HomBounds` is
  precomposition `g ↦ g.comp f`, a `K`-linear map `Hom(σ, τ) → Hom(ρ, τ)`
  for an intertwiner `f : ρ → σ`.
- `exists_comp_eq_of_comp_eq_zero`: let `i : ρ → σ` and `q : σ → γ` be intertwiners with
  `q` surjective and every `x` with `q x = 0` in the image of `i`. Then every intertwiner
  `f : σ → τ` with `f ∘ i = 0` factors as `g ∘ q`. The proof passes to group-algebra
  modules, descends `f` to the quotient by `ker q` with `Submodule.liftQ`, and composes
  with the inverse of `σ / ker q ≃ γ`.
- The imported `HomSpace.comap_injective` states that precomposition with a
  surjective intertwiner is injective.
- `rank_intertwiningMap_le_add`: for `i` and `q` as above, with the three source carriers
  in one universe,
  `rank Hom(σ, τ) ≤ rank Hom(ρ, τ) + rank Hom(γ, τ)`.
  By rank–nullity for `R = precomposition with i`, `rank Hom(σ, τ)` is
  `rank (range R) + rank (ker R)`. The range lies in `Hom(ρ, τ)`. The kernel lies in the
  range of precomposition with `q` by the factorization lemma, so its rank is at most
  `rank Hom(γ, τ)`.
- `ObjectRepFiltration.subrepresentationInclusion h` is the inclusion `S → T` of invariant
  subspaces with `S ≤ T`, as an intertwiner.
- `ObjectRepFiltration.rank_intertwiningMap_le_sum`: let `s` be a filtration
  `0 = V₀ ≤ V₁ ≤ ⋯ ≤ Vₙ = A` of a representation `A : Rep K G` (an
  `ObjectRepFiltration A n`), `τ` any representation, and `d : Fin n → ℕ` with
  `rank Hom(Vᵢ₊₁/Vᵢ, τ) ≤ d i` for every graded piece (`s.gradedRepresentation i`). Then
  `rank Hom(A, τ) ≤ ∑ i, d i`.

## Proof of the filtration bound

Induction on `j ≤ n` shows `rank Hom(Vⱼ, τ) ≤ ∑_{i < j} d i`. For `j = 0`, `V₀ = ⊥`, so
every intertwiner out of it vanishes and the rank is `0`. For the step, apply
`rank_intertwiningMap_le_add` to the inclusion `Vⱼ → Vⱼ₊₁` and the graded projection
`Vⱼ₊₁ → Vⱼ₊₁/Vⱼ`, which is surjective with kernel `Vⱼ`, and then add the bound `d j`.
Finally `Vₙ = ⊤`, so the inclusion `Vₙ → A` is surjective. Precomposition with it embeds
`Hom(A, τ)` into `Hom(Vₙ, τ)`.
