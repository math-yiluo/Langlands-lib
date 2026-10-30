# Ordered Čech cochains of abelian presheaves

Author: Worker 727.

This module defines the ordered Čech complex of a presheaf of abelian groups on a topological
space for a family of opens. It also proves the elementwise formula for the differential,
functoriality in the presheaf, and the long-exact-sequence step used to move exactness along a
short exact sequence of presheaves. It is a helper for the proof of
`Langlands.AlgebraicGeometry.Modules.AffineQuasicoherentHigherDirectImageVanishingStatement`
(module `Langlands.AlgebraicGeometry.Modules.AffineQuasicoherentHigherDirectImageVanishingProof`).
It contains no `sorry` and no new axioms.

## Provenance

The complex is the Čech complex of The Stacks Project, Cohomology of Sheaves, Section
`section-cech` (tag 01ED) and Definition `definition-cech-complex` (tag 01EF), lines 868-925
of `cohomology.tex` in the registered source `stacks-flasque-affine-vanishing-kunneth-a04446e5`
(Stacks commit `a04446e57ec1fbc252a871afcec7752fb2807b14`). Stacks indexes `p`-cochains by all ordered tuples
`(i_0, …, i_p)`, repetitions allowed, and uses the alternating sum of the face maps as
differential. This file uses exactly this ordered complex, not the alternating subcomplex.
Mathlib has no Čech complex of a presheaf on a topological space, so the construction is
internal. Its name and exact form are a project choice made for the proof of Stacks Lemma
01XC.

## Definitions

All declarations are in namespace `Langlands.Cohomology.Cech`. Throughout, `T : TopCat.{u}`,
`P : TopCat.Presheaf AddCommGrpCat.{v} T`, `ι : Type w` and `U : ι → Opens T`.

- `inter U σ` for `σ : Fin n → ι` is the open `⨅ a, U (σ a)`, the intersection
  `U (σ 0) ⊓ ⋯ ⊓ U (σ (n - 1))`. For `n = 0` it is `⊤`; it is used only for `n ≥ 1`.
- `res h : P.obj (op W) →+ P.obj (op V)` for `h : V ≤ W` is the restriction map
  `P.map (homOfLE h).op`, as an additive map.
- `C P U p` (abbreviation) is the type of `p`-cochains: dependent functions
  `z : ∀ σ : Fin (p + 1) → ι, P.obj (op (inter U σ))`.
- `cosimplicial P U` is the cosimplicial abelian group with `[n] ↦ C P U n`. A monotone map
  `θ : [m] ⟶ [n]` sends `z` to `τ ↦ res (z (τ ∘ θ))`.
- `complex P U` is Mathlib's alternating coface complex of `cosimplicial P U`, a
  `CochainComplex AddCommGrpCat ℕ`.
- `d P U p : C P U p →+ C P U (p + 1)` is the differential of `complex P U` in degree `p`.
- `coface P U p k` omits the `k`-th index: `(coface P U p k z) τ = res (z (τ ∘ k.succAbove))`.
- `ExactAt P U p` is the proposition that every `(p + 1)`-cocycle is a coboundary:
  `∀ z : C P U (p + 1), d P U (p + 1) z = 0 → ∃ y : C P U p, d P U p y = z`. So it says
  that the Čech complex is exact in degree `p + 1`. Degree `0` is not covered.
- `map U φ p : C P U p →+ C Q U p` applies a morphism of presheaves `φ : P ⟶ Q` to each
  component.

## Results

- `inter_le_comp σ θ`, `inter_le_apply σ a`: `inter U σ ≤ inter U (σ ∘ θ)` and
  `inter U σ ≤ U (σ a)`.
- `res_res`, `res_self`: restriction is functorial.
- `d_eq_sum`, `d_apply`: the differential is the alternating sum of the coface maps:
  `d P U p z τ = ∑ k : Fin (p + 2), (-1) ^ k • res (z (τ ∘ k.succAbove))`.
- `d_d`: `d P U (p + 1) (d P U p z) = 0` (from Mathlib's `d_squared` for alternating coface
  complexes).
- `map_res`, `d_map`: morphisms of presheaves commute with restriction and with the
  differential.
- `res_congr`: if `σ = σ'`, then the restrictions of `x σ` and `x σ'` to a common smaller
  open agree. This replaces rewriting inside dependent types.
- `inter_cons`, `cons_comp_succAbove_zero`, `cons_comp_succAbove_succ`,
  `le_inter_cons_comp`: combinatorics of prepending an index `i` to a tuple `τ`.
- `res_eq_sum_of_d_eq_zero hz i τ hO`: if `z` is a `(p + 1)`-cocycle and `O ≤ U i ⊓ inter U τ`,
  then on `O` the component `z τ` is the alternating sum of the components
  `z (i, τ with the k-th index omitted)`. This is the cocycle condition at the tuple `(i, τ)`.
- `exactAt_of_shortExact i π hiπ hi hex hπ hB hA`: let `A ⟶ B ⟶ C'` be morphisms of presheaves
  with `π ∘ i = 0` such that on every `inter U σ` (`σ` of positive length) the map `i` is
  injective, `ker π ⊆ im i`, and `π` is surjective. If `ExactAt B U p` and
  `ExactAt A U (p + 1)`, then `ExactAt C' U p`. This is the step of the long exact sequence of
  Čech cohomology `Ȟ^{p+1}(B) ⟶ Ȟ^{p+1}(C') ⟶ Ȟ^{p+2}(A)` used in the proof of Stacks Lemma 01EW (`lemma-cech-vanish-basis`), proved by
  a direct diagram chase on cochains.
