# Restriction and the smooth Hom bifunctor

Worker 231, Task 5449.

This is an internal supporting unit for the tensor identity of Renard III.2.11
(*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, printed pp.82–83 / PDF pp.88–89; registered source
`renard-2026-representations-groupes-reductifs-padiques`). The source's proof of
the second Mackey isomorphism leaves exactly one step unjustified, the
identification (III.2.11.8). The source says it becomes evident when the
pseudo-forgetful functor is isomorphic to the forgetful one. The derived results
below supply that step for continuous pullback `restriction φ hφ` along
`φ : H →* G`.

## Algebraic helpers

- `quotientRep S` is left translation of `G` on finitely supported functions
  `G ⧸ S →₀ ℂ`, built with `Finsupp.lmapDomain`.
- For a vector `x` fixed by `S`, `quotientLift S ρ x hx` is the equivariant map
  `δ_{gS} ↦ ρ g x`. It is built from the orbit map `orbitMap`, and
  `quotientLift_single_one` shows that it sends `δ_S` to `x`.
- `quotientRep_fixed` shows that `δ_{φ(U)}` is fixed by `U` acting through `φ`.
- `linHom_comp` shows that pulling back the conjugation Hom representation
  `Representation.linHom ρ σ` along `φ` gives the conjugation Hom of the pullbacks.
- `isSmoothVector_of_comp` assumes that every `φ(U)`, for `U` an open subgroup of
  `H`, contains an open subgroup of `G`. Under that condition, a vector smooth for
  `ρ ∘ φ` is smooth for `ρ`.

## Openness from a left adjoint of restriction

`exists_fixing_of_adjunction` applies to any adjunction `adj : P ⊣ restriction φ hφ`
of smooth categories with carrier universe `max uG v`, and any vector `w` of an
`H`-representation `W`. It gives a single open subgroup `K` of `G` that fixes
`f w` for every `G`-representation `E` and every `H`-map `f : W ⟶ restriction E`.
The reason is that `f` factors as the unit followed by the restriction of a `G`-map
`P W ⟶ E`, and the image of `w` under the unit is fixed by an open subgroup
because `P W` is smooth.

`exists_openSubgroup_le_map_of_adjunction` concludes that for every open subgroup
`U` of `H`, some open subgroup `K` of `G` satisfies
`∀ k ∈ K, ∃ u ∈ U, φ u = k`. The proof has four steps.

1. Choose a compact open subgroup `U₀ ≤ U` with the published
   `compactOpenSubgroupBasis`, and put `S = φ(U₀)`. This `S` is compact, hence
   closed.
2. Let `quotientTestObj φ S` be the `H`-smooth vectors of `quotientRep S ∘ φ`,
   lifted to the carrier universe `max uG v`. Using `G ⧸ S` rather than a quotient
   of `H` keeps the carrier in the universe of `G`. The base vector
   `quotientBase φ U₀ = δ_S` is fixed by `U₀`, and `exists_fixing_of_adjunction`
   gives an open `K`.
3. For every `S`-fixed vector `x` of a smooth `G`-representation `E`,
   `quotientTestHom` is an `H`-map sending the base vector to `x`. Hence `K` fixes
   every such `x`.
4. Suppose `g ∈ K` but `g ∉ S`. The published basis gives a compact open subgroup
   `K'` disjoint from the closed set `S g`. Take `E` to be the lifted left regular
   representation on test functions (`leftTests`, smooth by the published
   `isSmooth_leftTests`), and `x` the characteristic function of the compact open
   set `S K'`. This `x` is `S`-fixed, so it is fixed by `g`. Evaluating at `g` gives
   `g ∈ S K'`, and then `K'` meets `S g`, a contradiction.

## The comparison (III.2.11.8)

Assume `hopen : ∀ U : OpenSubgroup H, ∃ K : OpenSubgroup G, ∀ k ∈ K, ∃ u ∈ U, φ u = k`.

- `smoothVectors_linHom_le` and `smoothVectors_linHom_ge` show that the `G`-smooth
  linear maps `V →ₗ E` are exactly the linear maps that are smooth for the
  conjugation action of `H` through `φ`. The first inclusion holds for every
  continuous `φ`; the second uses `hopen`.
- `restrictionHomIso φ hφ hopen` is a natural isomorphism
  `smoothHomBifunctor G ⋙ restriction φ hφ ≅
  (restriction φ hφ).op.prod (restriction φ hφ) ⋙ smoothHomBifunctor H`.
  Its components are the identity on underlying linear maps, so the inverse laws
  and naturality hold definitionally.
