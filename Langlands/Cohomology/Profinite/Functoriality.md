# Functoriality: maps along continuous homomorphisms, restriction, inflation

`Langlands/Cohomology/Profinite/Functoriality.lean`, namespace `Langlands.ProfiniteCohomology`.

A pair `(φ, f)` of a continuous homomorphism `φ : H →ₜ* G` and a morphism
`f : Rep.res φ A ⟶ B` of `H`-representations ("compatible pair" in Neukirch–Schmidt–Wingberg)
induces `map φ f n : Hⁿ(G, A) ⟶ Hⁿ(H, B)`. There is one such definition: maps of coefficients are
`map (.id G) f n`, restriction and inflation are abbreviations for special pairs. This is the
shape of Mathlib's `ContinuousCohomology.map`.

## Declarations

- `subgroupInclusion S : S →ₜ* G`, `quotientMap N : G →ₜ* G ⧸ N`: the inclusion of a subgroup and
  the projection to a quotient, as continuous homomorphisms; `continuous_subgroup_subtype`,
  `continuous_quotientGroup_mk'` their continuity.
- `isLocallyConstant_cochainsMap`: `c ↦ f ∘ c ∘ φⁿ` preserves local constancy.
- `cochainsMap φ f : cochains A ⟶ cochains B`, the induced map of complexes, with
  `cochainsι_cochainsMap_apply` (its formula), `cochainsMap_comp_cochainsι` (compatibility with
  Mathlib's `groupCohomology.cochainsMap`), `cochainsMap_id`, `cochainsMap_comp` (for
  `φ.comp ψ` and `(Rep.resFunctor ψ).map f ≫ g`), `cochainsMap_id_comp`, `cochainsMap_zero`,
  `cochainsMap_id_zero`; a coefficient map that is a monomorphism (epimorphism) gives a
  monomorphism (epimorphism) of cochains in each degree.
- `cocyclesMap φ f n`, and `map φ f n : cohomology A n ⟶ cohomology B n`, the map in degree `n`,
  with `cohomologyπ_map` (on classes of cocycles), `map_id`, `map_comp`, `map_id_comp`,
  `map_zero_eq_zero`, `map_id_zero`.
- `cochainsFunctor k G`, `cohomologyFunctor k G n`: the complex and the cohomology in degree `n`
  as additive functors on the Library's category `SmoothRep k G`, with `cohomologyFunctor_obj`,
  `cohomologyFunctor_map`.
- `res A S n : Hⁿ(G, A) ⟶ Hⁿ(S, A)`: restriction to a subgroup `S`, i.e.
  `map (subgroupInclusion S) (𝟙 _) n` (`res_eq`); `res_naturality`: it commutes with maps of
  coefficients.
- `infl A N n : Hⁿ(G/N, A^N) ⟶ Hⁿ(G, A)`: inflation from the quotient by a normal subgroup `N`,
  i.e. the map for the projection `G → G/N` and the inclusion `A^N → A` (`infl_eq`);
  `isSmoothRep_quotientToInvariantsFunctor_obj`: `A^N` as a smooth `G/N`-representation through
  Mathlib's functor.

- `bijective_coeffMap_of_iso e r`: an isomorphism of smooth modules over `ℤ` is bijective on `Hʳ`.

Complete type of `bijective_coeffMap_of_iso`, as printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.ProfiniteCohomology.bijective_coeffMap_of_iso.{u} {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {A B : Rep.{u, u, u} (ULift.{u, 0} ℤ) G} [Langlands.IsSmoothRep A] [Langlands.IsSmoothRep B]
  (e : A ≅ B) (r : ℕ) : Function.Bijective ⇑(ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.coeffMap e.hom r))
```

## Source and licence

Ported from `src/GroundTheory/ProfiniteCohomology/ContinuousCochains/Functoriality.lean`
(sections `Map` and `Functor`), `src/GroundTheory/ProfiniteCohomology/CohomologyFunctoriality.lean`
and `src/GroundTheory/ProfiniteCohomology/CohomologyFunctoriality/Naturality.lean` of the repository
`leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>),
commit `f1f6d65`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`).

Changed against the source: the source has two maps, `cohomologyMap f n` (coefficients) and
`cohomologyMapAlong φ hφ f n` (with `φ : H →* G` and a separate continuity proof `hφ`), with
cochain maps `cochainsMap f` and `cochainsMapAlong φ hφ f`, and proves that they agree for
`φ = id`. Here there is one `cochainsMap φ f` and one `map φ f n` with `φ : H →ₜ* G`. Names:
`cohomologyMapAlong` → `map`, `cohomologyMap f` → `map (.id G) f`, `cochainsMapAlong` →
`cochainsMap`, `cocyclesMapAlong` → `cocyclesMap`, `cohomologyRes` → `res`, `cohomologyInfl` →
`infl` (both now abbreviations), `cohomologyRes_eq` → `res_eq`, `cohomologyInfl_eq` → `infl_eq`,
`cohomologyRes_naturality` → `res_naturality`, `cohomologyπ_cohomologyMapAlong` →
`cohomologyπ_map`, `cohomologyMapAlong_id`/`cohomologyMap_id` → `map_id`,
`cohomologyMapAlong_comp` → `map_comp`, `cohomologyMapAlong_id_comp`/`cohomologyMap_comp` →
`map_id_comp`, `cochainsMapAlong_comp_cochainsComplexι` → `cochainsMap_comp_cochainsι`; the
source's `cohomologyMapAlong_id_eq_cohomologyMap`, `cochainsMapAlong_id_eq_cochainsMap` and
`cohomologyMap_comp_cohomologyRes` are no longer needed. The functors are on the Library's
`SmoothRep` in place of the source's `DiscreteRep`. `res_naturality` is proved with
`backward.isDefEq.respectTransparency false` because the coefficient map `g : A ⟶ A'` is used at
the definitionally equal type `Rep.res (.id G) A ⟶ A'`, as Mathlib does for its own
`groupCohomology.map (MonoidHom.id G)`.

`bijective_coeffMap_of_iso` contains no text of the source.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter I, §5, p. 45 (compatible pairs and the maps they induce) and
  p. 47 (inflation, restriction).
- J.-P. Serre, *Galois Cohomology* (English translation of *Cohomologie galoisienne*, Springer 1997;
  corrected printing 2002), chapter I, §2.4, p. 12 (compatible pairs `(f, h)`, restriction).
