# Proof that pointwise separation gives a finite section seed

This module proves `Langlands.AlgebraicGeometry.Picard.FiniteSeedOfSeparationStatement` as
the theorem `Langlands.AlgebraicGeometry.Picard.finiteSeedOfSeparation`.

## Statement proved

Let `K` be a field, `X` a Noetherian scheme, `p : X ⟶ Spec K` a morphism and
`z : Spec K ⟶ X` a point. Call a pair `(L, s)` of a line bundle `L` on `X` and a global
section `s` of `L` *good* if `s` vanishes along `z` and does not vanish along some rational
point. Assume that

* every rational point `x ≠ z` is detected by a good section (`s` does not vanish along
  `x`), and
* every nonzero rational tangent vector `t : Spec K[ε] ⟶ X` at `z` is detected by a good
  section.

Then some finite family of good sections, indexed by `Fin n` (possibly `n = 0`), is a
finite point-tangent section seed at `z` in the sense of the published
`IsFinitePointTangentSectionSeed`.

## Helper lemmas

* The reused `Langlands.SchemeModule.pullback_scalar_eq_zero_iff` from
  [ResidueLocalChartProof](../Modules/ResidueLocalChartProof.md): for `f : Y ⟶ X` and an
  endomorphism `φ` of `𝒪_X`, the pullback `f^* φ` is zero exactly when
  `f.appTop (φ.app ⊤ 1) = 0`. Its proof composes with `pullbackUnitIso f`, transposes along
  the pullback–pushforward adjunction, and uses `pullbackUnitAdjunction` and
  `structureModule_hom_eq_zero_iff`.
* `exists_localEquation`: every global section `s` of a line bundle `L` has a local
  equation near every point `x`. Take a trivializing open `U ∋ x` with an isomorphism
  `e : L|_U ≅ 𝒪_U` (from `L.property x`) and the endomorphism
  `ψ := (restrictUnitIso U.ι).inv ≫ restrict(sectionHom L.obj s) ≫ e.hom` of `𝒪_U`;
  the function `a` on `U` is `ψ.app ⊤ 1`, transported along `U.topIso`. For
  `g : T ⟶ X` with `g⁻¹(U) = T`, factor `g = g' ≫ U.ι` through the open immersion
  (`IsOpenImmersion.lift`); then `g.appLE U ⊤ hg a = g'.appTop (ψ.app ⊤ 1)`
  (`Scheme.Hom.appLE_comp_appLE`), and `VanishesAlong L g s` is equivalent successively
  to `g^*(sectionHom L.obj s) = 0` (`pullbackSection_eq_zero_iff`),
  `g'^*(restrict(sectionHom L.obj s)) = 0` (`pullback_map_comp_eq_zero_iff` and
  `restrictFunctorIsoPullback`), `g'^* ψ = 0` (composing with isomorphisms) and, by the
  previous helper, `g'.appTop (ψ.app ⊤ 1) = 0`.
* `germ_stalkSpecializes_stalkClosedPointTo`: for a local ring `R`, a morphism
  `f : Spec R ⟶ X` whose closed point specializes to `x`, and a function `a` on an open
  `U ∋ x` with `f⁻¹(U) = Spec R`, the germ of `a` at `x`, sent to the stalk at the image
  of the closed point (`stalkSpecializes`) and then to `R` (Mathlib's
  `Scheme.stalkClosedPointTo f`), equals `f.appLE U ⊤ hg a` read in `R` through
  `ΓSpecIso R`. This combines `germ_stalkSpecializes` with Mathlib's
  `Scheme.germ_stalkClosedPointTo`.
* `exists_finset_forall_le_biSup` (private): in a complete lattice with no infinite
  strictly ascending chains (`WellFoundedGT`), every family `f : ι → α` is bounded by
  `⨆ j ∈ F, f j` for some finite set `F`. Proof: choose `F` with `⨆ j ∈ F, f j` maximal
  among finite sub-suprema (`WellFounded.has_min` for `>`); adding any `i` to `F` cannot
  increase the supremum, so `f i` lies below it.

## Proof of the main theorem

1. Let `ι` be the type of good pairs `(L, s)` and `z₀ ∈ X` the image of the closed point
   of `Spec K` under `z`. By `exists_localEquation` at `z₀`, choose for each `i ∈ ι` an
   open `U i ∋ z₀` and a local equation `a i` on `U i`, and let `c i` be the germ of
   `a i` in the stalk `𝒪_{X,z₀}`.
2. Points. The opens of the Noetherian space `X` satisfy `WellFoundedGT`, so the helper
   gives a finite `F₁ ⊆ ι` such that the generation open `trivializationOpen L.obj s` of
   every good pair lies in the union of the generation opens of the pairs in `F₁`.
3. Tangent vectors. The stalk `𝒪_{X,z₀}` is a Noetherian ring (`X` is locally
   Noetherian), so its ideals satisfy `WellFoundedGT`, and the helper gives a finite
   `F₂ ⊆ ι` such that every principal ideal `(c i)` lies in `⨆ j ∈ F₂, (c j)`.
4. The seed is the family of pairs in `F := F₁ ∪ F₂`, indexed by `Fin (card F)` through
   `F.equivFin`. Clauses 1 and 2 of the seed predicate hold because each member is good.
5. Clause 3 (points). For a rational point `x ≠ z`, take a good pair `(L, s)` not
   vanishing along `x`. By `vanishesAlong_iff_not_mem`, the image point of `x` lies in
   the generation open of `s`, hence by step 2 in the generation open of some member of
   `F₁`, and by `vanishesAlong_iff_not_mem` again that member does not vanish along `x`.
6. Clause 4 (tangent vectors). Let `t` be a nonzero tangent vector at `z` and `(L, s)` a
   good pair not vanishing along `t`; suppose for contradiction that every member of the
   family vanishes along `t`. Since `t` composed with the augmentation `K[ε] → K` is `z`,
   every point of `Spec K[ε]` maps into every open containing `z₀`
   (`forall_mem_of_augmentation_comp`); in particular the closed point of `Spec K[ε]`
   specializes to `z₀`, and `t⁻¹(U j)` is everything for each `j`. Let
   `φ : 𝒪_{X,z₀} → K[ε]` be `stalkSpecializes` followed by `Scheme.stalkClosedPointTo t`.
   By the local equations and `germ_stalkSpecializes_stalkClosedPointTo` (with
   `ΓSpecIso` injective), a good pair `j` vanishes along `t` exactly when `φ (c j) = 0`.
   So every `c j` with `j ∈ F₂` lies in the kernel of the ring homomorphism `φ`, hence
   `⨆ j ∈ F₂, (c j) ≤ ker φ`, and by step 3 the germ of the local equation of `(L, s)`
   lies in `ker φ`, so `(L, s)` vanishes along `t`, a contradiction.

The case `n = 0` needs no separate treatment: `F` may be empty.

## Provenance

This is the finiteness step of Milne's proof of Theorem 7.1 (J. S. Milne, *Abelian
Varieties*, author version 2022, p.11), in section form, as explained in the statement's
Markdown. The proof is new Lean code in this project. The route follows the statement's
intended proof, recast in lattice form: instead of a minimal common zero locus of
finitely many good sections (descending chain condition on closed subsets), it uses a
maximal union of finitely many generation opens (ascending chain condition on opens), and
for tangent vectors a maximal finitely generated ideal of germs of local equations in the
Noetherian stalk at `z₀`. The local equations are produced directly from a trivialization
of the line bundle (`exists_localEquation`), not from the frame vanishing criterion.
