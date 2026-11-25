# Group cohomology of restricted products; naturality of the connecting map

`Langlands/Cohomology/RestrictedProduct.lean`, namespace `Langlands.Cohomology`. Cohomology is
Mathlib's `groupCohomology` of a representation of a group.

**Restricted products.** `IsRestrictedProduct π j`: a representation `A` of `G` is the restricted
product of a family of representations `P i` with respect to subrepresentations `j i : U i ⟶ P i`,
through morphisms `π i : A ⟶ P i`: an element of `A` is determined by its components, its components
lie in `U i` for all but finitely many `i`, and every family of components lying in `U i` for all but
finitely many `i` comes from an element. For a finite group `G` and `n : ℕ` such that
`Hⁿ⁺¹(G, U i) = 0` for all but finitely many `i`:

* `IsRestrictedProduct.eq_zero_of_map_eq_zero`: a class of `Hⁿ⁺¹(G, A)` whose image in every
  `Hⁿ⁺¹(G, P i)` vanishes is zero;
* `IsRestrictedProduct.finite_map_ne_zero`: the image of a class of `Hⁿ⁺¹(G, A)` in `Hⁿ⁺¹(G, P i)` is
  nonzero for only finitely many `i`.

**Cochains.** For representations `A`, `B` of a group `G` (inhomogeneous cochains):
`hom_inhomogeneousCochains_d_apply`: a morphism `φ : A ⟶ B` commutes with the differential;
`π_eq_zero_iff_exists_d_eq`: an `(n+1)`-cocycle has zero class exactly when it is the differential of
an `n`-cochain; `π_cocyclesMk_eq_zero`: the class of a differential is zero;
`iCocycles_cocyclesMap_id_apply`, `map_id_π_apply`: the image of a cocycle and of its class under `φ`.

**Change of group.** For a homomorphism `f : G' →* G`, short exact sequences `X` of representations
of `G` and `Y` of representations of `G'`, and a morphism `α : Res_f X ⟶ Y` of short complexes:

* `inhomogeneousCochainsShortComplexMapAlong f α`: the induced morphism of short complexes of
  inhomogeneous cochain complexes;
* `groupCohomology_δ_comp_map`: **the connecting homomorphism is natural**,
  `δ_X ≫ map f α₁ = map f α₃ ≫ δ_Y` (with its `reassoc` form `groupCohomology_δ_comp_map_assoc`).

`bijective_groupCohomology_map`: the map `Hⁿ(G, A) → Hⁿ(H, B)` along a bijective homomorphism
`f : H →* G` and a bijective coefficient map `Res_f A ⟶ B` is bijective (it is the map of Mathlib's
`groupCohomology.mapIso` for the inverse isomorphisms).

## Complete types

As printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.Cohomology.hom_inhomogeneousCochains_d_apply.{u} {k G : Type u} [CommRing k] [Group G]
  {A B : Rep.{u, u, u} k G} (φ : A ⟶ B) {n : ℕ} (f : (Fin n → G) → ↑A) (g : Fin (n + 1) → G) :
  (Rep.Hom.hom φ) ((CategoryTheory.ConcreteCategory.hom (inhomogeneousCochains.d A n)) f g) =
    (CategoryTheory.ConcreteCategory.hom (inhomogeneousCochains.d B n)) (fun x => (Rep.Hom.hom φ) (f x)) g
Langlands.Cohomology.π_eq_zero_iff_exists_d_eq.{u} {k G : Type u} [CommRing k] [Group G] {A : Rep.{u, u, u} k G} {n : ℕ}
  (z : ↑(groupCohomology.cocycles A (n + 1))) :
  (CategoryTheory.ConcreteCategory.hom (groupCohomology.π A (n + 1))) z = 0 ↔
    ∃ β,
      (CategoryTheory.ConcreteCategory.hom (inhomogeneousCochains.d A n)) β =
        (CategoryTheory.ConcreteCategory.hom (groupCohomology.iCocycles A (n + 1))) z
Langlands.Cohomology.π_cocyclesMk_eq_zero.{u} {k G : Type u} [CommRing k] [Group G] {A : Rep.{u, u, u} k G} {n : ℕ}
  (f : (Fin (n + 1) → G) → ↑A) (hf : (CategoryTheory.ConcreteCategory.hom (inhomogeneousCochains.d A (n + 1))) f = 0)
  (β : (Fin n → G) → ↑A) (hβ : (CategoryTheory.ConcreteCategory.hom (inhomogeneousCochains.d A n)) β = f) :
  (CategoryTheory.ConcreteCategory.hom (groupCohomology.π A (n + 1))) (groupCohomology.cocyclesMk f hf) = 0
Langlands.Cohomology.iCocycles_cocyclesMap_id_apply.{u} {k G : Type u} [CommRing k] [Group G] {A B : Rep.{u, u, u} k G}
  (φ : A ⟶ B) {n : ℕ} (z : ↑(groupCohomology.cocycles A n)) (g : Fin n → G) :
  (CategoryTheory.ConcreteCategory.hom (groupCohomology.iCocycles B n))
      ((CategoryTheory.ConcreteCategory.hom (groupCohomology.cocyclesMap (MonoidHom.id G) φ n)) z) g =
    (Rep.Hom.hom φ) ((CategoryTheory.ConcreteCategory.hom (groupCohomology.iCocycles A n)) z g)
Langlands.Cohomology.map_id_π_apply.{u} {k G : Type u} [CommRing k] [Group G] {A B : Rep.{u, u, u} k G} (φ : A ⟶ B)
  {n : ℕ} (z : ↑(groupCohomology.cocycles A n)) :
  (CategoryTheory.ConcreteCategory.hom (groupCohomology.map (MonoidHom.id G) φ n))
      ((CategoryTheory.ConcreteCategory.hom (groupCohomology.π A n)) z) =
    (CategoryTheory.ConcreteCategory.hom (groupCohomology.π B n))
      ((CategoryTheory.ConcreteCategory.hom (groupCohomology.cocyclesMap (MonoidHom.id G) φ n)) z)
Langlands.Cohomology.IsRestrictedProduct.{u, v} {k G : Type u} [CommRing k] [Group G] {ι : Type v}
  {A : Rep.{u, u, u} k G} {P U : ι → Rep.{u, u, u} k G} (π : (i : ι) → A ⟶ P i) (j : (i : ι) → U i ⟶ P i) : Prop
Langlands.Cohomology.IsRestrictedProduct.eq_zero_of_map_eq_zero.{u, v} {k G : Type u} [CommRing k] [Group G]
  {ι : Type v} {A : Rep.{u, u, u} k G} {P U : ι → Rep.{u, u, u} k G} {π : (i : ι) → A ⟶ P i} {j : (i : ι) → U i ⟶ P i}
  [Finite G] (h : Langlands.Cohomology.IsRestrictedProduct π j) (n : ℕ)
  (hU : {i | ¬CategoryTheory.Limits.IsZero (groupCohomology (U i) (n + 1))}.Finite) (x : ↑(groupCohomology A (n + 1)))
  (hx : ∀ (i : ι), (CategoryTheory.ConcreteCategory.hom (groupCohomology.map (MonoidHom.id G) (π i) (n + 1))) x = 0) :
  x = 0
Langlands.Cohomology.IsRestrictedProduct.finite_map_ne_zero.{u, v} {k G : Type u} [CommRing k] [Group G] {ι : Type v}
  {A : Rep.{u, u, u} k G} {P U : ι → Rep.{u, u, u} k G} {π : (i : ι) → A ⟶ P i} {j : (i : ι) → U i ⟶ P i} [Finite G]
  (h : Langlands.Cohomology.IsRestrictedProduct π j) (n : ℕ)
  (hU : {i | ¬CategoryTheory.Limits.IsZero (groupCohomology (U i) (n + 1))}.Finite) (x : ↑(groupCohomology A (n + 1))) :
  {i | (CategoryTheory.ConcreteCategory.hom (groupCohomology.map (MonoidHom.id G) (π i) (n + 1))) x ≠ 0}.Finite
Langlands.Cohomology.inhomogeneousCochainsShortComplexMapAlong.{u} {k G G' : Type u} [CommRing k] [Group G] [Group G']
  (f : G' →* G) {X : CategoryTheory.ShortComplex (Rep.{u, u, u} k G)}
  {Y : CategoryTheory.ShortComplex (Rep.{u, u, u} k G')} (α : X.map (Rep.resFunctor f) ⟶ Y) :
  X.map (groupCohomology.cochainsFunctor k G) ⟶ Y.map (groupCohomology.cochainsFunctor k G')
Langlands.Cohomology.groupCohomology_δ_comp_map.{u} {k G G' : Type u} [CommRing k] [Group G] [Group G'] (f : G' →* G)
  {X : CategoryTheory.ShortComplex (Rep.{u, u, u} k G)} {Y : CategoryTheory.ShortComplex (Rep.{u, u, u} k G')}
  (α : X.map (Rep.resFunctor f) ⟶ Y) (hX : X.ShortExact) (hY : Y.ShortExact) (i j : ℕ) (hij : i + 1 = j) :
  CategoryTheory.CategoryStruct.comp (groupCohomology.δ hX i j hij) (groupCohomology.map f α.τ₁ j) =
    CategoryTheory.CategoryStruct.comp (groupCohomology.map f α.τ₃ i) (groupCohomology.δ hY i j hij)
Langlands.Cohomology.bijective_groupCohomology_map.{u} {k G H : Type u} [CommRing k] [Group G] [Group H]
  {A : Rep.{u, u, u} k G} {B : Rep.{u, u, u} k H} (f : H →* G) (hf : Function.Bijective ⇑f) (φ : Rep.res f A ⟶ B)
  (hφ : Function.Bijective ⇑(Rep.Hom.hom φ)) (n : ℕ) :
  Function.Bijective ⇑(CategoryTheory.ConcreteCategory.hom (groupCohomology.map f φ n))
```

## Outline of the proofs

A cochain of degree `n + 1` of a finite group takes finitely many values, so its components lie in
`U i` outside a finite set `T` of indices, which may be enlarged by the finitely many `i` with
`Hⁿ⁺¹(G, U i) ≠ 0`. For `i ∉ T` the `i`-th component of a cocycle `f` lifts to a cocycle of `U i`,
which is a differential `d β'ᵢ`; so the component of `f` is `d (j i ∘ β'ᵢ)` and its class vanishes
(finite support). If moreover the classes of all components vanish, choose primitives `βᵢ` of the
components, in `U i` for `i ∉ T`; for each argument the family `(βᵢ(g))ᵢ` lies in the restricted
product and so comes from an element `b(g)` of `A`, and `d b = f` because both sides have the same
components. This is the argument of Tate for the idèles (Cassels–Fröhlich, Chapter VII, §7,
Proposition 7.3), written for an abstract restricted product and the cohomology in one degree.

The naturality of `δ` is `HomologicalComplex.HomologySequence.δ_naturality` for the morphism of short
exact sequences of cochain complexes `inhomogeneousCochainsShortComplexMapAlong f α` (a cochain `x` goes
to `α ∘ x ∘ fⁿ`). The bijectivity is `groupCohomology.map_congr` with `groupCohomology.mapIso`.

## Declarations

`hom_inhomogeneousCochains_d_apply`, `π_eq_zero_iff_exists_d_eq`, `π_cocyclesMk_eq_zero`,
`iCocycles_cocyclesMap_id_apply`, `map_id_π_apply`, `IsRestrictedProduct`,
`IsRestrictedProduct.eq_zero_of_map_eq_zero`, `IsRestrictedProduct.finite_map_ne_zero`,
`inhomogeneousCochainsShortComplexMapAlong`, `groupCohomology_δ_comp_map`,
`bijective_groupCohomology_map`.

Used by the cohomology of the idèles in
`Langlands.GaloisCohomology.Global.BrauerSequence.HigherDegrees.IdeleDecomposition`
(`IsRestrictedProduct`), `…HigherDegrees.Connecting` (`groupCohomology_δ_comp_map`) and
`…HigherDegrees.RealComponents` (`bijective_groupCohomology_map`).

## Source and licence

New file; it contains no text of the repository `leanprover-community/riemann-hypothesis`.

## References

- J. T. Tate, *Global Class Field Theory*, in J. W. S. Cassels, A. Fröhlich (eds.), *Algebraic Number
  Theory* (Academic Press 1967), Chapter VII, §7, Proposition 7.3, p. 177 (the cohomology of the
  idèles as a direct limit of the cohomology of products, computed factor by factor).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008,
  corrected printing 2013), Chapter I, §5, p. 45 (the maps on cohomology of a compatible pair
  `G' → G`, `A → A'`), and Proposition (1.5.2), p. 48 (inflation, restriction, corestriction and
  conjugation commute with `δ`; the proof on cochains is the one used here for any compatible pair).
