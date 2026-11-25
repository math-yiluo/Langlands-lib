# Transport of cohomology with compact support along isomorphisms

`Langlands/GaloisCohomology/CompactSupport/Transport.lean`, namespace `Langlands.GaloisCohomology`.

Let `θ : G ≃ₜ* G'` be an isomorphism of topological groups, `(φ_i : H_i →ₜ* G)_{i ∈ ι}` and
`(φ'_j : H'_j →ₜ* G')_{j ∈ ι'}` two families, `e : ι ≃ ι'` a bijection of the index sets and
`ψ_i : H_i ≃ₜ* H'_{e i}` isomorphisms with `θ ∘ φ_i = φ'_{e i} ∘ ψ_i`. A morphism
`f : Res_θ A' → A` from a `G'`-module to a `G`-module induces maps of cochains compatible with the
localizations (`localRes_transportLocal`), hence a map of cohomology with compact support
`compactTransport : H_cⁿ(G', A') → H_cⁿ(G, A)`, compatible with `H_c → H` and with cup products
(`compactTransport_compactCupRes`). When `f` is an isomorphism, so is `compactTransport`
(`compactTransportIso`), by the five lemma for mapping cocones.

This is used to identify the cohomology with compact support of an open subgroup of `G_S`, with the
Mackey family of local groups, with that of the Galois group `G_{S_L}(L)` of its fixed field.

## Complete types

As printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.bijective_transportLocalMor.{u} {k G G' : Type u} [CommRing k] [Group G] [TopologicalSpace G]
  [Group G'] [TopologicalSpace G'] {ι ι' : Type u} {H : ι → Type u} {H' : ι' → Type u} [(i : ι) → Group (H i)]
  [(i : ι) → TopologicalSpace (H i)] [(j : ι') → Group (H' j)] [(j : ι') → TopologicalSpace (H' j)]
  (φ : (i : ι) → H i →ₜ* G) (φ' : (j : ι') → H' j →ₜ* G') (θ : G ≃ₜ* G') (e : ι ≃ ι') (ψ : (i : ι) → H i ≃ₜ* H' (e i))
  (hcomm : ∀ (i : ι) (h : H i), θ ((φ i) h) = (φ' (e i)) ((ψ i) h)) {A' : Rep.{u, u, u} k G'} {A : Rep.{u, u, u} k G}
  (f : Rep.res (↑θ) A' ≅ A) (i : ι) :
  Function.Bijective ⇑(Rep.Hom.hom (Langlands.GaloisCohomology.transportLocalMor φ φ' θ e ψ hcomm f.hom i))
Langlands.GaloisCohomology.cochainsMap_cupPairingCochains.{u} {k : Type u} [CommRing k] {K₁ K₂ : Type u} [Group K₁]
  [TopologicalSpace K₁] [IsTopologicalGroup K₁] [Group K₂] [TopologicalSpace K₂] [IsTopologicalGroup K₂]
  (ι₀ : K₁ →ₜ* K₂) {A B C : Rep.{u, u, u} k K₂} [Langlands.IsSmoothRep A] [Langlands.IsSmoothRep B]
  [Langlands.IsSmoothRep C] {A₁ B₁ C₁ : Rep.{u, u, u} k K₁} [Langlands.IsSmoothRep A₁] [Langlands.IsSmoothRep B₁]
  [Langlands.IsSmoothRep C₁] (a : Rep.res (↑ι₀) A ⟶ A₁) (b : Rep.res (↑ι₀) B ⟶ B₁) (c : Rep.res (↑ι₀) C ⟶ C₁)
  (μ : CategoryTheory.MonoidalCategoryStruct.tensorObj A B ⟶ C)
  (μ₁ : CategoryTheory.MonoidalCategoryStruct.tensorObj A₁ B₁ ⟶ C₁)
  (hμ :
    CategoryTheory.CategoryStruct.comp ((Rep.resFunctor ↑ι₀).map μ) c =
      CategoryTheory.CategoryStruct.comp (Langlands.ProfiniteCohomology.resTensorHom (↑ι₀) a b) μ₁)
  {r s n : ℕ} (h : r + s = n) (x : ↑((Langlands.ProfiniteCohomology.cochains A).X r))
  (z : ↑((Langlands.ProfiniteCohomology.cochains B).X s)) :
  (ModuleCat.Hom.hom ((Langlands.ProfiniteCohomology.cochainsMap ι₀ c).f n))
      (((Langlands.GaloisCohomology.cupPairingCochains μ h) x) z) =
    ((Langlands.GaloisCohomology.cupPairingCochains μ₁ h)
        ((ModuleCat.Hom.hom ((Langlands.ProfiniteCohomology.cochainsMap ι₀ a).f r)) x))
      ((ModuleCat.Hom.hom ((Langlands.ProfiniteCohomology.cochainsMap ι₀ b).f s)) z)
Langlands.GaloisCohomology.compactTransport.{u} {k G G' : Type u} [CommRing k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] {ι ι' : Type u} {H : ι → Type u}
  {H' : ι' → Type u} [(i : ι) → Group (H i)] [(i : ι) → TopologicalSpace (H i)] [∀ (i : ι), IsTopologicalGroup (H i)]
  [(j : ι') → Group (H' j)] [(j : ι') → TopologicalSpace (H' j)] [∀ (j : ι'), IsTopologicalGroup (H' j)]
  (φ : (i : ι) → H i →ₜ* G) (φ' : (j : ι') → H' j →ₜ* G') (θ : G ≃ₜ* G') (e : ι ≃ ι') (ψ : (i : ι) → H i ≃ₜ* H' (e i))
  (hcomm : ∀ (i : ι) (h : H i), θ ((φ i) h) = (φ' (e i)) ((ψ i) h)) {A' : Rep.{u, u, u} k G'} [Langlands.IsSmoothRep A']
  {A : Rep.{u, u, u} k G} [Langlands.IsSmoothRep A] (f : Rep.res (↑θ) A' ⟶ A) (n : ℕ) :
  Langlands.GaloisCohomology.compactSupportCohomologyRes φ' A' n ⟶
    Langlands.GaloisCohomology.compactSupportCohomologyRes φ A n
Langlands.GaloisCohomology.compactTransportCochains.{u} {k G G' : Type u} [CommRing k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] {ι ι' : Type u} {H : ι → Type u}
  {H' : ι' → Type u} [(i : ι) → Group (H i)] [(i : ι) → TopologicalSpace (H i)] [∀ (i : ι), IsTopologicalGroup (H i)]
  [(j : ι') → Group (H' j)] [(j : ι') → TopologicalSpace (H' j)] [∀ (j : ι'), IsTopologicalGroup (H' j)]
  (φ : (i : ι) → H i →ₜ* G) (φ' : (j : ι') → H' j →ₜ* G') (θ : G ≃ₜ* G') (e : ι ≃ ι') (ψ : (i : ι) → H i ≃ₜ* H' (e i))
  (hcomm : ∀ (i : ι) (h : H i), θ ((φ i) h) = (φ' (e i)) ((ψ i) h)) {A' : Rep.{u, u, u} k G'} [Langlands.IsSmoothRep A']
  {A : Rep.{u, u, u} k G} [Langlands.IsSmoothRep A] (f : Rep.res (↑θ) A' ⟶ A) :
  (Langlands.GaloisCohomology.compactSupportCochains φ' A' (fun j => Rep.res (↑(φ' j)) A') fun x =>
      CategoryTheory.CategoryStruct.id (Rep.res (↑(φ' x)) A')) ⟶
    Langlands.GaloisCohomology.compactSupportCochains φ A (fun i => Rep.res (↑(φ i)) A) fun x =>
      CategoryTheory.CategoryStruct.id (Rep.res (↑(φ x)) A)
Langlands.GaloisCohomology.compactTransportIso.{u} {k G G' : Type u} [CommRing k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] {ι ι' : Type u} {H : ι → Type u}
  {H' : ι' → Type u} [(i : ι) → Group (H i)] [(i : ι) → TopologicalSpace (H i)] [∀ (i : ι), IsTopologicalGroup (H i)]
  [(j : ι') → Group (H' j)] [(j : ι') → TopologicalSpace (H' j)] [∀ (j : ι'), IsTopologicalGroup (H' j)]
  (φ : (i : ι) → H i →ₜ* G) (φ' : (j : ι') → H' j →ₜ* G') (θ : G ≃ₜ* G') (e : ι ≃ ι') (ψ : (i : ι) → H i ≃ₜ* H' (e i))
  (hcomm : ∀ (i : ι) (h : H i), θ ((φ i) h) = (φ' (e i)) ((ψ i) h)) {A' : Rep.{u, u, u} k G'} [Langlands.IsSmoothRep A']
  {A : Rep.{u, u, u} k G} [Langlands.IsSmoothRep A] (f : Rep.res (↑θ) A' ≅ A) (n : ℕ) :
  Langlands.GaloisCohomology.compactSupportCohomologyRes φ' A' n ≅
    Langlands.GaloisCohomology.compactSupportCohomologyRes φ A n
Langlands.GaloisCohomology.compactTransportIso_hom.{u} {k G G' : Type u} [CommRing k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] {ι ι' : Type u} {H : ι → Type u}
  {H' : ι' → Type u} [(i : ι) → Group (H i)] [(i : ι) → TopologicalSpace (H i)] [∀ (i : ι), IsTopologicalGroup (H i)]
  [(j : ι') → Group (H' j)] [(j : ι') → TopologicalSpace (H' j)] [∀ (j : ι'), IsTopologicalGroup (H' j)]
  (φ : (i : ι) → H i →ₜ* G) (φ' : (j : ι') → H' j →ₜ* G') (θ : G ≃ₜ* G') (e : ι ≃ ι') (ψ : (i : ι) → H i ≃ₜ* H' (e i))
  (hcomm : ∀ (i : ι) (h : H i), θ ((φ i) h) = (φ' (e i)) ((ψ i) h)) {A' : Rep.{u, u, u} k G'} [Langlands.IsSmoothRep A']
  {A : Rep.{u, u, u} k G} [Langlands.IsSmoothRep A] (f : Rep.res (↑θ) A' ≅ A) (n : ℕ) :
  (Langlands.GaloisCohomology.compactTransportIso φ φ' θ e ψ hcomm f n).hom =
    Langlands.GaloisCohomology.compactTransport φ φ' θ e ψ hcomm f.hom n
Langlands.GaloisCohomology.compactTransport_compactCupRes.{u} {k G G' : Type u} [CommRing k] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] {ι ι' : Type u}
  {H : ι → Type u} {H' : ι' → Type u} [(i : ι) → Group (H i)] [(i : ι) → TopologicalSpace (H i)]
  [∀ (i : ι), IsTopologicalGroup (H i)] [(j : ι') → Group (H' j)] [(j : ι') → TopologicalSpace (H' j)]
  [∀ (j : ι'), IsTopologicalGroup (H' j)] (φ : (i : ι) → H i →ₜ* G) (φ' : (j : ι') → H' j →ₜ* G') (θ : G ≃ₜ* G')
  (e : ι ≃ ι') (ψ : (i : ι) → H i ≃ₜ* H' (e i)) (hcomm : ∀ (i : ι) (h : H i), θ ((φ i) h) = (φ' (e i)) ((ψ i) h))
  {A' B' C' : Rep.{u, u, u} k G'} [Langlands.IsSmoothRep A'] [Langlands.IsSmoothRep B'] [Langlands.IsSmoothRep C']
  {A B C : Rep.{u, u, u} k G} [Langlands.IsSmoothRep A] [Langlands.IsSmoothRep B] [Langlands.IsSmoothRep C]
  (fA : Rep.res (↑θ) A' ⟶ A) (fB : Rep.res (↑θ) B' ⟶ B) (fC : Rep.res (↑θ) C' ⟶ C)
  (μ' : CategoryTheory.MonoidalCategoryStruct.tensorObj A' B' ⟶ C')
  (μ : CategoryTheory.MonoidalCategoryStruct.tensorObj A B ⟶ C)
  (hμ :
    CategoryTheory.CategoryStruct.comp ((Rep.resFunctor ↑θ).map μ') fC =
      CategoryTheory.CategoryStruct.comp (Langlands.ProfiniteCohomology.resTensorHom (↑θ) fA fB) μ)
  {r s n : ℕ} (h : r + s = n) (y : ↑(Langlands.GaloisCohomology.compactSupportCohomologyRes φ' A' r))
  (x : ↑(Langlands.ProfiniteCohomology.cohomology B' s)) :
  (ModuleCat.Hom.hom (Langlands.GaloisCohomology.compactTransport φ φ' θ e ψ hcomm fC n))
      (((Langlands.GaloisCohomology.compactCupRes φ' μ' h) y) x) =
    ((Langlands.GaloisCohomology.compactCupRes φ μ h)
        ((ModuleCat.Hom.hom (Langlands.GaloisCohomology.compactTransport φ φ' θ e ψ hcomm fA r)) y))
      ((ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.map (↑θ) fB s)) x)
Langlands.GaloisCohomology.compactTransport_compactToGlobal.{u} {k G G' : Type u} [CommRing k] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] {ι ι' : Type u}
  {H : ι → Type u} {H' : ι' → Type u} [(i : ι) → Group (H i)] [(i : ι) → TopologicalSpace (H i)]
  [∀ (i : ι), IsTopologicalGroup (H i)] [(j : ι') → Group (H' j)] [(j : ι') → TopologicalSpace (H' j)]
  [∀ (j : ι'), IsTopologicalGroup (H' j)] (φ : (i : ι) → H i →ₜ* G) (φ' : (j : ι') → H' j →ₜ* G') (θ : G ≃ₜ* G')
  (e : ι ≃ ι') (ψ : (i : ι) → H i ≃ₜ* H' (e i)) (hcomm : ∀ (i : ι) (h : H i), θ ((φ i) h) = (φ' (e i)) ((ψ i) h))
  {A' : Rep.{u, u, u} k G'} [Langlands.IsSmoothRep A'] {A : Rep.{u, u, u} k G} [Langlands.IsSmoothRep A]
  (f : Rep.res (↑θ) A' ⟶ A) (n : ℕ) :
  CategoryTheory.CategoryStruct.comp (Langlands.GaloisCohomology.compactTransport φ φ' θ e ψ hcomm f n)
      (Langlands.GaloisCohomology.compactToGlobal φ A (fun x => Rep.res (↑(φ x)) A)
        (fun x => CategoryTheory.CategoryStruct.id (Rep.res (↑(φ x)) A)) n) =
    CategoryTheory.CategoryStruct.comp
      (Langlands.GaloisCohomology.compactToGlobal φ' A' (fun x => Rep.res (↑(φ' x)) A')
        (fun x => CategoryTheory.CategoryStruct.id (Rep.res (↑(φ' x)) A')) n)
      (Langlands.ProfiniteCohomology.map (↑θ) f n)
Langlands.GaloisCohomology.homologyMap_transportLocal_localCohomologyIso.{u} {k G G' : Type u} [CommRing k] [Group G]
  [TopologicalSpace G] [Group G'] [TopologicalSpace G'] {ι ι' : Type u} {H : ι → Type u} {H' : ι' → Type u}
  [(i : ι) → Group (H i)] [(i : ι) → TopologicalSpace (H i)] [∀ (i : ι), IsTopologicalGroup (H i)]
  [(j : ι') → Group (H' j)] [(j : ι') → TopologicalSpace (H' j)] [∀ (j : ι'), IsTopologicalGroup (H' j)]
  (φ : (i : ι) → H i →ₜ* G) (φ' : (j : ι') → H' j →ₜ* G') (θ : G ≃ₜ* G') (e : ι ≃ ι') (ψ : (i : ι) → H i ≃ₜ* H' (e i))
  (hcomm : ∀ (i : ι) (h : H i), θ ((φ i) h) = (φ' (e i)) ((ψ i) h)) {A' : Rep.{u, u, u} k G'} [Langlands.IsSmoothRep A']
  {A : Rep.{u, u, u} k G} [Langlands.IsSmoothRep A] (f : Rep.res (↑θ) A' ⟶ A) (n : ℕ) :
  CategoryTheory.CategoryStruct.comp
      (HomologicalComplex.homologyMap (Langlands.GaloisCohomology.transportLocal φ φ' θ e ψ hcomm f) n)
      (Langlands.GaloisCohomology.localCohomologyIso (fun i => Rep.res (↑(φ i)) A) n).hom =
    CategoryTheory.CategoryStruct.comp
      (Langlands.GaloisCohomology.localCohomologyIso (fun j => Rep.res (↑(φ' j)) A') n).hom
      (Langlands.GaloisCohomology.transportLocalCohomology φ φ' θ e ψ hcomm f n)
Langlands.GaloisCohomology.homotopy_ofEq_hom_apply.{u} {k : Type u} [CommRing k] {C D : CochainComplex (ModuleCat k) ℕ}
  {f g : C ⟶ D} (h : f = g) (i j : ℕ) (x : ↑(C.X i)) : (ModuleCat.Hom.hom ((Homotopy.ofEq h).hom i j)) x = 0
Langlands.GaloisCohomology.isIso_compactTransport.{u} {k G G' : Type u} [CommRing k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] {ι ι' : Type u} {H : ι → Type u}
  {H' : ι' → Type u} [(i : ι) → Group (H i)] [(i : ι) → TopologicalSpace (H i)] [∀ (i : ι), IsTopologicalGroup (H i)]
  [(j : ι') → Group (H' j)] [(j : ι') → TopologicalSpace (H' j)] [∀ (j : ι'), IsTopologicalGroup (H' j)]
  (φ : (i : ι) → H i →ₜ* G) (φ' : (j : ι') → H' j →ₜ* G') (θ : G ≃ₜ* G') (e : ι ≃ ι') (ψ : (i : ι) → H i ≃ₜ* H' (e i))
  (hcomm : ∀ (i : ι) (h : H i), θ ((φ i) h) = (φ' (e i)) ((ψ i) h)) {A' : Rep.{u, u, u} k G'} [Langlands.IsSmoothRep A']
  {A : Rep.{u, u, u} k G} [Langlands.IsSmoothRep A] (f : Rep.res (↑θ) A' ≅ A) (n : ℕ) :
  CategoryTheory.IsIso (Langlands.GaloisCohomology.compactTransport φ φ' θ e ψ hcomm f.hom n)
Langlands.GaloisCohomology.isIso_homologyMap_transportGlobal.{u} {k G G' : Type u} [CommRing k] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] (θ : G ≃ₜ* G')
  {A' : Rep.{u, u, u} k G'} [Langlands.IsSmoothRep A'] {A : Rep.{u, u, u} k G} [Langlands.IsSmoothRep A]
  (f : Rep.res (↑θ) A' ≅ A) (n : ℕ) :
  CategoryTheory.IsIso (HomologicalComplex.homologyMap (Langlands.GaloisCohomology.transportGlobal θ f.hom) n)
Langlands.GaloisCohomology.isIso_homologyMap_transportLocal.{u} {k G G' : Type u} [CommRing k] [Group G]
  [TopologicalSpace G] [Group G'] [TopologicalSpace G'] {ι ι' : Type u} {H : ι → Type u} {H' : ι' → Type u}
  [(i : ι) → Group (H i)] [(i : ι) → TopologicalSpace (H i)] [∀ (i : ι), IsTopologicalGroup (H i)]
  [(j : ι') → Group (H' j)] [(j : ι') → TopologicalSpace (H' j)] [∀ (j : ι'), IsTopologicalGroup (H' j)]
  (φ : (i : ι) → H i →ₜ* G) (φ' : (j : ι') → H' j →ₜ* G') (θ : G ≃ₜ* G') (e : ι ≃ ι') (ψ : (i : ι) → H i ≃ₜ* H' (e i))
  (hcomm : ∀ (i : ι) (h : H i), θ ((φ i) h) = (φ' (e i)) ((ψ i) h)) {A' : Rep.{u, u, u} k G'} [Langlands.IsSmoothRep A']
  {A : Rep.{u, u, u} k G} [Langlands.IsSmoothRep A] (f : Rep.res (↑θ) A' ≅ A) (n : ℕ) :
  CategoryTheory.IsIso
    (HomologicalComplex.homologyMap (Langlands.GaloisCohomology.transportLocal φ φ' θ e ψ hcomm f.hom) n)
Langlands.GaloisCohomology.localRes_transportLocal.{u} {k G G' : Type u} [CommRing k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] {ι ι' : Type u} {H : ι → Type u}
  {H' : ι' → Type u} [(i : ι) → Group (H i)] [(i : ι) → TopologicalSpace (H i)] [∀ (i : ι), IsTopologicalGroup (H i)]
  [(j : ι') → Group (H' j)] [(j : ι') → TopologicalSpace (H' j)] [∀ (j : ι'), IsTopologicalGroup (H' j)]
  (φ : (i : ι) → H i →ₜ* G) (φ' : (j : ι') → H' j →ₜ* G') (θ : G ≃ₜ* G') (e : ι ≃ ι') (ψ : (i : ι) → H i ≃ₜ* H' (e i))
  (hcomm : ∀ (i : ι) (h : H i), θ ((φ i) h) = (φ' (e i)) ((ψ i) h)) {A' : Rep.{u, u, u} k G'} [Langlands.IsSmoothRep A']
  {A : Rep.{u, u, u} k G} [Langlands.IsSmoothRep A] (f : Rep.res (↑θ) A' ⟶ A) :
  CategoryTheory.CategoryStruct.comp
      (Langlands.GaloisCohomology.localRes φ' A' (fun j => Rep.res (↑(φ' j)) A') fun x =>
        CategoryTheory.CategoryStruct.id (Rep.res (↑(φ' x)) A'))
      (Langlands.GaloisCohomology.transportLocal φ φ' θ e ψ hcomm f) =
    CategoryTheory.CategoryStruct.comp (Langlands.GaloisCohomology.transportGlobal θ f)
      (Langlands.GaloisCohomology.localRes φ A (fun i => Rep.res (↑(φ i)) A) fun x =>
        CategoryTheory.CategoryStruct.id (Rep.res (↑(φ x)) A))
Langlands.GaloisCohomology.transportGlobal.{u} {k G G' : Type u} [CommRing k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] (θ : G ≃ₜ* G')
  {A' : Rep.{u, u, u} k G'} [Langlands.IsSmoothRep A'] {A : Rep.{u, u, u} k G} [Langlands.IsSmoothRep A]
  (f : Rep.res (↑θ) A' ⟶ A) : Langlands.ProfiniteCohomology.cochains A' ⟶ Langlands.ProfiniteCohomology.cochains A
Langlands.GaloisCohomology.transportLocal.{u} {k G G' : Type u} [CommRing k] [Group G] [TopologicalSpace G] [Group G']
  [TopologicalSpace G'] {ι ι' : Type u} {H : ι → Type u} {H' : ι' → Type u} [(i : ι) → Group (H i)]
  [(i : ι) → TopologicalSpace (H i)] [∀ (i : ι), IsTopologicalGroup (H i)] [(j : ι') → Group (H' j)]
  [(j : ι') → TopologicalSpace (H' j)] [∀ (j : ι'), IsTopologicalGroup (H' j)] (φ : (i : ι) → H i →ₜ* G)
  (φ' : (j : ι') → H' j →ₜ* G') (θ : G ≃ₜ* G') (e : ι ≃ ι') (ψ : (i : ι) → H i ≃ₜ* H' (e i))
  (hcomm : ∀ (i : ι) (h : H i), θ ((φ i) h) = (φ' (e i)) ((ψ i) h)) {A' : Rep.{u, u, u} k G'} [Langlands.IsSmoothRep A']
  {A : Rep.{u, u, u} k G} [Langlands.IsSmoothRep A] (f : Rep.res (↑θ) A' ⟶ A) :
  (Langlands.GaloisCohomology.piComplex fun j => Langlands.ProfiniteCohomology.cochains (Rep.res (↑(φ' j)) A')) ⟶
    Langlands.GaloisCohomology.piComplex fun i => Langlands.ProfiniteCohomology.cochains (Rep.res (↑(φ i)) A)
Langlands.GaloisCohomology.transportLocalCohomology.{u} {k G G' : Type u} [CommRing k] [Group G] [TopologicalSpace G]
  [Group G'] [TopologicalSpace G'] {ι ι' : Type u} {H : ι → Type u} {H' : ι' → Type u} [(i : ι) → Group (H i)]
  [(i : ι) → TopologicalSpace (H i)] [∀ (i : ι), IsTopologicalGroup (H i)] [(j : ι') → Group (H' j)]
  [(j : ι') → TopologicalSpace (H' j)] [∀ (j : ι'), IsTopologicalGroup (H' j)] (φ : (i : ι) → H i →ₜ* G)
  (φ' : (j : ι') → H' j →ₜ* G') (θ : G ≃ₜ* G') (e : ι ≃ ι') (ψ : (i : ι) → H i ≃ₜ* H' (e i))
  (hcomm : ∀ (i : ι) (h : H i), θ ((φ i) h) = (φ' (e i)) ((ψ i) h)) {A' : Rep.{u, u, u} k G'} [Langlands.IsSmoothRep A']
  {A : Rep.{u, u, u} k G} [Langlands.IsSmoothRep A] (f : Rep.res (↑θ) A' ⟶ A) (n : ℕ) :
  ↧((j : ι') → ↑(Langlands.ProfiniteCohomology.cohomology (Rep.res (↑(φ' j)) A') n)) ⟶
    ↧((i : ι) → ↑(Langlands.ProfiniteCohomology.cohomology (Rep.res (↑(φ i)) A) n))
Langlands.GaloisCohomology.transportLocalCohomology_bijective.{u} {k G G' : Type u} [CommRing k] [Group G]
  [TopologicalSpace G] [Group G'] [TopologicalSpace G'] {ι ι' : Type u} {H : ι → Type u} {H' : ι' → Type u}
  [(i : ι) → Group (H i)] [(i : ι) → TopologicalSpace (H i)] [∀ (i : ι), IsTopologicalGroup (H i)]
  [(j : ι') → Group (H' j)] [(j : ι') → TopologicalSpace (H' j)] [∀ (j : ι'), IsTopologicalGroup (H' j)]
  (φ : (i : ι) → H i →ₜ* G) (φ' : (j : ι') → H' j →ₜ* G') (θ : G ≃ₜ* G') (e : ι ≃ ι') (ψ : (i : ι) → H i ≃ₜ* H' (e i))
  (hcomm : ∀ (i : ι) (h : H i), θ ((φ i) h) = (φ' (e i)) ((ψ i) h)) {A' : Rep.{u, u, u} k G'} [Langlands.IsSmoothRep A']
  {A : Rep.{u, u, u} k G} [Langlands.IsSmoothRep A] (f : Rep.res (↑θ) A' ≅ A) (n : ℕ) :
  Function.Bijective ⇑(ModuleCat.Hom.hom (Langlands.GaloisCohomology.transportLocalCohomology φ φ' θ e ψ hcomm f.hom n))
Langlands.GaloisCohomology.transportLocalMor.{u} {k G G' : Type u} [CommRing k] [Group G] [TopologicalSpace G]
  [Group G'] [TopologicalSpace G'] {ι ι' : Type u} {H : ι → Type u} {H' : ι' → Type u} [(i : ι) → Group (H i)]
  [(i : ι) → TopologicalSpace (H i)] [(j : ι') → Group (H' j)] [(j : ι') → TopologicalSpace (H' j)]
  (φ : (i : ι) → H i →ₜ* G) (φ' : (j : ι') → H' j →ₜ* G') (θ : G ≃ₜ* G') (e : ι ≃ ι') (ψ : (i : ι) → H i ≃ₜ* H' (e i))
  (hcomm : ∀ (i : ι) (h : H i), θ ((φ i) h) = (φ' (e i)) ((ψ i) h)) {A' : Rep.{u, u, u} k G'} {A : Rep.{u, u, u} k G}
  (f : Rep.res (↑θ) A' ⟶ A) (i : ι) : Rep.res (↑(ψ i)) (Rep.res (↑(φ' (e i))) A') ⟶ Rep.res (↑(φ i)) A
Langlands.GaloisCohomology.transportLocalMor_hom_apply.{u} {k G G' : Type u} [CommRing k] [Group G] [TopologicalSpace G]
  [Group G'] [TopologicalSpace G'] {ι ι' : Type u} {H : ι → Type u} {H' : ι' → Type u} [(i : ι) → Group (H i)]
  [(i : ι) → TopologicalSpace (H i)] [(j : ι') → Group (H' j)] [(j : ι') → TopologicalSpace (H' j)]
  (φ : (i : ι) → H i →ₜ* G) (φ' : (j : ι') → H' j →ₜ* G') (θ : G ≃ₜ* G') (e : ι ≃ ι') (ψ : (i : ι) → H i ≃ₜ* H' (e i))
  (hcomm : ∀ (i : ι) (h : H i), θ ((φ i) h) = (φ' (e i)) ((ψ i) h)) {A' : Rep.{u, u, u} k G'} {A : Rep.{u, u, u} k G}
  (f : Rep.res (↑θ) A' ⟶ A) (i : ι) (a : ↑A') :
  (Rep.Hom.hom (Langlands.GaloisCohomology.transportLocalMor φ φ' θ e ψ hcomm f i)) a = (Rep.Hom.hom f) a
Langlands.GaloisCohomology.transportLocalMor_pairing.{u} {k G G' : Type u} [CommRing k] [Group G] [TopologicalSpace G]
  [Group G'] [TopologicalSpace G'] {ι ι' : Type u} {H : ι → Type u} {H' : ι' → Type u} [(i : ι) → Group (H i)]
  [(i : ι) → TopologicalSpace (H i)] [(j : ι') → Group (H' j)] [(j : ι') → TopologicalSpace (H' j)]
  (φ : (i : ι) → H i →ₜ* G) (φ' : (j : ι') → H' j →ₜ* G') (θ : G ≃ₜ* G') (e : ι ≃ ι') (ψ : (i : ι) → H i ≃ₜ* H' (e i))
  (hcomm : ∀ (i : ι) (h : H i), θ ((φ i) h) = (φ' (e i)) ((ψ i) h)) {A' B' C' : Rep.{u, u, u} k G'}
  {A B C : Rep.{u, u, u} k G} (fA : Rep.res (↑θ) A' ⟶ A) (fB : Rep.res (↑θ) B' ⟶ B) (fC : Rep.res (↑θ) C' ⟶ C)
  (μ' : CategoryTheory.MonoidalCategoryStruct.tensorObj A' B' ⟶ C')
  (μ : CategoryTheory.MonoidalCategoryStruct.tensorObj A B ⟶ C)
  (hμ :
    CategoryTheory.CategoryStruct.comp ((Rep.resFunctor ↑θ).map μ') fC =
      CategoryTheory.CategoryStruct.comp (Langlands.ProfiniteCohomology.resTensorHom (↑θ) fA fB) μ)
  (i : ι) :
  CategoryTheory.CategoryStruct.comp ((Rep.resFunctor ↑(ψ i)).map ((Rep.resFunctor ↑(φ' (e i))).map μ'))
      (Langlands.GaloisCohomology.transportLocalMor φ φ' θ e ψ hcomm fC i) =
    CategoryTheory.CategoryStruct.comp
      (Langlands.ProfiniteCohomology.resTensorHom (↑(ψ i))
        (Langlands.GaloisCohomology.transportLocalMor φ φ' θ e ψ hcomm fA i)
        (Langlands.GaloisCohomology.transportLocalMor φ φ' θ e ψ hcomm fB i))
      ((Rep.resFunctor ↑(φ i)).map μ)
Langlands.GaloisCohomology.transportLocal_pi_cup.{u} {k G G' : Type u} [CommRing k] [Group G] [TopologicalSpace G]
  [Group G'] [TopologicalSpace G'] {ι ι' : Type u} {H : ι → Type u} {H' : ι' → Type u} [(i : ι) → Group (H i)]
  [(i : ι) → TopologicalSpace (H i)] [∀ (i : ι), IsTopologicalGroup (H i)] [(j : ι') → Group (H' j)]
  [(j : ι') → TopologicalSpace (H' j)] [∀ (j : ι'), IsTopologicalGroup (H' j)] (φ : (i : ι) → H i →ₜ* G)
  (φ' : (j : ι') → H' j →ₜ* G') (θ : G ≃ₜ* G') (e : ι ≃ ι') (ψ : (i : ι) → H i ≃ₜ* H' (e i))
  (hcomm : ∀ (i : ι) (h : H i), θ ((φ i) h) = (φ' (e i)) ((ψ i) h)) {A' B' C' : Rep.{u, u, u} k G'}
  [Langlands.IsSmoothRep A'] [Langlands.IsSmoothRep B'] [Langlands.IsSmoothRep C'] {A B C : Rep.{u, u, u} k G}
  [Langlands.IsSmoothRep A] [Langlands.IsSmoothRep B] [Langlands.IsSmoothRep C] (fA : Rep.res (↑θ) A' ⟶ A)
  (fB : Rep.res (↑θ) B' ⟶ B) (fC : Rep.res (↑θ) C' ⟶ C)
  (μ' : CategoryTheory.MonoidalCategoryStruct.tensorObj A' B' ⟶ C')
  (μ : CategoryTheory.MonoidalCategoryStruct.tensorObj A B ⟶ C)
  (hμ :
    CategoryTheory.CategoryStruct.comp ((Rep.resFunctor ↑θ).map μ') fC =
      CategoryTheory.CategoryStruct.comp (Langlands.ProfiniteCohomology.resTensorHom (↑θ) fA fB) μ)
  {r s n : ℕ} (hh : r + s = n)
  (y₀ :
    ↑((Langlands.GaloisCohomology.piComplex fun j => Langlands.ProfiniteCohomology.cochains (Rep.res (↑(φ' j)) A')).X
        r))
  (w₀ :
    ↑((Langlands.GaloisCohomology.piComplex fun j => Langlands.ProfiniteCohomology.cochains (Rep.res (↑(φ' j)) B')).X
        s)) :
  (ModuleCat.Hom.hom ((Langlands.GaloisCohomology.transportLocal φ φ' θ e ψ hcomm fC).f n))
      ((((Langlands.GaloisCohomology.LeibnizPairing.pi fun j =>
                Langlands.GaloisCohomology.cupLeibniz ((Rep.resFunctor ↑(φ' j)).map μ')).μ
            hh)
          y₀)
        w₀) =
    (((Langlands.GaloisCohomology.LeibnizPairing.pi fun i =>
              Langlands.GaloisCohomology.cupLeibniz ((Rep.resFunctor ↑(φ i)).map μ)).μ
          hh)
        ((ModuleCat.Hom.hom ((Langlands.GaloisCohomology.transportLocal φ φ' θ e ψ hcomm fA).f r)) y₀))
      ((ModuleCat.Hom.hom ((Langlands.GaloisCohomology.transportLocal φ φ' θ e ψ hcomm fB).f s)) w₀)
```

## Outline of the proofs

The cochain maps are compatible with the localizations (`localRes_transportLocal`), so they induce a map of mapping cocones; when `f` is an isomorphism, the global and local parts are isomorphisms on cohomology (`isIso_map_of_mulEquiv`), hence so is the map of cocones (`mappingCoconeNat.isIso_homologyMap_mapOfHomotopy`). Cup products: cochain-level compatibility (`cochainsMap_cupPairingCochains`) and `mappingCoconeNat.homologyMap_mapOfHomotopy_coconeLeft`.

## Declarations

`transportLocalMor`, `transportLocalMor_hom_apply`, `transportGlobal`, `transportLocal`, `localRes_transportLocal`, `compactTransportCochains`, `compactTransport`, `compactTransport_compactToGlobal`, `transportLocalCohomology`, `homologyMap_transportLocal_localCohomologyIso`, `bijective_transportLocalMor`, `transportLocalCohomology_bijective`, `isIso_homologyMap_transportGlobal`, `isIso_homologyMap_transportLocal`, `isIso_compactTransport`, `compactTransportIso`, `compactTransportIso_hom`, `homotopy_ofEq_hom_apply`, `cochainsMap_cupPairingCochains`, `transportLocalMor_pairing`, `transportLocal_pi_cup`, `compactTransport_compactCupRes`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, file `src/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseTransport.lean`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The Library's cochains and coefficient maps (`cochains`, `cochainsMap`, `map`, `IsSmoothRep`) replace the source's (`cochainsComplex`, `cochainsMapAlong`, `cohomologyMapAlong`, `IsDiscreteRep`).

## References

- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter I, §4, Theorem 4.10, pp. 56–57; chapter II, §2, pp. 165–166 (cohomology with compact support).
