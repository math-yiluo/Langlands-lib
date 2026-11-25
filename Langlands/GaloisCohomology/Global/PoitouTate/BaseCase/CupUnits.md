# Cup products of the Kummer classes with compact support

`Langlands/GaloisCohomology/Global/PoitouTate/BaseCase/CupUnits.lean`, namespace `Langlands.GaloisCohomology.PoitouTate.Internal`.

With the notation of `Langlands.GaloisCohomology.Global.PoitouTate.BaseCase.UnitsData`, this file
computes the cup product of the Kummer class with compact support `δ_c(e)` of a class
`e ∈ H_c¹(G_S, 𝒪_Sˣ; (K̄_vˣ)_v)` with a character `χ ∈ H¹(G_S, ℤ/n)`, after mapping
`μ_n → 𝒪_Sˣ`.

* `compactSupportMap_compactCupRes_kummerCompactδ`: `i_*(δ_c(e) ∪ χ) = e ∪ δχ`, `δχ ∈ H²(G_S, ℤ)`
  the Bockstein of `χ` (for `0 → ℤ → ℤ → ℤ/n → 0`, `bockSeq`) and the cup product along the action
  pairing `𝒪_Sˣ ⊗ ℤ → 𝒪_Sˣ` (`intActPairing`; `unitsCup` with all its arguments explicit): the
  connecting maps of the Kummer sequence with compact support and of the Bockstein sequence commute
  with cup products up to the sign `(-1)^r` (`compactCup_compactSupportδ_add_compactCup_δ`), and the
  maps of coefficients commute with cup products (`compactSupportMap_compactCup`).
* `exists_unitsData_cup_bock`: for a datum `d = (t, a)`, `unitsData d ∪ δχ` is
  `localToCompact (W|_{K_v} + a_v ∪ δχ_v)_v` for a `2`-cocycle `W` of `G_S` in `K_Sˣ` with
  `W(g, h) t^{-c_χ(g, h)} ∈ 𝒪_Sˣ` for all `g, h` (`c_χ = bockInt` the integer cocycle of `δχ`);
  `exists_compactCupRes_kummerCompactδ_unitsData` combines the two.
* `localUnitsCup ι S v a b`: the cup product at `v ∈ S` of a local unit `a ∈ K_vˣ` with a class of
  `H²(G_S, ℤ)` restricted to `G_{K_v}`.

The cone lemmas `coconeLeft_homology_eq_homologyδ`, `exists_coconeLeft_homology_eq_homologyδ`,
`homologyδ_homologyπ_eq_localToCompact` compute the cup product of the class of a cone cycle whose
global part is a coboundary.

## Complete types

As printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.PoitouTate.Internal.mappingCoconeNat_d_hom_apply'.{u} {k : Type u} [CommRing k]
  {K L : CochainComplex (ModuleCat k) ℕ} (f : K ⟶ L) (n : ℕ) (x : ↑(K.X n))
  (y : ↑(Langlands.GaloisCohomology.shiftNegOneX L n)) :
  (ModuleCat.Hom.hom ((Langlands.GaloisCohomology.mappingCoconeNat f).d n (n + 1))) (x, y) =
    ((ModuleCat.Hom.hom (K.d n (n + 1))) x,
      (Langlands.GaloisCohomology.shiftNegOneSucc L n) ((ModuleCat.Hom.hom (f.f n)) x) +
        (ModuleCat.Hom.hom (Langlands.GaloisCohomology.shiftNegOneD L n)) y)
Langlands.GaloisCohomology.PoitouTate.Internal.coconeLeft_homology_eq_homologyδ.{u} {k : Type u} [CommRing k]
  {K L K' L' N N' : CochainComplex (ModuleCat k) ℕ} {f : K ⟶ L} {f' : K' ⟶ L'}
  (μL : Langlands.GaloisCohomology.LeibnizPairing L N' L') (ρ : N ⟶ N')
  (μK : Langlands.GaloisCohomology.LeibnizPairing K N K')
  (hc :
    ∀ {r s n : ℕ} (h : r + s = n) (x : ↑(K.X r)) (z : ↑(N.X s)),
      (ModuleCat.Hom.hom (f'.f n)) (((μK.μ h) x) z) =
        ((μL.μ h) ((ModuleCat.Hom.hom (f.f r)) x)) ((ModuleCat.Hom.hom (ρ.f s)) z))
  {p s m : ℕ} (h : p + 1 + s = m + 1)
  (X : ↑(HomologicalComplex.cycles (Langlands.GaloisCohomology.mappingCoconeNat f) (p + 1)))
  (e : ↑(HomologicalComplex.cycles N s)) (q : ↑(K'.X m)) (w : ↑(HomologicalComplex.cycles L' m))
  (hq :
    (ModuleCat.Hom.hom (K'.d m (m + 1))) q =
      ((μK.μ h)
          ((ModuleCat.Hom.hom (HomologicalComplex.iCycles (Langlands.GaloisCohomology.mappingCoconeNat f) (p + 1)))
              X).1)
        ((ModuleCat.Hom.hom (HomologicalComplex.iCycles N s)) e))
  (hw :
    (ModuleCat.Hom.hom (HomologicalComplex.iCycles L' m)) w =
      ((μL.μ ⋯)
            (have this :=
              ((ModuleCat.Hom.hom (HomologicalComplex.iCycles (Langlands.GaloisCohomology.mappingCoconeNat f) (p + 1)))
                  X).2;
            this))
          ((ModuleCat.Hom.hom (ρ.f s)) ((ModuleCat.Hom.hom (HomologicalComplex.iCycles N s)) e)) -
        (ModuleCat.Hom.hom (f'.f m)) q) :
  (((μL.coconeLeft ρ μK ⋯).homology h)
        ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ (Langlands.GaloisCohomology.mappingCoconeNat f) (p + 1))) X))
      ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ N s)) e) =
    (ModuleCat.Hom.hom (Langlands.GaloisCohomology.mappingCoconeNat.homologyδ f' m))
      ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ L' m)) w)
Langlands.GaloisCohomology.PoitouTate.Internal.exists_coconeLeft_homology_eq_homologyδ.{u} {k : Type u} [CommRing k]
  {K L K' L' N N' : CochainComplex (ModuleCat k) ℕ} {f : K ⟶ L} {f' : K' ⟶ L'}
  (μL : Langlands.GaloisCohomology.LeibnizPairing L N' L') (ρ : N ⟶ N')
  (μK : Langlands.GaloisCohomology.LeibnizPairing K N K')
  (hc :
    ∀ {r s n : ℕ} (h : r + s = n) (x : ↑(K.X r)) (z : ↑(N.X s)),
      (ModuleCat.Hom.hom (f'.f n)) (((μK.μ h) x) z) =
        ((μL.μ h) ((ModuleCat.Hom.hom (f.f r)) x)) ((ModuleCat.Hom.hom (ρ.f s)) z))
  {p s m : ℕ} (h : p + 1 + s = m + 1)
  (X : ↑(HomologicalComplex.cycles (Langlands.GaloisCohomology.mappingCoconeNat f) (p + 1)))
  (e : ↑(HomologicalComplex.cycles N s)) (q : ↑(K'.X m))
  (hq :
    (ModuleCat.Hom.hom (K'.d m (m + 1))) q =
      ((μK.μ h)
          ((ModuleCat.Hom.hom (HomologicalComplex.iCycles (Langlands.GaloisCohomology.mappingCoconeNat f) (p + 1)))
              X).1)
        ((ModuleCat.Hom.hom (HomologicalComplex.iCycles N s)) e)) :
  ∃ w,
    (ModuleCat.Hom.hom (HomologicalComplex.iCycles L' m)) w =
        ((μL.μ ⋯)
              (have this :=
                ((ModuleCat.Hom.hom
                      (HomologicalComplex.iCycles (Langlands.GaloisCohomology.mappingCoconeNat f) (p + 1)))
                    X).2;
              this))
            ((ModuleCat.Hom.hom (ρ.f s)) ((ModuleCat.Hom.hom (HomologicalComplex.iCycles N s)) e)) -
          (ModuleCat.Hom.hom (f'.f m)) q ∧
      (((μL.coconeLeft ρ μK ⋯).homology h)
            ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ (Langlands.GaloisCohomology.mappingCoconeNat f) (p + 1)))
              X))
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ N s)) e) =
        (ModuleCat.Hom.hom (Langlands.GaloisCohomology.mappingCoconeNat.homologyδ f' m))
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ L' m)) w)
Langlands.GaloisCohomology.PoitouTate.Internal.homologyδ_homologyπ_eq_localToCompact.{u} {k G : Type u} [CommRing k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {ι : Type u} {H : ι → Type u} [(v : ι) → Group (H v)]
  [(v : ι) → TopologicalSpace (H v)] [∀ (v : ι), IsTopologicalGroup (H v)] (φ : (v : ι) → H v →ₜ* G)
  {C : Rep.{u, u, u} k G} [Langlands.IsSmoothRep C] {Cᵥ : (v : ι) → Rep.{u, u, u} k (H v)}
  [∀ (v : ι), Langlands.IsSmoothRep (Cᵥ v)] {c : (v : ι) → Rep.res (↑(φ v)) C ⟶ Cᵥ v} {m : ℕ}
  (w :
    ↑(HomologicalComplex.cycles
        (Langlands.GaloisCohomology.piComplex fun v => Langlands.ProfiniteCohomology.cochains (Cᵥ v)) m)) :
  (ModuleCat.Hom.hom
        (Langlands.GaloisCohomology.mappingCoconeNat.homologyδ (Langlands.GaloisCohomology.localRes φ C Cᵥ c) m))
      ((ModuleCat.Hom.hom
          (HomologicalComplex.homologyπ
            (Langlands.GaloisCohomology.piComplex fun v => Langlands.ProfiniteCohomology.cochains (Cᵥ v)) m))
        w) =
    (ModuleCat.Hom.hom (Langlands.GaloisCohomology.localToCompact φ C Cᵥ c m)) fun v =>
      (ModuleCat.Hom.hom (HomologicalComplex.homologyπ (Langlands.ProfiniteCohomology.cochains (Cᵥ v)) m))
        ((ModuleCat.Hom.hom
            (HomologicalComplex.cyclesMap
              (Langlands.GaloisCohomology.piProj (fun v => Langlands.ProfiniteCohomology.cochains (Cᵥ v)) v) m))
          w)
Langlands.GaloisCohomology.PoitouTate.Internal.compactSupportMap_compactCup.{u} {k G : Type u} [CommRing k] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] {ι : Type u} {H : ι → Type u} [(v : ι) → Group (H v)]
  [(v : ι) → TopologicalSpace (H v)] [∀ (v : ι), IsTopologicalGroup (H v)] (φ : (v : ι) → H v →ₜ* G)
  {A B C C' : Rep.{u, u, u} k G} [Langlands.IsSmoothRep A] [Langlands.IsSmoothRep B] [Langlands.IsSmoothRep C]
  [Langlands.IsSmoothRep C'] {Aᵥ Cᵥ C'ᵥ : (v : ι) → Rep.{u, u, u} k (H v)} [∀ (v : ι), Langlands.IsSmoothRep (Aᵥ v)]
  [∀ (v : ι), Langlands.IsSmoothRep (Cᵥ v)] [∀ (v : ι), Langlands.IsSmoothRep (C'ᵥ v)]
  {a : (v : ι) → Rep.res (↑(φ v)) A ⟶ Aᵥ v} {c : (v : ι) → Rep.res (↑(φ v)) C ⟶ Cᵥ v}
  {c' : (v : ι) → Rep.res (↑(φ v)) C' ⟶ C'ᵥ v} (μ : CategoryTheory.MonoidalCategoryStruct.tensorObj A B ⟶ C)
  (μᵥ : (v : ι) → CategoryTheory.MonoidalCategoryStruct.tensorObj (Aᵥ v) (Rep.res (↑(φ v)) B) ⟶ Cᵥ v)
  (hμ :
    ∀ (v : ι),
      CategoryTheory.CategoryStruct.comp ((Rep.resFunctor ↑(φ v)).map μ) (c v) =
        CategoryTheory.CategoryStruct.comp
          (Langlands.ProfiniteCohomology.resTensorHom (↑(φ v)) (a v)
            (CategoryTheory.CategoryStruct.id (Rep.res (↑(φ v)) B)))
          (μᵥ v))
  (g : C ⟶ C') (gᵥ : (v : ι) → Cᵥ v ⟶ C'ᵥ v)
  (hg :
    ∀ (v : ι),
      CategoryTheory.CategoryStruct.comp (c v) (gᵥ v) =
        CategoryTheory.CategoryStruct.comp ((Rep.resFunctor ↑(φ v)).map g) (c' v))
  (hμ' :
    ∀ (v : ι),
      CategoryTheory.CategoryStruct.comp ((Rep.resFunctor ↑(φ v)).map (CategoryTheory.CategoryStruct.comp μ g)) (c' v) =
        CategoryTheory.CategoryStruct.comp
          (Langlands.ProfiniteCohomology.resTensorHom (↑(φ v)) (a v)
            (CategoryTheory.CategoryStruct.id (Rep.res (↑(φ v)) B)))
          (CategoryTheory.CategoryStruct.comp (μᵥ v) (gᵥ v)))
  {r s n : ℕ} (h : r + s = n) (x : ↑(Langlands.GaloisCohomology.compactSupportCohomology φ A Aᵥ a r))
  (y : ↑(Langlands.ProfiniteCohomology.cohomology B s)) :
  (ModuleCat.Hom.hom (Langlands.GaloisCohomology.compactSupportMap φ g gᵥ hg n))
      (((Langlands.GaloisCohomology.compactCup φ μ μᵥ hμ h) x) y) =
    ((Langlands.GaloisCohomology.compactCup φ (CategoryTheory.CategoryStruct.comp μ g)
          (fun v => CategoryTheory.CategoryStruct.comp (μᵥ v) (gᵥ v)) hμ' h)
        x)
      y
Langlands.GaloisCohomology.PoitouTate.Internal.compactCup_congr.{u} {k G : Type u} [CommRing k] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] {ι : Type u} {H : ι → Type u} [(v : ι) → Group (H v)]
  [(v : ι) → TopologicalSpace (H v)] [∀ (v : ι), IsTopologicalGroup (H v)] (φ : (v : ι) → H v →ₜ* G)
  {A B C : Rep.{u, u, u} k G} [Langlands.IsSmoothRep A] [Langlands.IsSmoothRep B] [Langlands.IsSmoothRep C]
  {Aᵥ Cᵥ : (v : ι) → Rep.{u, u, u} k (H v)} [∀ (v : ι), Langlands.IsSmoothRep (Aᵥ v)]
  [∀ (v : ι), Langlands.IsSmoothRep (Cᵥ v)] {a : (v : ι) → Rep.res (↑(φ v)) A ⟶ Aᵥ v}
  {c : (v : ι) → Rep.res (↑(φ v)) C ⟶ Cᵥ v} (μ : CategoryTheory.MonoidalCategoryStruct.tensorObj A B ⟶ C)
  (μᵥ μᵥ' : (v : ι) → CategoryTheory.MonoidalCategoryStruct.tensorObj (Aᵥ v) (Rep.res (↑(φ v)) B) ⟶ Cᵥ v) (e : μᵥ = μᵥ')
  (hμ :
    ∀ (v : ι),
      CategoryTheory.CategoryStruct.comp ((Rep.resFunctor ↑(φ v)).map μ) (c v) =
        CategoryTheory.CategoryStruct.comp
          (Langlands.ProfiniteCohomology.resTensorHom (↑(φ v)) (a v)
            (CategoryTheory.CategoryStruct.id (Rep.res (↑(φ v)) B)))
          (μᵥ v))
  (hμ' :
    ∀ (v : ι),
      CategoryTheory.CategoryStruct.comp ((Rep.resFunctor ↑(φ v)).map μ) (c v) =
        CategoryTheory.CategoryStruct.comp
          (Langlands.ProfiniteCohomology.resTensorHom (↑(φ v)) (a v)
            (CategoryTheory.CategoryStruct.id (Rep.res (↑(φ v)) B)))
          (μᵥ' v))
  {r s n : ℕ} (h : r + s = n) (x : ↑(Langlands.GaloisCohomology.compactSupportCohomology φ A Aᵥ a r))
  (y : ↑(Langlands.ProfiniteCohomology.cohomology B s)) :
  ((Langlands.GaloisCohomology.compactCup φ μ μᵥ hμ h) x) y =
    ((Langlands.GaloisCohomology.compactCup φ μ μᵥ' hμ' h) x) y
Langlands.GaloisCohomology.PoitouTate.Internal.lsmul_uliftUp.{u} {A : Type u} [AddCommGroup A]
  [Module (ULift.{u, 0} ℤ) A] (m : ℤ) (x : A) : ((LinearMap.lsmul (ULift.{u, 0} ℤ) A) { down := m }) x = m • x
Langlands.GaloisCohomology.PoitouTate.Internal.intMulPairingRes.{u} {K : Type u} [Group K] {G : Type u} [Group G]
  (A : Rep.{u, u, u} (ULift.{u, 0} ℤ) K) (ψ : K →* G) :
  CategoryTheory.MonoidalCategoryStruct.tensorObj (Rep.res ψ (Langlands.ProfiniteCohomology.intRepTriv G)) A ⟶ A
Langlands.GaloisCohomology.PoitouTate.Internal.intActPairing.{u} {K : Type u} [Group K]
  (A : Rep.{u, u, u} (ULift.{u, 0} ℤ) K) :
  CategoryTheory.MonoidalCategoryStruct.tensorObj A (Langlands.ProfiniteCohomology.intRepTriv K) ⟶ A
Langlands.GaloisCohomology.PoitouTate.Internal.intActPairing_tmul.{u} {K : Type u} [Group K]
  (A : Rep.{u, u, u} (ULift.{u, 0} ℤ) K) (a : ↑A) (m : ℤ) :
  (Rep.Hom.hom (Langlands.GaloisCohomology.PoitouTate.Internal.intActPairing A)) (a ⊗ₜ[ULift.{u, 0} ℤ] { down := m }) =
    m • a
Langlands.GaloisCohomology.PoitouTate.Internal.intActPairingRes.{u} {K : Type u} [Group K] {G : Type u} [Group G]
  (A : Rep.{u, u, u} (ULift.{u, 0} ℤ) K) (ψ : K →* G) :
  CategoryTheory.MonoidalCategoryStruct.tensorObj A (Rep.res ψ (Langlands.ProfiniteCohomology.intRepTriv G)) ⟶ A
Langlands.GaloisCohomology.PoitouTate.Internal.intActPairingRes_tmul.{u} {K : Type u} [Group K] {G : Type u} [Group G]
  (A : Rep.{u, u, u} (ULift.{u, 0} ℤ) K) (ψ : K →* G) (a : ↑A) (m : ℤ) :
  (Rep.Hom.hom (Langlands.GaloisCohomology.PoitouTate.Internal.intActPairingRes A ψ))
      (a ⊗ₜ[ULift.{u, 0} ℤ] { down := m }) =
    m • a
Langlands.GaloisCohomology.PoitouTate.Internal.resTensorHom_id_id.{u} {G L : Type u} [Group G] [Group L] (ψ : L →* G)
  {A B : Rep.{u, u, u} (ULift.{u, 0} ℤ) G} :
  Langlands.ProfiniteCohomology.resTensorHom ψ (CategoryTheory.CategoryStruct.id (Rep.res ψ A))
      (CategoryTheory.CategoryStruct.id (Rep.res ψ B)) =
    CategoryTheory.CategoryStruct.id (Rep.res ψ (CategoryTheory.MonoidalCategoryStruct.tensorObj A B))
Langlands.GaloisCohomology.PoitouTate.Internal.tensor_intActPairing_eq.{u} {G : Type u} [Group G] (n : ℕ)
  {D E : Rep.{u, u, u} (ULift.{u, 0} ℤ) G} (hD : ∀ (d : ↑D), n • d = 0) (f : D ⟶ E) :
  CategoryTheory.CategoryStruct.comp
      (CategoryTheory.MonoidalCategoryStruct.tensorHom f
        (CategoryTheory.CategoryStruct.id (Langlands.ProfiniteCohomology.intRepTriv G)))
      (Langlands.GaloisCohomology.PoitouTate.Internal.intActPairing E) =
    CategoryTheory.CategoryStruct.comp
      (CategoryTheory.MonoidalCategoryStruct.tensorHom (CategoryTheory.CategoryStruct.id D)
        (Langlands.ProfiniteCohomology.zmodReduction G n))
      (CategoryTheory.CategoryStruct.comp (Langlands.GaloisCohomology.zmodMulPairingRight n D hD) f)
Langlands.GaloisCohomology.PoitouTate.Internal.tensor_intActPairingRes_eq.{u} {G L : Type u} [Group G] [Group L] (n : ℕ)
  {D : Rep.{u, u, u} (ULift.{u, 0} ℤ) G} (hD : ∀ (d : ↑D), n • d = 0) (ψ : L →* G)
  {Eᵥ : Rep.{u, u, u} (ULift.{u, 0} ℤ) L} (f : Rep.res ψ D ⟶ Eᵥ) :
  CategoryTheory.CategoryStruct.comp
      (CategoryTheory.MonoidalCategoryStruct.tensorHom f
        (CategoryTheory.CategoryStruct.id (Rep.res ψ (Langlands.ProfiniteCohomology.intRepTriv G))))
      (Langlands.GaloisCohomology.PoitouTate.Internal.intActPairingRes Eᵥ ψ) =
    CategoryTheory.CategoryStruct.comp
      (CategoryTheory.MonoidalCategoryStruct.tensorHom (CategoryTheory.CategoryStruct.id (Rep.res ψ D))
        ((Rep.resFunctor ψ).map (Langlands.ProfiniteCohomology.zmodReduction G n)))
      (CategoryTheory.CategoryStruct.comp
        ((Rep.resFunctor ψ).map (Langlands.GaloisCohomology.zmodMulPairingRight n D hD)) f)
Langlands.GaloisCohomology.PoitouTate.Internal.tensor_nsmul_intActPairing_eq.{u} {G : Type u} [Group G] (n : ℕ)
  (A : Rep.{u, u, u} (ULift.{u, 0} ℤ) G) :
  CategoryTheory.CategoryStruct.comp
      (CategoryTheory.MonoidalCategoryStruct.tensorHom (CategoryTheory.CategoryStruct.id A)
        (n • CategoryTheory.CategoryStruct.id (Langlands.ProfiniteCohomology.intRepTriv G)))
      (Langlands.GaloisCohomology.PoitouTate.Internal.intActPairing A) =
    CategoryTheory.CategoryStruct.comp
      (CategoryTheory.MonoidalCategoryStruct.tensorHom (n • CategoryTheory.CategoryStruct.id A)
        (CategoryTheory.CategoryStruct.id (Langlands.ProfiniteCohomology.intRepTriv G)))
      (Langlands.GaloisCohomology.PoitouTate.Internal.intActPairing A)
Langlands.GaloisCohomology.PoitouTate.Internal.tensor_nsmul_intActPairingRes_eq.{u} {G L : Type u} [Group G] [Group L]
  (n : ℕ) (ψ : L →* G) (A : Rep.{u, u, u} (ULift.{u, 0} ℤ) L) :
  CategoryTheory.CategoryStruct.comp
      (CategoryTheory.MonoidalCategoryStruct.tensorHom (CategoryTheory.CategoryStruct.id A)
        ((Rep.resFunctor ψ).map (n • CategoryTheory.CategoryStruct.id (Langlands.ProfiniteCohomology.intRepTriv G))))
      (Langlands.GaloisCohomology.PoitouTate.Internal.intActPairingRes A ψ) =
    CategoryTheory.CategoryStruct.comp
      (CategoryTheory.MonoidalCategoryStruct.tensorHom (n • CategoryTheory.CategoryStruct.id A)
        (CategoryTheory.CategoryStruct.id (Rep.res ψ (Langlands.ProfiniteCohomology.intRepTriv G))))
      (Langlands.GaloisCohomology.PoitouTate.Internal.intActPairingRes A ψ)
Langlands.GaloisCohomology.PoitouTate.Internal.res_comp_compat.{u} {G L : Type u} [Group G] [Group L]
  {D E : Rep.{u, u, u} (ULift.{u, 0} ℤ) G} {Cᵥ : Rep.{u, u, u} (ULift.{u, 0} ℤ) L}
  {X C' : Rep.{u, u, u} (ULift.{u, 0} ℤ) G} (ψ : L →* G) (μ : CategoryTheory.MonoidalCategoryStruct.tensorObj D E ⟶ X)
  (g : X ⟶ C') (c : Rep.res ψ C' ⟶ Cᵥ) (gᵥ : Rep.res ψ X ⟶ Cᵥ)
  (hg :
    CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.id (Rep.res ψ X)) gᵥ =
      CategoryTheory.CategoryStruct.comp ((Rep.resFunctor ψ).map g) c) :
  CategoryTheory.CategoryStruct.comp ((Rep.resFunctor ψ).map (CategoryTheory.CategoryStruct.comp μ g)) c =
    CategoryTheory.CategoryStruct.comp
      (Langlands.ProfiniteCohomology.resTensorHom ψ (CategoryTheory.CategoryStruct.id (Rep.res ψ D))
        (CategoryTheory.CategoryStruct.id (Rep.res ψ E)))
      (CategoryTheory.CategoryStruct.comp ((Rep.resFunctor ψ).map μ) gᵥ)
Langlands.GaloisCohomology.PoitouTate.Internal.eq_of_add_neg_one_pow_one_smul_eq_zero.{u_1, u_2} {R : Type u_1}
  {M : Type u_2} [Ring R] [AddCommGroup M] [Module R M] {a b : M} (h : a + (-1) ^ 1 • b = 0) : a = b
Langlands.GaloisCohomology.PoitouTate.Internal.intActPairing_res_compat.{u} {G L : Type u} [Group G] [Group L]
  (ψ : L →* G) (A : Rep.{u, u, u} (ULift.{u, 0} ℤ) G) {Aᵥ : Rep.{u, u, u} (ULift.{u, 0} ℤ) L} (f : Rep.res ψ A ⟶ Aᵥ) :
  CategoryTheory.CategoryStruct.comp
      ((Rep.resFunctor ψ).map (Langlands.GaloisCohomology.PoitouTate.Internal.intActPairing A)) f =
    CategoryTheory.CategoryStruct.comp
      (Langlands.ProfiniteCohomology.resTensorHom ψ f
        (CategoryTheory.CategoryStruct.id (Rep.res ψ (Langlands.ProfiniteCohomology.intRepTriv G))))
      (Langlands.GaloisCohomology.PoitouTate.Internal.intActPairingRes Aᵥ ψ)
Langlands.GaloisCohomology.PoitouTate.Internal.localFamilyHom.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (v : ↑S) :
  Gal(AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion K
          ↑v)/IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v) →*
    Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S
Langlands.GaloisCohomology.PoitouTate.Internal.unitsCup.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (s : ℕ) :
  ↑(Langlands.GaloisCohomology.compactSupportCohomology (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
        (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S)
        (fun v =>
          Langlands.GaloisCohomology.unitsModule (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)
            (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)))
        (fun v => Langlands.GaloisCohomology.PoitouTate.Internal.sUnitsLocalHom ι S ↑v) 1) →ₗ[ULift.{u, 0} ℤ]
    ↑(Langlands.ProfiniteCohomology.cohomology
          (Langlands.ProfiniteCohomology.intRepTriv (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
          s) →ₗ[ULift.{u, 0} ℤ]
      ↑(Langlands.GaloisCohomology.compactSupportCohomology (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
          (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S)
          (fun v =>
            Langlands.GaloisCohomology.unitsModule (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)
              (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)))
          (fun v => Langlands.GaloisCohomology.PoitouTate.Internal.sUnitsLocalHom ι S ↑v) (1 + s))
Langlands.GaloisCohomology.PoitouTate.Internal.compactSupportMap_compactCupRes_kummerCompactδ.{u} {K Ω : Type u}
  [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (n : ℕ) [NeZero n]
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S)
  (x : ↑(Langlands.GaloisCohomology.PoitouTate.Internal.unitsCompact ι S 1))
  (y :
    ↑(Langlands.ProfiniteCohomology.cohomology
        (Langlands.ProfiniteCohomology.zmodRep (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) n) 1)) :
  (ModuleCat.Hom.hom
        (Langlands.GaloisCohomology.compactSupportMap (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
          (Langlands.GaloisCohomology.sUnitsKummerSequence S (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) n).f
          (fun v => (Langlands.GaloisCohomology.PoitouTate.localKummerSequence ι S n ↑v).f) ⋯ 3))
      (((Langlands.GaloisCohomology.compactCupRes (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
            (Langlands.GaloisCohomology.zmodMulPairingRight n
              (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S n) ⋯)
            ⋯)
          ((ModuleCat.Hom.hom (Langlands.GaloisCohomology.PoitouTate.Internal.kummerCompactδ ι n hS)) x))
        y) =
    ((Langlands.GaloisCohomology.PoitouTate.Internal.unitsCup ι S 2) x)
      ((ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.δ ⋯ 1 2 ⋯)) y)
Langlands.GaloisCohomology.PoitouTate.Internal.exists_cocycle_δ_bockSeq.{u} {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {n : ℕ} (hn : n ≠ 0)
  (z : ↑(Langlands.ProfiniteCohomology.cocycles (Langlands.ProfiniteCohomology.zmodRep G n) 1)) :
  ∃ x₁,
    (CategoryTheory.ConcreteCategory.hom
            (Langlands.ProfiniteCohomology.cohomologyπ (Langlands.ProfiniteCohomology.intRepTriv G) 2))
          x₁ =
        (ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.δ ⋯ 1 2 ⋯))
          ((CategoryTheory.ConcreteCategory.hom
              (Langlands.ProfiniteCohomology.cohomologyπ (Langlands.ProfiniteCohomology.bockSeq G n).X₃ 1))
            z) ∧
      ∀ (g h : G),
        (Langlands.ProfiniteCohomology.cochainOf (Langlands.ProfiniteCohomology.intRepTriv G)
              ((Langlands.ProfiniteCohomology.cocycleι (Langlands.ProfiniteCohomology.intRepTriv G) 2) x₁)
              ![g, h]).down =
          Langlands.ProfiniteCohomology.bockInt (Langlands.ProfiniteCohomology.zmodCocycleHom z) g h
Langlands.GaloisCohomology.PoitouTate.Internal.cupCochain_const_left.{u} {k G : Type u} [CommRing k] [Group G]
  {A B : Rep.{u, u, u} k G} {q n : ℕ} (h : 0 + q = n) (m : ↑A) (g : (Fin q → G) → ↑B) (x : Fin n → G) :
  Langlands.ProfiniteCohomology.cupCochain h (fun x => m) g x = m ⊗ₜ[k] g fun j => x ⟨↑j, ⋯⟩
Langlands.GaloisCohomology.PoitouTate.Internal.constCupSub.{u} {k G : Type u} [CommRing k] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] {U X B : Rep.{u, u, u} k G} [Langlands.IsSmoothRep U]
  [Langlands.IsSmoothRep X] [Langlands.IsSmoothRep B] (j : U ⟶ X)
  (μX : CategoryTheory.MonoidalCategoryStruct.tensorObj X B ⟶ X) (m : ↑X) {s : ℕ}
  (e : ↑((Langlands.ProfiniteCohomology.cochains B).X s)) (z : ↑((Langlands.ProfiniteCohomology.cochains U).X s)) :
  ↑((Langlands.ProfiniteCohomology.cochains X).X s)
Langlands.GaloisCohomology.PoitouTate.Internal.cochainOf_constCupSub.{u} {k G : Type u} [CommRing k] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] {U X B : Rep.{u, u, u} k G} [Langlands.IsSmoothRep U]
  [Langlands.IsSmoothRep X] [Langlands.IsSmoothRep B] (j : U ⟶ X)
  (μX : CategoryTheory.MonoidalCategoryStruct.tensorObj X B ⟶ X) (m : ↑X) {s : ℕ}
  (e : ↑((Langlands.ProfiniteCohomology.cochains B).X s)) (z : ↑((Langlands.ProfiniteCohomology.cochains U).X s))
  (σ : Fin s → G) :
  Langlands.ProfiniteCohomology.cochainOf X (Langlands.GaloisCohomology.PoitouTate.Internal.constCupSub j μX m e z) σ =
    (Rep.Hom.hom μX) (m ⊗ₜ[k] Langlands.ProfiniteCohomology.cochainOf B e σ) -
      (Rep.Hom.hom j) (Langlands.ProfiniteCohomology.cochainOf U z σ)
Langlands.GaloisCohomology.PoitouTate.Internal.d_constCupSub.{u} {k G : Type u} [CommRing k] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] {U X B : Rep.{u, u, u} k G} [Langlands.IsSmoothRep U]
  [Langlands.IsSmoothRep X] [Langlands.IsSmoothRep B] (j : U ⟶ X)
  (μU : CategoryTheory.MonoidalCategoryStruct.tensorObj U B ⟶ U)
  (μX : CategoryTheory.MonoidalCategoryStruct.tensorObj X B ⟶ X)
  (hj :
    CategoryTheory.CategoryStruct.comp μU j =
      CategoryTheory.CategoryStruct.comp
        (CategoryTheory.MonoidalCategoryStruct.tensorHom j (CategoryTheory.CategoryStruct.id B)) μX)
  (m : ↑X) (x : ↑((Langlands.ProfiniteCohomology.cochains U).X 1))
  (hx :
    (CategoryTheory.ConcreteCategory.hom ((Langlands.ProfiniteCohomology.coeffCochainsMap j).f 1)) x =
      (ModuleCat.Hom.hom ((Langlands.ProfiniteCohomology.cochains X).d 0 1))
        ((Langlands.GaloisCohomology.zeroCochain X) m))
  {s : ℕ} (e : ↑((Langlands.ProfiniteCohomology.cochains B).X s))
  (he : (ModuleCat.Hom.hom ((Langlands.ProfiniteCohomology.cochains B).d s (s + 1))) e = 0)
  (z : ↑((Langlands.ProfiniteCohomology.cochains U).X s))
  (hz :
    (ModuleCat.Hom.hom ((Langlands.ProfiniteCohomology.cochains U).d s (s + 1))) z =
      ((Langlands.GaloisCohomology.cupPairingCochains μU ⋯) x) e) :
  (ModuleCat.Hom.hom ((Langlands.ProfiniteCohomology.cochains X).d s (s + 1)))
      (Langlands.GaloisCohomology.PoitouTate.Internal.constCupSub j μX m e z) =
    0
Langlands.GaloisCohomology.PoitouTate.Internal.exists_compactCup_const.{u} {k G : Type u} [CommRing k] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] {ι : Type u} {H : ι → Type u} [(v : ι) → Group (H v)]
  [(v : ι) → TopologicalSpace (H v)] [∀ (v : ι), IsTopologicalGroup (H v)] (φ : (v : ι) → H v →ₜ* G)
  {U X B : Rep.{u, u, u} k G} [Langlands.IsSmoothRep U] [Langlands.IsSmoothRep X] [Langlands.IsSmoothRep B] (j : U ⟶ X)
  (μU : CategoryTheory.MonoidalCategoryStruct.tensorObj U B ⟶ U)
  (μX : CategoryTheory.MonoidalCategoryStruct.tensorObj X B ⟶ X)
  (hj :
    CategoryTheory.CategoryStruct.comp μU j =
      CategoryTheory.CategoryStruct.comp
        (CategoryTheory.MonoidalCategoryStruct.tensorHom j (CategoryTheory.CategoryStruct.id B)) μX)
  (Ωᵥ : (v : ι) → Rep.{u, u, u} k (H v)) [∀ (v : ι), Langlands.IsSmoothRep (Ωᵥ v)]
  (a : (v : ι) → Rep.res (↑(φ v)) U ⟶ Ωᵥ v) (l : (v : ι) → Rep.res (↑(φ v)) X ⟶ Ωᵥ v)
  (hal : ∀ (v : ι) (x : ↑U), (Rep.Hom.hom (a v)) x = (Rep.Hom.hom (l v)) ((Rep.Hom.hom j) x))
  (μΩ : (v : ι) → CategoryTheory.MonoidalCategoryStruct.tensorObj (Ωᵥ v) (Rep.res (↑(φ v)) B) ⟶ Ωᵥ v)
  (hl :
    ∀ (v : ι),
      CategoryTheory.CategoryStruct.comp ((Rep.resFunctor ↑(φ v)).map μX) (l v) =
        CategoryTheory.CategoryStruct.comp
          (Langlands.ProfiniteCohomology.resTensorHom (↑(φ v)) (l v)
            (CategoryTheory.CategoryStruct.id (Rep.res (↑(φ v)) B)))
          (μΩ v))
  (hμ :
    ∀ (v : ι),
      CategoryTheory.CategoryStruct.comp ((Rep.resFunctor ↑(φ v)).map μU) (a v) =
        CategoryTheory.CategoryStruct.comp
          (Langlands.ProfiniteCohomology.resTensorHom (↑(φ v)) (a v)
            (CategoryTheory.CategoryStruct.id (Rep.res (↑(φ v)) B)))
          (μΩ v))
  (Xc : ↑(HomologicalComplex.cycles (Langlands.GaloisCohomology.compactSupportCochains φ U Ωᵥ a) 1)) (m : ↑X)
  (x : ↑((Langlands.ProfiniteCohomology.cochains U).X 1))
  (hX1 :
    ((ModuleCat.Hom.hom (HomologicalComplex.iCycles (Langlands.GaloisCohomology.compactSupportCochains φ U Ωᵥ a) 1))
          Xc).1 =
      x)
  (y : (v : ι) → ↑(Ωᵥ v))
  (hX2 :
    ((ModuleCat.Hom.hom (HomologicalComplex.iCycles (Langlands.GaloisCohomology.compactSupportCochains φ U Ωᵥ a) 1))
          Xc).2 =
      Langlands.GaloisCohomology.PoitouTate.Internal.piConst Ωᵥ y)
  (hy : ∀ (v : ι), y v = (Rep.Hom.hom (l v)) m)
  (hx :
    (CategoryTheory.ConcreteCategory.hom ((Langlands.ProfiniteCohomology.coeffCochainsMap j).f 1)) x =
      (ModuleCat.Hom.hom ((Langlands.ProfiniteCohomology.cochains X).d 0 1))
        ((Langlands.GaloisCohomology.zeroCochain X) m))
  {s : ℕ} (e : ↑(HomologicalComplex.cycles (Langlands.ProfiniteCohomology.cochains B) s))
  (z : ↑((Langlands.ProfiniteCohomology.cochains U).X s))
  (hz :
    (ModuleCat.Hom.hom ((Langlands.ProfiniteCohomology.cochains U).d s (s + 1))) z =
      ((Langlands.GaloisCohomology.cupPairingCochains μU ⋯) x)
        ((ModuleCat.Hom.hom (HomologicalComplex.iCycles (Langlands.ProfiniteCohomology.cochains B) s)) e)) :
  ∃ W,
    Langlands.ProfiniteCohomology.cochainOf X ((Langlands.ProfiniteCohomology.cocycleι X s) W) =
        Langlands.ProfiniteCohomology.cochainOf X
          (Langlands.GaloisCohomology.PoitouTate.Internal.constCupSub j μX m
            ((ModuleCat.Hom.hom (HomologicalComplex.iCycles (Langlands.ProfiniteCohomology.cochains B) s)) e) z) ∧
      ((Langlands.GaloisCohomology.compactCup φ μU μΩ hμ ⋯)
            ((ModuleCat.Hom.hom
                (HomologicalComplex.homologyπ (Langlands.GaloisCohomology.compactSupportCochains φ U Ωᵥ a) 1))
              Xc))
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ (Langlands.ProfiniteCohomology.cochains B) s)) e) =
        (ModuleCat.Hom.hom (Langlands.GaloisCohomology.localToCompact φ U Ωᵥ a s)) fun v =>
          (ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.map (φ v) (l v) s))
            ((CategoryTheory.ConcreteCategory.hom (Langlands.ProfiniteCohomology.cohomologyπ X s)) W)
Langlands.GaloisCohomology.PoitouTate.Internal.exists_d_eq_cupPairingCochains.{u} {k G : Type u} [CommRing k] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] {A B C : Rep.{u, u, u} k G} [Langlands.IsSmoothRep A]
  [Langlands.IsSmoothRep B] [Langlands.IsSmoothRep C] (μ : CategoryTheory.MonoidalCategoryStruct.tensorObj A B ⟶ C)
  {p q m : ℕ} (h : p + q = m + 1) (x : ↑(Langlands.ProfiniteCohomology.cocycles A p))
  (y : ↑(Langlands.ProfiniteCohomology.cocycles B q))
  (h0 :
    ((Langlands.ProfiniteCohomology.cupPairing μ h)
          ((CategoryTheory.ConcreteCategory.hom (Langlands.ProfiniteCohomology.cohomologyπ A p)) x))
        ((CategoryTheory.ConcreteCategory.hom (Langlands.ProfiniteCohomology.cohomologyπ B q)) y) =
      0) :
  ∃ z,
    (ModuleCat.Hom.hom ((Langlands.ProfiniteCohomology.cochains C).d m (m + 1))) z =
      ((Langlands.GaloisCohomology.cupPairingCochains μ h) ((Langlands.ProfiniteCohomology.cocycleι A p) x))
        ((Langlands.ProfiniteCohomology.cocycleι B q) y)
Langlands.GaloisCohomology.PoitouTate.Internal.intActPairing_sUnitsToUnits.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) :
  CategoryTheory.CategoryStruct.comp
      (Langlands.GaloisCohomology.PoitouTate.Internal.intActPairing
        (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S))
      (Langlands.GaloisCohomology.sUnitsToUnits S ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) =
    CategoryTheory.CategoryStruct.comp
      (CategoryTheory.MonoidalCategoryStruct.tensorHom
        (Langlands.GaloisCohomology.sUnitsToUnits S ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))
        (CategoryTheory.CategoryStruct.id
          (Langlands.ProfiniteCohomology.intRepTriv (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))))
      (Langlands.GaloisCohomology.PoitouTate.Internal.intActPairing
        (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)))
Langlands.GaloisCohomology.PoitouTate.Internal.toMul_mul_zpow_inv_mem.{u_1} {M : Type u_1} [CommGroup M]
  (N : Subgroup M) (t : M) (b : ℤ) (w : M) (X : Additive M) (hX : X = b • Additive.ofMul t - Additive.ofMul w)
  (hw : w ∈ N) : Additive.toMul X * (t ^ b)⁻¹ ∈ N
Langlands.GaloisCohomology.PoitouTate.Internal.exists_unitsData_cup_bock.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (n : ℕ) [NeZero n] (hn : IsPrimePow n)
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S)
  (t : ↥(Langlands.GaloisCohomology.sInvariantSubgroup Ω S))
  (z :
    ↑(Langlands.ProfiniteCohomology.cocycles
        (Langlands.ProfiniteCohomology.zmodRep (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) n) 1)) :
  ∃ W,
    (∀ (g h : Gal(↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)/K)),
        Additive.toMul
              (Langlands.ProfiniteCohomology.cochainOf
                (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))
                ((Langlands.ProfiniteCohomology.cocycleι
                    (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) 2)
                  W)
                ![g, h]) *
            (↑t ^ Langlands.ProfiniteCohomology.bockInt (Langlands.ProfiniteCohomology.zmodCocycleHom z) g h)⁻¹ ∈
          Langlands.GaloisCohomology.maximalSUnits K Ω S) ∧
      ((Langlands.GaloisCohomology.PoitouTate.Internal.unitsCup ι S 2)
            ((Langlands.GaloisCohomology.PoitouTate.Internal.unitsData S ι) (Additive.ofMul t, 0)))
          ((ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.δ ⋯ 1 2 ⋯))
            ((CategoryTheory.ConcreteCategory.hom
                (Langlands.ProfiniteCohomology.cohomologyπ
                  (Langlands.ProfiniteCohomology.bockSeq (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) n).X₃ 1))
              z)) =
        (ModuleCat.Hom.hom
            (Langlands.GaloisCohomology.localToCompact (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
              (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S)
              (fun v =>
                Langlands.GaloisCohomology.unitsModule (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)
                  (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)))
              (fun v => Langlands.GaloisCohomology.PoitouTate.Internal.sUnitsLocalHom ι S ↑v) 2))
          fun v =>
          (ModuleCat.Hom.hom
              (Langlands.ProfiniteCohomology.map (Langlands.GaloisCohomology.PoitouTate.localFamily ι S v)
                (Langlands.GaloisCohomology.PoitouTate.Internal.maximalUnitsLocalHom ι S ↑v) 2))
            ((CategoryTheory.ConcreteCategory.hom
                (Langlands.ProfiniteCohomology.cohomologyπ
                  (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) 2))
              W)
Langlands.GaloisCohomology.PoitouTate.Internal.localUnitsCup.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (v : ↑S)
  (a : Additive (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)ˣ)
  (b :
    ↑(Langlands.ProfiniteCohomology.cohomology
        (Langlands.ProfiniteCohomology.intRepTriv (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) 2)) :
  ↑(Langlands.ProfiniteCohomology.cohomology
      (Langlands.GaloisCohomology.unitsModule (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)))
      2)
Langlands.GaloisCohomology.PoitouTate.Internal.exists_unitsData_cup_bock'.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (n : ℕ) [NeZero n] (hn : IsPrimePow n)
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S)
  (d : Langlands.GaloisCohomology.PoitouTate.Internal.UnitsDatum Ω S)
  (z :
    ↑(Langlands.ProfiniteCohomology.cocycles
        (Langlands.ProfiniteCohomology.zmodRep (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) n) 1)) :
  ∃ W,
    (∀ (g h : Gal(↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)/K)),
        Additive.toMul
              (Langlands.ProfiniteCohomology.cochainOf
                (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))
                ((Langlands.ProfiniteCohomology.cocycleι
                    (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) 2)
                  W)
                ![g, h]) *
            (↑(Additive.toMul d.1) ^
                Langlands.ProfiniteCohomology.bockInt (Langlands.ProfiniteCohomology.zmodCocycleHom z) g h)⁻¹ ∈
          Langlands.GaloisCohomology.maximalSUnits K Ω S) ∧
      ((Langlands.GaloisCohomology.PoitouTate.Internal.unitsCup ι S 2)
            ((Langlands.GaloisCohomology.PoitouTate.Internal.unitsData S ι) d))
          ((ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.δ ⋯ 1 2 ⋯))
            ((CategoryTheory.ConcreteCategory.hom
                (Langlands.ProfiniteCohomology.cohomologyπ
                  (Langlands.ProfiniteCohomology.bockSeq (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) n).X₃ 1))
              z)) =
        (ModuleCat.Hom.hom
            (Langlands.GaloisCohomology.localToCompact (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
              (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S)
              (fun v =>
                Langlands.GaloisCohomology.unitsModule (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)
                  (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)))
              (fun v => Langlands.GaloisCohomology.PoitouTate.Internal.sUnitsLocalHom ι S ↑v) 2))
          fun v =>
          (ModuleCat.Hom.hom
                (Langlands.ProfiniteCohomology.map (Langlands.GaloisCohomology.PoitouTate.localFamily ι S v)
                  (Langlands.GaloisCohomology.PoitouTate.Internal.maximalUnitsLocalHom ι S ↑v) 2))
              ((CategoryTheory.ConcreteCategory.hom
                  (Langlands.ProfiniteCohomology.cohomologyπ
                    (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) 2))
                W) +
            Langlands.GaloisCohomology.PoitouTate.Internal.localUnitsCup ι S v (d.2 v)
              ((ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.δ ⋯ 1 2 ⋯))
                ((CategoryTheory.ConcreteCategory.hom
                    (Langlands.ProfiniteCohomology.cohomologyπ
                      (Langlands.ProfiniteCohomology.bockSeq (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) n).X₃
                      1))
                  z))
Langlands.GaloisCohomology.PoitouTate.Internal.exists_compactCupRes_kummerCompactδ_unitsData.{u} {K Ω : Type u}
  [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (n : ℕ) [NeZero n] (hn : IsPrimePow n)
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S)
  (d : Langlands.GaloisCohomology.PoitouTate.Internal.UnitsDatum Ω S)
  (z :
    ↑(Langlands.ProfiniteCohomology.cocycles
        (Langlands.ProfiniteCohomology.zmodRep (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) n) 1)) :
  ∃ W,
    (∀ (g h : Gal(↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)/K)),
        Additive.toMul
              (Langlands.ProfiniteCohomology.cochainOf
                (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))
                ((Langlands.ProfiniteCohomology.cocycleι
                    (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) 2)
                  W)
                ![g, h]) *
            (↑(Additive.toMul d.1) ^
                Langlands.ProfiniteCohomology.bockInt (Langlands.ProfiniteCohomology.zmodCocycleHom z) g h)⁻¹ ∈
          Langlands.GaloisCohomology.maximalSUnits K Ω S) ∧
      (ModuleCat.Hom.hom
            (Langlands.GaloisCohomology.compactSupportMap (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
              (Langlands.GaloisCohomology.sUnitsKummerSequence S (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))
                  n).f
              (fun v => (Langlands.GaloisCohomology.PoitouTate.localKummerSequence ι S n ↑v).f) ⋯ 3))
          (((Langlands.GaloisCohomology.compactCupRes (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
                (Langlands.GaloisCohomology.zmodMulPairingRight n
                  (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S n) ⋯)
                ⋯)
              ((ModuleCat.Hom.hom (Langlands.GaloisCohomology.PoitouTate.Internal.kummerCompactδ ι n hS))
                ((Langlands.GaloisCohomology.PoitouTate.Internal.unitsData S ι) d)))
            ((CategoryTheory.ConcreteCategory.hom
                (Langlands.ProfiniteCohomology.cohomologyπ
                  (Langlands.ProfiniteCohomology.zmodRep (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) n) 1))
              z)) =
        (ModuleCat.Hom.hom
            (Langlands.GaloisCohomology.localToCompact (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
              (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S)
              (fun v =>
                Langlands.GaloisCohomology.unitsModule (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)
                  (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)))
              (fun v => Langlands.GaloisCohomology.PoitouTate.Internal.sUnitsLocalHom ι S ↑v) 2))
          fun v =>
          (ModuleCat.Hom.hom
                (Langlands.ProfiniteCohomology.map (Langlands.GaloisCohomology.PoitouTate.localFamily ι S v)
                  (Langlands.GaloisCohomology.PoitouTate.Internal.maximalUnitsLocalHom ι S ↑v) 2))
              ((CategoryTheory.ConcreteCategory.hom
                  (Langlands.ProfiniteCohomology.cohomologyπ
                    (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) 2))
                W) +
            Langlands.GaloisCohomology.PoitouTate.Internal.localUnitsCup ι S v (d.2 v)
              ((ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.δ ⋯ 1 2 ⋯))
                ((CategoryTheory.ConcreteCategory.hom
                    (Langlands.ProfiniteCohomology.cohomologyπ
                      (Langlands.ProfiniteCohomology.bockSeq (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) n).X₃
                      1))
                  z))
```

## Outline of the proofs

For `exists_unitsData_cup_bock`: the cocycle of `e ∪ δχ` is `(σ(t)/t ∪ c_χ, (ι_v(t) a_v) ∪ c_χ)`.
Its global part `g` is a `2`-cocycle in `𝒪_Sˣ`; the cochain `t ∪ c_χ` with values in `K_Sˣ`
(`cupCochain_const_left`, `constCupSub`) has coboundary `g` up to sign, so the class of `g` in
`H³(G_S, 𝒪_Sˣ)` is killed by `n` and vanishes, `H³(G_S, 𝒪_Sˣ)` having no `ℓ`-torsion
(`eq_zero_of_cohomology_three_maximalSUnits`); so `g = df` with `f` a `2`-cochain in `𝒪_Sˣ`
(`exists_d_eq_cupPairingCochains`), and `W = t ∪ c_χ - f` is a cocycle in `K_Sˣ` congruent to
`t ^ {c_χ}`. The cone cycle is then cohomologous to `(0, (W|_v + a_v ∪ c_χ)_v)`, whose class is
`localToCompact` of the local classes (`exists_compactCup_const`, `homologyδ_homologyπ_eq_localToCompact`).
The sign of `compactCup_compactSupportδ_add_compactCup_δ` in degree `r = 1` is absorbed by
`eq_of_add_neg_one_pow_one_smul_eq_zero`.

## Declarations

In the order of the file:

- `mappingCoconeNat_d_hom_apply'` (theorem).
- `coconeLeft_homology_eq_homologyδ` (theorem): A cocone-left product of a cocycle `(x, y)` with a cocycle `e`, when `x · e = d q`, is the connecting image of the cycle `y · e - f'(q)`.
- `exists_coconeLeft_homology_eq_homologyδ` (theorem): The existence form of `coconeLeft_homology_eq_homologyδ`.
- `homologyδ_homologyπ_eq_localToCompact` (theorem): The connecting map of the cocone on the class of a cycle of the local terms is `localToCompact` of its components.
- `compactSupportMap_compactCup` (theorem): **Naturality of the cup product with compact support in the target.**
- `compactCup_congr` (theorem): The cup product with compact support depends only on the local pairings, not on the proofs of compatibility.
- `lsmul_uliftUp` (theorem).
- `intMulPairingRes` (def): The multiplication pairing `Res ℤ ⊗ A → A` for a module of a group `K` mapping to `G`.
- `intActPairing` (def): The action pairing `A ⊗ ℤ → A`, `a ⊗ m ↦ m • a`.
- `intActPairing_tmul` (theorem).
- `intActPairingRes` (def): The action pairing `A ⊗ Res ℤ → A` for a module of a group `K` mapping to `G`.
- `intActPairingRes_tmul` (theorem).
- `resTensorHom_id_id` (theorem).
- `tensor_intActPairing_eq` (theorem): `x ⊗ m ↦ m • f(x)` and `x ⊗ m ↦ f((m mod n) · x)` agree on a module killed by `n`.
- `tensor_intActPairingRes_eq` (theorem): The local form of `tensor_intActPairing_eq`.
- `tensor_nsmul_intActPairing_eq` (theorem).
- `tensor_nsmul_intActPairingRes_eq` (theorem).
- `res_comp_compat` (theorem): Restriction of a pairing composed with a map, against restricted local maps.
- `eq_of_add_neg_one_pow_one_smul_eq_zero` (theorem).
- `intActPairing_res_compat` (theorem): Restriction of the action pairing against a local map.
- `localFamilyHom` (abbrev): The localization homomorphism at `v ∈ S`, as a monoid homomorphism.
- `unitsCup` (def): The cup product `H_c¹(G_S, 𝒪_Sˣ) × Hˢ(G_S, ℤ) → H_c^{1+s}(G_S, 𝒪_Sˣ)` along the action `𝒪_Sˣ ⊗ ℤ → 𝒪_Sˣ` (and `K̄_vˣ ⊗ ℤ → K̄_vˣ` at the places of `S`).
- `compactSupportMap_compactCupRes_kummerCompactδ` (theorem): **Kummer and Bockstein.** The image in `H_c³(G_S, 𝒪_Sˣ)` of `δ_c(e) ∪ χ` (cup product `μ_n ⊗ ℤ/n → μ_n`) is `e ∪ δχ` (cup product `𝒪_Sˣ ⊗ ℤ → 𝒪_Sˣ`).
- `exists_cocycle_δ_bockSeq` (theorem): The Bockstein of a character `z ∈ H¹(G, ℤ/n)` is the class of the integer cocycle `bockInt z`.
- `cupCochain_const_left` (theorem).
- `constCupSub` (def): `m ∪ e - j(z)`, a cochain of `X`.
- `cochainOf_constCupSub` (theorem).
- `d_constCupSub` (theorem).
- `exists_compactCup_const` (theorem): **The cup product of a class `(x, (l_v m)_v)` with `x = d m` in `X`.** If `x ∪ e = d z` with `z` a cochain of `U`, then the cup product with compact support of the class with the class of `e` is the image under `localToCompact` of the localizations of the cocycle `m ∪ e - j(z)` of `X`.
- `exists_d_eq_cupPairingCochains` (theorem): A cup product of cocycles whose class vanishes is the coboundary of a cochain.
- `intActPairing_sUnitsToUnits` (theorem).
- `toMul_mul_zpow_inv_mem` (theorem): An element `u` of `K_Sˣ` with `u = b • t - w` (additively) for an `S`-unit `w`.
- `exists_unitsData_cup_bock` (theorem): **The cup product of the class of `(t, 1)` with the Bockstein of `χ`.** It is the image under `localToCompact` of the localizations of a `2`-cocycle `W` of `G_S` in `K_Sˣ` with `W(g, h) ≡ t ^ {c_χ(g, h)}` modulo `𝒪_Sˣ`.
- `localUnitsCup` (def): The local cup symbol `a_v ∪ δχ_v ∈ H²(K_v, K̄_vˣ)` of a unit `a_v ∈ K_vˣ` with the localization of a class `b ∈ H²(G_S, ℤ)`.
- `exists_unitsData_cup_bock'` (theorem): **The cup product of the class of a datum `(t, a)` with the Bockstein of `χ`**: the image under `localToCompact` of `(W|_{K_v} + a_v ∪ δχ_v)_v`, `W` a `2`-cocycle of `G_S` in `K_Sˣ` with `W ≡ t ^ {c_χ}` modulo `𝒪_Sˣ`.
- `exists_compactCupRes_kummerCompactδ_unitsData` (theorem): **The cup product of the Kummer class with compact support of a datum with a character**, in `H_c³(G_S, 𝒪_Sˣ)`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files `src/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseCupCone.lean`, `src/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseCupGlob.lean`, `src/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseCupNat.lean`, `src/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseCupFormula.lean`, `src/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseCupKummer.lean`, `src/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseCupLocal.lean` and `src/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseCupGlobal.lean`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The Library's `compactCup`, `compactCupRes`, `compactSupportδ`, `compactCup_compactSupportδ_add_compactCup_δ`, `LeibnizPairing`, `bockSeq` and `exists_cocycle_cupPairing_δ_bockSeq` replace the source's cup products with compact support, its Leibniz pairings and Bockstein sequence; the comparison of the source's two local Kummer sequences is not needed, the Library's local Kummer sequence having `μ_n(K_S)` as first term.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition, corrected printing (Springer, 2013), Chapter VIII, §6, the explicit description of the duality pairing for finite modules (a
  cochain `z ∈ C²(G_S, 𝒪_Sˣ)` with `x ∪ x' = ∂z`, which exists since `H³(G_S, 𝒪_Sˣ)(p) = 0`) and
  Proposition (8.6.8), pp. 487–488; Proposition (8.3.11), p. 458.
