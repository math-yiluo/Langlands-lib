# The vanishing of `Ĥ_cʳ(G_S, Coind_W(ℤ/2))` in degrees `≥ 4`

`Langlands/GaloisCohomology/Global/RealPlaces/VanishingMackey.lean`, namespace `Langlands.GaloisCohomology`.

**Transfer** (`bijective_res_transfer`). Let `V` be an open subgroup of a group `G`, `E : V ≅ Γ` an
isomorphism of topological groups, `a : Res_E B → A` a bijective morphism of modules, `(f_p : C_p → V)` and
`(g_q : D_q → Γ)` families of continuous homomorphisms, `β : P ≃ Q` a bijection of the index sets and
`e_p : C_p ≅ D_{β p}` isomorphisms with `E ∘ f_p = g_{β p} ∘ e_p`. If the restrictions
`Hⁿ(Γ, B) → ∏_q Hⁿ(D_q, B)` form a bijection, so do `Hⁿ(V, A) → ∏_p Hⁿ(C_p, A)` (`transferCoeff`: the
coefficient maps given by `a`).

**Shapiro and Mackey** (`bijective_res_coind_iff_mackey`). For a compact group `G`, a family of compact
groups `ψ_w : F_w → G`, an open subgroup `V` and a smooth `V`-module `N`, the restrictions of
`Hⁿ(G, Coind_V N)` to the `F_w` form a bijection if and only if the maps `Hⁿ(V, N) → Hⁿ(F_w ∩ x⁻¹ V x, N)`
along the conjugations, over the `w` and the double cosets `V x F_w`, do; in positive degree, if the
Mackey subgroups other than `F_w` are trivial, only the top double cosets count
(`bijective_mackey_iff_top` of the module `Langlands.Cohomology.Profinite.Mackey.Cohomology`, with
`subsingleton_cohomology_of_subsingleton_group` of `Langlands.Cohomology.Profinite.Comparison.FiniteQuotients`:
the cohomology of the trivial group vanishes in positive degree); `subsingleton_of_ne_top_closureGalois`: a proper subgroup of the
Galois group of a real place is trivial.

**For `G_S`.** Let `L ⊆ K_S` be a finite extension of `K` and `W = G_S(L)`. `realMackeyLocalEquiv`: a top
Mackey subgroup at a real place is the Galois group of the attached real place of `L`.
`bijective_realLocalization_coind_zmodRep_two`: if `S` contains the places above `2`, the localization
`Hʳ(G_S, Coind_W(ℤ/2)) → ∏_{w real} Hʳ(K_w, Coind_W(ℤ/2))` is bijective for `r ≥ 3`.

**Theorem** (`subsingleton_compactCohomology_coind_zmodRep_two`). If `S` contains the places above `2`,
then `Ĥ_cʳ(G_S, Coind_W(ℤ/2)) = 0` for every open subgroup `W` of `G_S` and every `r ≥ 4`.

## Complete types

As printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.transferCoeff.{u} {k G Γ : Type u} [CommRing k] [Group G] [TopologicalSpace G] [Group Γ]
  [TopologicalSpace Γ] {V : OpenSubgroup G} (E : ↥↑V ≃ₜ* Γ) {A : Rep.{u, u, u} k ↥↑V} {B : Rep.{u, u, u} k Γ}
  (a : Rep.res E.toMonoidHom B ⟶ A) {P : Type u} {C : P → Type u} [(p : P) → Group (C p)]
  [(p : P) → TopologicalSpace (C p)] (f : (p : P) → C p →ₜ* ↥↑V) {Q : Type u} {D : Q → Type u} [(q : Q) → Group (D q)]
  [(q : Q) → TopologicalSpace (D q)] (g : (q : Q) → D q →ₜ* Γ) (β : P ≃ Q) (e : (p : P) → C p ≃ₜ* D (β p))
  (he : ∀ (p : P) (c : C p), E ((f p) c) = (g (β p)) ((e p) c)) (p : P) :
  Rep.res (e p).toMonoidHom (Rep.res (↑(g (β p))) B) ⟶ Rep.res (↑(f p)) A
Langlands.GaloisCohomology.bijective_res_transfer.{u} {k G Γ : Type u} [CommRing k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {V : OpenSubgroup G} (E : ↥↑V ≃ₜ* Γ)
  {A : Rep.{u, u, u} k ↥↑V} {B : Rep.{u, u, u} k Γ} [Langlands.IsSmoothRep A] [Langlands.IsSmoothRep B]
  (a : Rep.res E.toMonoidHom B ⟶ A) (ha : Function.Bijective ⇑(Rep.Hom.hom a)) {P : Type u} {C : P → Type u}
  [(p : P) → Group (C p)] [(p : P) → TopologicalSpace (C p)] [∀ (p : P), IsTopologicalGroup (C p)]
  (f : (p : P) → C p →ₜ* ↥↑V) {Q : Type u} {D : Q → Type u} [(q : Q) → Group (D q)] [(q : Q) → TopologicalSpace (D q)]
  [∀ (q : Q), IsTopologicalGroup (D q)] (g : (q : Q) → D q →ₜ* Γ) (β : P ≃ Q) (e : (p : P) → C p ≃ₜ* D (β p))
  (he : ∀ (p : P) (c : C p), E ((f p) c) = (g (β p)) ((e p) c))
  [hfA : ∀ (p : P), Langlands.IsSmoothRep (Rep.res (↑(f p)) A)]
  [hgB : ∀ (q : Q), Langlands.IsSmoothRep (Rep.res (↑(g q)) B)] (n : ℕ)
  (h :
    Function.Bijective fun x q =>
      (ModuleCat.Hom.hom
          (Langlands.ProfiniteCohomology.map (g q) (CategoryTheory.CategoryStruct.id (Rep.res (↑(g q)) B)) n))
        x) :
  Function.Bijective fun x p =>
    (ModuleCat.Hom.hom
        (Langlands.ProfiniteCohomology.map (f p) (CategoryTheory.CategoryStruct.id (Rep.res (↑(f p)) A)) n))
      x
Langlands.GaloisCohomology.bijective_res_coind_iff_mackey.{u} {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] {κ : Type u} {F : κ → Type u} [(w : κ) → Group (F w)]
  [(w : κ) → TopologicalSpace (F w)] [∀ (w : κ), IsTopologicalGroup (F w)] [∀ (w : κ), CompactSpace (F w)]
  (ψ : (w : κ) → F w →ₜ* G) (V : OpenSubgroup G) (N : Rep.{u, u, u} k ↥↑V) [Langlands.IsSmoothRep N] (n : ℕ) :
  (Function.Bijective fun x w =>
      (ModuleCat.Hom.hom
          (Langlands.ProfiniteCohomology.map (ψ w)
            (CategoryTheory.CategoryStruct.id (Rep.res (↑(ψ w)) (Rep.coind.{u, u, u, u} (↑V).subtype N))) n))
        x) ↔
    Function.Bijective fun c w d =>
      (ModuleCat.Hom.hom
          (Langlands.ProfiniteCohomology.map (Langlands.ProfiniteCohomology.mackeyConjₜ V (ψ w) (Quotient.out d))
            (CategoryTheory.CategoryStruct.id
              (Rep.res (↑(Langlands.ProfiniteCohomology.mackeyConjₜ V (ψ w) (Quotient.out d))) N))
            n))
        c
Langlands.GaloisCohomology.subsingleton_of_ne_top_closureGalois.{u} {K : Type u} [Field K] [NumberField K]
  (w : NumberField.InfinitePlace K) (hw : w.IsReal) (P : Subgroup Gal(AlgebraicClosure w.Completion/w.Completion))
  (hP : P ≠ ⊤) : Subsingleton ↥P
Langlands.GaloisCohomology.realMackeyLocalEquiv.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {L : Type u} [Field L] [NumberField L]
  [Algebra K L] [Algebra L Ω] [IsScalarTower K L Ω]
  (hL : ∀ (x : L), (Algebra.algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (p : Langlands.GaloisCohomology.RealMackeyTop S hL ι) :
  ↥(Langlands.ProfiniteCohomology.mackeySubgroup
        (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL))
        (Langlands.Galois.realLocalizationHom ι S ↑(↑p).fst).toMonoidHom (Quotient.out (↑p).snd)) ≃ₜ*
    Gal(AlgebraicClosure
        (↑((Langlands.GaloisCohomology.realMackeyPlaceEquiv hL ι)
              p)).Completion/(↑((Langlands.GaloisCohomology.realMackeyPlaceEquiv hL ι) p)).Completion)
Langlands.GaloisCohomology.realMackeyLocalEquiv_apply.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {L : Type u} [Field L] [NumberField L]
  [Algebra K L] [Algebra L Ω] [IsScalarTower K L Ω]
  (hL : ∀ (x : L), (Algebra.algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (p : Langlands.GaloisCohomology.RealMackeyTop S hL ι)
  (σ :
    ↥(Langlands.ProfiniteCohomology.mackeySubgroup
        (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL))
        (Langlands.Galois.realLocalizationHom ι S ↑(↑p).fst).toMonoidHom (Quotient.out (↑p).snd))) :
  (Langlands.GaloisCohomology.realMackeyLocalEquiv ι hL p) σ =
    (Langlands.GaloisCohomology.realClosureGaloisEquiv ↑(↑p).fst ⋯ ↑(Langlands.GaloisCohomology.realMackeyPlace hL ι p)
        ⋯)
      ↑σ
Langlands.GaloisCohomology.bijective_realLocalization_coind_zmodRep_two.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {L : Type u} [Field L] [NumberField L]
  [Algebra K L] [Algebra L Ω] [IsScalarTower K L Ω]
  (hL : ∀ (x : L), (Algebra.algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (h2 : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑2 ∈ v.asIdeal → v ∈ S)
  [IsSepClosure L Ω] {r : ℕ} (hr : 3 ≤ r) :
  Function.Bijective fun x w =>
    (Langlands.GaloisCohomology.realLocalization ι
        (Rep.coind.{u, u, u, u} (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).subtype
          (Langlands.ProfiniteCohomology.zmodRep
            (↥↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)) 2))
        (↑w) r)
      x
Langlands.GaloisCohomology.subsingleton_compactCohomology_coind_zmodRep_two.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (h2 : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑2 ∈ v.asIdeal → v ∈ S)
  (W : OpenSubgroup (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) {r : ℕ} (hr : 4 ≤ r) :
  Subsingleton
    ↑(Langlands.GaloisCohomology.PoitouTate.compactCohomology ι
        (Rep.coind.{u, u, u, u} (↑W).subtype (Langlands.ProfiniteCohomology.zmodRep (↥↑W) 2)) r)
```

## Outline of the proofs

Transfer: the map along `E` (coefficients `a`) and the maps along the `e_p` are bijective
(`isIso_map_of_mulEquiv`), and the two families correspond through them (`map_map_apply`, `map_congr`
with `E ∘ f_p = g_{β p} ∘ e_p`). Shapiro and Mackey: `mackeyCohomology_bijective` and
`map_comp_mackeyCohomologyMap` for each `w`, and `isIso_shapiroMap`. For `G_S`: the top double cosets at the
real places are the real places of `L` (`realMackeyPlaceEquiv`), the conjugations are the localizations of
`G_{S_L}(L)` for `realPlaceEmbeddingsOver` (`fixingOpenSubgroupEquiv_mackeyConj_eq_realLocalizationHom`),
and over `L` the localization of `ℤ/2` is bijective in degrees `≥ 3`
(`bijective_realLocalization_zmodRep_two`). The vanishing follows by the criterion
`subsingleton_compactCohomology_of_surjective_of_injective`, after writing `W` as the subgroup fixing some
`L` (`exists_fixingOpenSubgroup_eq`).

## Declarations

`transferCoeff`, `bijective_res_transfer`, `bijective_res_coind_iff_mackey`, `subsingleton_of_ne_top_closureGalois`, `realMackeyLocalEquiv`, `realMackeyLocalEquiv_apply`, `bijective_realLocalization_coind_zmodRep_two`, `subsingleton_compactCohomology_coind_zmodRep_two`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files `src/GroundTheory/ProfiniteCohomology/RealPlaces/VanishingMackey.lean` (lines 18–146, 174–178, 202–253) and `src/GroundTheory/ProfiniteCohomology/RealPlaces/VanishingMackeyTransfer.lean` (lines 180–259, 300–380). The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The Library's Mackey formula (`mackeyCohomologyMap`, `mackeyCohomology_bijective`, `map_comp_mackeyCohomologyMap`) and Shapiro map replace the source's `MackeyFormula` files; the injectivity and surjectivity statements are combined into bijectivity; the transfer takes general modules and a bijective coefficient map (the source's `trivialRes_transfer` is for trivial coefficients); the units part of the source (`gsMackeyTop_gsOpenSubgroup` through `injective_gsRealRes_zmodRep_two`) is replaced by `bijective_realLocalization_zmodRep_two`.

The source's `subsingleton_cohomology_of_subsingleton_group` is ported in the module
`Langlands.Cohomology.Profinite.Comparison.FiniteQuotients`, and its `injective_mackeyRealRes_iff`,
`surjective_mackeyRealRes_iff` (as `bijective_mackey_iff_top`) in `Langlands.Cohomology.Profinite.Mackey.Cohomology`.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008; corrected printing 2013), chapter I, §5, Proposition (1.5.6), p. 51 (the double coset formula).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008; corrected printing 2013), chapter VIII, §6, (8.6.10) (long exact sequence of Poitou–Tate; (ii): `Hⁱ(G_S, A) ≅ ⊕_{𝔭 real} Hⁱ(k_𝔭, A)` for `i ≥ 3`), statement p. 489, proof of (ii) pp. 490–491 (degree `3` from the duality of the class formation (8.4.4) and (7.2.17); the degrees `i ≥ 3` by the exact sequence `0 → A → Ind A → B → 0` and induction).
