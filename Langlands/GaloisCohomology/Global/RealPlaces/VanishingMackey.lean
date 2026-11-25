import Langlands.GaloisCohomology.Global.RealPlaces.VanishingPlaces

/-!
# The vanishing of `Ĥ_cʳ(G_S, Coind_W(ℤ/2))` in degrees `≥ 4`

**Transfer** (`bijective_trivial_transfer`). Let `E : W ≅ Γ` be an isomorphism of topological groups,
`(f_p : C_p → W)` and `(g_q : D_q → Γ)` families of continuous homomorphisms, `β : P ≃ Q` a bijection of
the index sets and `e_p : C_p ≅ D_{β p}` isomorphisms with `E ∘ f_p = g_{β p} ∘ e_p`. For a trivial module
`V`, if the restrictions `Hⁿ(Γ, V) → ∏_q Hⁿ(D_q, V)` form a bijection, so do `Hⁿ(W, V) → ∏_p Hⁿ(C_p, V)`.

**The real places of `G_S`.** Let `L ⊆ K_S` be a finite extension of `K`, `W = G_S(L)` the open subgroup
fixing it and `N` a smooth `W`-module. By Shapiro's lemma and the Mackey formula
(`mackeyCohomologyEquiv_map`), the localization of `Hⁿ(G_S, Coind_W N)` to the real places of `K` is the
family of maps `Hⁿ(W, N) → Hⁿ(D_w ∩ x⁻¹ W x, N)` along the conjugations, over the real places `w` and the
double cosets `W x D_w` (`bijective_realLocalization_coind_iff`). As `D_w` has order `2`, a Mackey
subgroup is `D_w` or trivial, and in positive degree only the top double cosets count
(`bijective_mackey_real_iff_top`). These correspond to the real places of `L`
(`realMackeyPlaceEquiv`), compatibly with `W ≅ G_{S_L}(L)` and the localizations of `G_{S_L}(L)`
(`fixingOpenSubgroupEquiv_mackeyConj_eq_realLocalizationHom`), so for `N = ℤ/2` the localization is
bijective in degrees `≥ 3` by `bijective_realLocalization_zmodRep_two` for `L`
(`bijective_realLocalization_coind_zmodRep_two`).

**Theorem** (`subsingleton_compactCohomology_coind_zmodRep_two`). If `S` contains the places above `2`,
then `Ĥ_cʳ(G_S, Coind_W(ℤ/2)) = 0` for every open subgroup `W` of `G_S` and every `r ≥ 4`.
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain
open GaloisGroupUnramifiedOutside Langlands.GaloisCohomology.PoitouTate

universe u

noncomputable section

section Transfer

variable {k G Γ : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {V : OpenSubgroup G}
  (E : (V : Subgroup G) ≃ₜ* Γ) {A : Rep.{u} k (V : Subgroup G)} {B : Rep.{u} k Γ} [IsSmoothRep A]
  [IsSmoothRep B] (a : Rep.res E.toMulEquiv.toMonoidHom B ⟶ A) (ha : Function.Bijective a.hom)
  {P : Type u} {C : P → Type u} [∀ p, Group (C p)] [∀ p, TopologicalSpace (C p)]
  [∀ p, IsTopologicalGroup (C p)] (f : ∀ p, C p →ₜ* (V : Subgroup G))
  {Q : Type u} {D : Q → Type u} [∀ q, Group (D q)] [∀ q, TopologicalSpace (D q)]
  [∀ q, IsTopologicalGroup (D q)] (g : ∀ q, D q →ₜ* Γ)
  (β : P ≃ Q) (e : ∀ p, C p ≃ₜ* D (β p)) (he : ∀ p c, E (f p c) = g (β p) (e p c))
  [hfA : ∀ p, IsSmoothRep (Rep.res (f p : C p →* (V : Subgroup G)) A)]
  [hgB : ∀ q, IsSmoothRep (Rep.res (g q : D q →* Γ) B)]

/-- The coefficient map `Res_{e_p} Res_{g_{β p}} B → Res_{f_p} A` given by `a`. -/
def transferCoeff (p : P) :
    Rep.res (e p).toMulEquiv.toMonoidHom (Rep.res (g (β p) : D (β p) →* Γ) B) ⟶
      Rep.res (f p : C p →* (V : Subgroup G)) A :=
  Rep.ofHom ⟨a.hom.toLinearMap, fun c => by
    ext x
    change a.hom (B.ρ (g (β p) (e p c)) x) = A.ρ (f p c) (a.hom x)
    rw [← he p c]
    exact Rep.hom_comm_apply a (f p c) x⟩

include ha he in
/-- **Transfer of restrictions** along isomorphisms of the groups, of the families and of the
modules. -/
theorem bijective_res_transfer (n : ℕ)
    (h : Function.Bijective fun (x : cohomology B n) (q : Q) => (map (g q) (𝟙 _) n).hom x) :
    Function.Bijective fun (x : cohomology A n) (p : P) => (map (f p) (𝟙 _) n).hom x := by
  let ΦE := map ⟨E.toMulEquiv.toMonoidHom, E.continuous⟩ a n
  have hΦE : Function.Bijective ΦE.hom := by
    have := isIso_map_of_mulEquiv E.toMulEquiv E.continuous E.symm.continuous a ha n
    exact ConcreteCategory.bijective_of_isIso _
  have hb : ∀ p, Function.Bijective (map ⟨(e p).toMulEquiv.toMonoidHom, (e p).continuous⟩
      (transferCoeff E a f g β e he p) n).hom := fun p => by
    have := isIso_map_of_mulEquiv (e p).toMulEquiv (e p).continuous (e p).symm.continuous
      (transferCoeff E a f g β e he p) ha n
    exact ConcreteCategory.bijective_of_isIso _
  let Ψ : (∀ q, cohomology (Rep.res (g q : D q →* Γ) B) n) →
      ∀ p, cohomology (Rep.res (f p : C p →* (V : Subgroup G)) A) n :=
    fun t p => (map ⟨(e p).toMulEquiv.toMonoidHom, (e p).continuous⟩
      (transferCoeff E a f g β e he p) n).hom (t (β p))
  have hΨ : Function.Bijective Ψ := by
    have h1 : Function.Bijective fun (t : ∀ q, cohomology (Rep.res (g q : D q →* Γ) B) n) (p : P) =>
        t (β p) :=
      (Equiv.piCongrLeft (fun q => cohomology (Rep.res (g q : D q →* Γ) B) n) β).symm.bijective
    have h2 : Function.Bijective fun (t : ∀ p, cohomology (Rep.res (g (β p) : D (β p) →* Γ) B) n)
        (p : P) => (map ⟨(e p).toMulEquiv.toMonoidHom, (e p).continuous⟩
          (transferCoeff E a f g β e he p) n).hom (t p) := by
      refine ⟨fun t t' htt' => funext fun p => (hb p).1 (congrFun htt' p), fun s => ?_⟩
      exact ⟨fun p => ((hb p).2 (s p)).choose, funext fun p => ((hb p).2 (s p)).choose_spec⟩
    exact h2.comp h1
  have key : (fun (x : cohomology A n) (p : P) => (map (f p) (𝟙 _) n).hom x) ∘ ΦE.hom =
      Ψ ∘ fun (x : cohomology B n) (q : Q) => (map (g q) (𝟙 _) n).hom x := by
    funext x p
    change (map (f p) (𝟙 _) n).hom ((map ⟨E.toMulEquiv.toMonoidHom, E.continuous⟩ a n).hom x) =
      (map ⟨(e p).toMulEquiv.toMonoidHom, (e p).continuous⟩ (transferCoeff E a f g β e he p) n).hom
        ((map (g (β p)) (𝟙 _) n).hom x)
    rw [map_map_apply, map_map_apply]
    have hφ : (⟨E.toMulEquiv.toMonoidHom, E.continuous⟩ : (V : Subgroup G) →ₜ* Γ).comp (f p) =
        (g (β p)).comp ⟨(e p).toMulEquiv.toMonoidHom, (e p).continuous⟩ :=
      ContinuousMonoidHom.ext fun c => he p c
    exact congrArg (fun F => ModuleCat.Hom.hom F x) (map_congr _ _ hφ (fun _ => rfl) n)
  refine (Function.Bijective.of_comp_iff _ hΦE).1 ?_
  rw [key]
  exact hΨ.comp h

end Transfer

section MackeyAbstract

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, CompactSpace (F w)] (ψ : ∀ w, F w →ₜ* G)
  (V : OpenSubgroup G) (N : Rep.{u} k (V : Subgroup G)) [IsSmoothRep N]

/-- **Shapiro and Mackey for a family.** The restrictions of `Hⁿ(G, Coind_V N)` to the groups `F_w` form a
bijection if and only if the maps `Hⁿ(V, N) → Hⁿ(F_w ∩ x⁻¹ V x, N)` along the conjugations, over the
`w` and the double cosets `V x ψ_w(F_w)`, do. -/
theorem bijective_res_coind_iff_mackey (n : ℕ) :
    Function.Bijective (fun (x : cohomology (Rep.coind (V : Subgroup G).subtype N) n) (w : κ) =>
      (map (ψ w) (𝟙 (Rep.res (ψ w : F w →* G) (Rep.coind (V : Subgroup G).subtype N))) n).hom x) ↔
    Function.Bijective (fun (c : cohomology N n) (w : κ)
      (d : MackeyDoubleCoset (V : Subgroup G) (ψ w).toMonoidHom) =>
        (map (mackeyConjₜ V (ψ w) d.out) (𝟙 _) n).hom c) := by
  have hM : ∀ w, Function.Bijective fun (a : cohomology (Rep.res (ψ w : F w →* G)
      (Rep.coind (V : Subgroup G).subtype N)) n)
      (d : MackeyDoubleCoset (V : Subgroup G) (ψ w).toMonoidHom) =>
        (show cohomology (Rep.res (mackeyConjₜ V (ψ w) d.out :
            mackeySubgroup (V : Subgroup G) (ψ w).toMonoidHom d.out →* (V : Subgroup G)) N) n from
          (mackeyCohomologyMap V (ψ w) N d.out n).hom a) :=
    fun w => mackeyCohomology_bijective V (ψ w) N n
  have hS : Function.Bijective (shapiroMap V N n).hom := by
    have := isIso_shapiroMap V n N
    exact ConcreteCategory.bijective_of_isIso _
  have key : ∀ (x : cohomology (Rep.coind (V : Subgroup G).subtype N) n) (w : κ)
      (d : MackeyDoubleCoset (V : Subgroup G) (ψ w).toMonoidHom),
      (show cohomology (Rep.res (mackeyConjₜ V (ψ w) d.out :
          mackeySubgroup (V : Subgroup G) (ψ w).toMonoidHom d.out →* (V : Subgroup G)) N) n from
        (mackeyCohomologyMap V (ψ w) N d.out n).hom
          ((map (ψ w) (𝟙 (Rep.res (ψ w : F w →* G) (Rep.coind (V : Subgroup G).subtype N))) n).hom x)) =
        (map (mackeyConjₜ V (ψ w) d.out) (𝟙 _) n).hom ((shapiroMap V N n).hom x) := fun x w d =>
    hom_apply_hom_apply_eq_of_comp_eq (map_comp_mackeyCohomologyMap V (ψ w) N d.out n) x
  constructor
  · rintro ⟨hi, hs⟩
    refine ⟨fun c c' hcc => ?_, fun s => ?_⟩
    · obtain ⟨x, rfl⟩ := hS.2 c
      obtain ⟨x', rfl⟩ := hS.2 c'
      refine congrArg _ (hi (funext fun w => (hM w).1 (funext fun d => ?_)))
      exact (key x w d).trans ((congrFun (congrFun hcc w) d).trans (key x' w d).symm)
    · choose t ht using fun w => (hM w).2 (s w)
      obtain ⟨x, hx⟩ := hs t
      refine ⟨(shapiroMap V N n).hom x, funext fun w => funext fun d => ?_⟩
      refine (key x w d).symm.trans ?_
      have hxw := congrFun hx w
      beta_reduce at hxw
      rw [hxw]
      exact congrFun (ht w) d
  · rintro ⟨hi, hs⟩
    refine ⟨fun x x' hxx => hS.1 (hi (funext fun w => funext fun d => ?_)), fun t => ?_⟩
    · refine (key x w d).symm.trans (Eq.trans ?_ (key x' w d))
      exact congrArg (fun a => (show cohomology (Rep.res (mackeyConjₜ V (ψ w) d.out :
            mackeySubgroup (V : Subgroup G) (ψ w).toMonoidHom d.out →* (V : Subgroup G)) N) n from
          (mackeyCohomologyMap V (ψ w) N d.out n).hom a)) (congrFun hxx w)
    · obtain ⟨c, hc⟩ := hs fun w d =>
        (show cohomology (Rep.res (mackeyConjₜ V (ψ w) d.out :
            mackeySubgroup (V : Subgroup G) (ψ w).toMonoidHom d.out →* (V : Subgroup G)) N) n from
          (mackeyCohomologyMap V (ψ w) N d.out n).hom (t w))
      obtain ⟨x, rfl⟩ := hS.2 c
      refine ⟨x, funext fun w => (hM w).1 (funext fun d => ?_)⟩
      exact (key x w d).trans (congrFun (congrFun hc w) d)

end MackeyAbstract


section GS

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) {S : Set (HeightOneSpectrum (𝓞 K))}

omit [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] in
/-- A proper subgroup of the Galois group of a real place is trivial. -/
theorem subsingleton_of_ne_top_closureGalois (w : InfinitePlace K) (hw : w.IsReal)
    (P : Subgroup Gal(AlgebraicClosure w.Completion/w.Completion)) (hP : P ≠ ⊤) : Subsingleton P := by
  have : Fact (Nat.card Gal(AlgebraicClosure w.Completion/w.Completion)).Prime :=
    ⟨by rw [card_closureGalois w hw]; exact Nat.prime_two⟩
  rw [P.eq_bot_or_eq_top_of_prime_card.resolve_right hP]
  infer_instance

variable {L : Type u} [Field L] [NumberField L] [Algebra K L] [Algebra L Ω] [IsScalarTower K L Ω]
  (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S)

/-- A top Mackey subgroup at a real place is the Galois group of the attached real place of `L`. -/
def realMackeyLocalEquiv (p : RealMackeyTop S hL ι) :
    mackeySubgroup (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S))
        (realLocalizationHom ι S p.1.1.1).toMonoidHom p.1.2.out ≃ₜ*
      Gal(AlgebraicClosure (realMackeyPlaceEquiv hL ι p).1.Completion /
        (realMackeyPlaceEquiv hL ι p).1.Completion) :=
  { ((MulEquiv.subgroupCongr p.2).trans Subgroup.topEquiv).trans
      (realClosureGaloisEquiv p.1.1.1 p.1.1.2 (realMackeyPlace hL ι p).1 (realMackeyPlace hL ι p).2) with
    continuous_toFun := continuous_of_discreteTopology
    continuous_invFun := continuous_of_discreteTopology }

theorem realMackeyLocalEquiv_apply (p : RealMackeyTop S hL ι)
    (σ : mackeySubgroup (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S))
      (realLocalizationHom ι S p.1.1.1).toMonoidHom p.1.2.out) :
    realMackeyLocalEquiv ι hL p σ =
      realClosureGaloisEquiv p.1.1.1 p.1.1.2 (realMackeyPlace hL ι p).1 (realMackeyPlace hL ι p).2 σ.1 :=
  rfl

/-- **The real places and `Coind_W(ℤ/2)`.** If `S` contains the places above `2` and `W` is the open
subgroup fixing `L`, the localization `Hʳ(G_S, Coind_W(ℤ/2)) → ∏_{w real} Hʳ(K_w, Coind_W(ℤ/2))` is
bijective for `r ≥ 3`. -/
theorem bijective_realLocalization_coind_zmodRep_two
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), ((2 : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    [IsSepClosure L Ω] {r : ℕ} (hr : 3 ≤ r) :
    Function.Bijective fun (x : cohomology (Rep.coind (fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (zmodRep.{u} (fixingOpenSubgroup S hL :
          Subgroup (GaloisGroupUnramifiedOutside K Ω S)) 2)) r)
      (w : {w : InfinitePlace K // w.IsReal}) =>
        realLocalization ι (Rep.coind (fixingOpenSubgroup S hL :
          Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (zmodRep.{u} (fixingOpenSubgroup S hL :
            Subgroup (GaloisGroupUnramifiedOutside K Ω S)) 2)) w.1 r x := by
  have : IsGalois L Ω := IsGalois.tower_top_of_isGalois K L Ω
  -- Shapiro and Mackey, then the top double cosets
  have h1 := bijective_res_coind_iff_mackey
    (fun w : {w : InfinitePlace K // w.IsReal} => realLocalizationHom ι S w.1)
    (fixingOpenSubgroup S hL) (zmodRep.{u} (fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)) 2) r
  have h2' := bijective_mackey_iff_top
    (fun w : {w : InfinitePlace K // w.IsReal} => realLocalizationHom ι S w.1)
    (fixingOpenSubgroup S hL) (zmodRep.{u} (fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)) 2) (n := r) (by omega)
    (fun w d hd => subsingleton_of_ne_top_closureGalois w.1 w.2 _ hd)
  -- the real places of `L`
  let ι₀ : PlaceEmbeddings L Ω := Classical.arbitrary _
  let ιL := realPlaceEmbeddingsOver hL ι ι₀
  have h2L : ∀ v : HeightOneSpectrum (𝓞 L), ((2 : ℕ) : 𝓞 L) ∈ v.asIdeal →
      v ∈ finitePlacesAbove L S := fun v hv => by
    rw [mem_finitePlacesAbove_iff_under]
    refine h2 _ ?_
    change algebraMap (𝓞 K) (𝓞 L) ((2 : ℕ) : 𝓞 K) ∈ v.asIdeal
    rw [map_natCast]
    exact hv
  have hLbij := bijective_realLocalization_zmodRep_two ιL (finitePlacesAbove L S) h2L hr
  have ht := bijective_res_transfer
    (C := fun p : RealMackeyTop S hL ι => mackeySubgroup (fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)) (realLocalizationHom ι S p.1.1.1).toMonoidHom
        p.1.2.out)
    (D := fun q : {w' : InfinitePlace L // w'.IsReal} =>
      Gal(AlgebraicClosure q.1.Completion/q.1.Completion))
    (A := zmodRep.{u} (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) 2)
    (B := zmodRep.{u} (GaloisGroupUnramifiedOutside L Ω (finitePlacesAbove L S)) 2)
    (fixingOpenSubgroupEquiv S hL) (Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩) Function.bijective_id
    (fun p : RealMackeyTop S hL ι =>
      mackeyConjₜ (fixingOpenSubgroup S hL) (realLocalizationHom ι S p.1.1.1) p.1.2.out)
    (fun q : {w' : InfinitePlace L // w'.IsReal} => realLocalizationHom ιL (finitePlacesAbove L S) q.1)
    (realMackeyPlaceEquiv hL ι) (realMackeyLocalEquiv ι hL)
    (fun p σ => fixingOpenSubgroupEquiv_mackeyConj_eq_realLocalizationHom hL ι ι₀ p σ)
    (hfA := fun p => isSmoothRep_res _ _) (hgB := fun q => isSmoothRep_res _ _) r hLbij
  beta_reduce at h1 h2' ht
  unfold RealMackeyTop at ht
  exact h1.2 (h2'.2 ht)

end GS

section Coind

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) {S : Set (HeightOneSpectrum (𝓞 K))}

/-- **Vanishing for `Coind_W(ℤ/2)`.** If `S` contains the places above `2`, then
`Ĥ_cʳ(G_S, Coind_W(ℤ/2)) = 0` for every open subgroup `W` of `G_S` and every `r ≥ 4`. -/
theorem subsingleton_compactCohomology_coind_zmodRep_two
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), ((2 : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (W : OpenSubgroup (GaloisGroupUnramifiedOutside K Ω S)) {r : ℕ} (hr : 4 ≤ r) :
    Subsingleton (compactCohomology ι
      (Rep.coind (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
        (zmodRep.{u} (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) 2)) r) := by
  obtain ⟨L, _, hL, rfl⟩ := exists_fixingOpenSubgroup_eq W
  obtain ⟨p, rfl⟩ : ∃ p, r = p + 1 := ⟨r - 1, by omega⟩
  exact subsingleton_compactCohomology_of_surjective_of_injective ι two_ne_zero _
    (nsmul_coind_zmodRep_eq_zero _) (by omega)
    (bijective_realLocalization_coind_zmodRep_two ι hL h2 (by omega)).2
    (bijective_realLocalization_coind_zmodRep_two ι hL h2 (by omega)).1

end Coind

end

end Langlands.GaloisCohomology
