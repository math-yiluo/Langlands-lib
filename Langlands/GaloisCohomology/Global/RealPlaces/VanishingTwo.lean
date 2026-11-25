import Langlands.GaloisCohomology.Global.RealPlaces.VanishingUnits

/-!
# The localization of `Hʳ(G_S, ℤ/2)` to the real places, `r ≥ 3`

Let `K` be a number field, `Ω` a separable closure, `S` a set of finite places of `K` containing the
places above `2`, `G_S = Gal(K_S/K)` and `ι : PlaceEmbeddings K Ω`.

**Theorem** (`bijective_realLocalization_zmodRep_two`). For every `r ≥ 3` the localization
`Hʳ(G_S, ℤ/2) → ∏_{w real} Hʳ(K_w, ℤ/2)` is bijective.

Proof. The localization is compatible with isomorphisms of modules
(`bijective_realLocalization_of_iso`, from `realLocalization_coeffMap`), and `μ₂ ≅ ℤ/2`
(`dualizingModuleTwoIso`: the Galois action on `±1` is trivial), so degree `3` is
`bijective_realLocalization_dualizingModule_two`. If `K` is totally complex both sides vanish. Otherwise
let `U = G_S(K(i))`, of index `2`, and `c` the image of the complex conjugation of a real place, which is
not in `U`. Then `Ind_U^{G_S}(ℤ/2)/(ℤ/2) ≅ ℤ/2` (`coindQuotientZModTwoIso`, through
`f ↦ f(1) + f(c)`), and the dimension shift `bijective_realLocalization_succ` passes from degree `r` to
degree `r + 1`.
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain
open Langlands.GaloisCohomology.PoitouTate

universe u

noncomputable section

section Transport

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) {S : Set (HeightOneSpectrum (𝓞 K))}

/-- The localization at an infinite place is natural in the module. -/
theorem realLocalization_coeffMap {A B : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)}
    [IsSmoothRep A] [IsSmoothRep B] (f : A ⟶ B) (w : InfinitePlace K) (r : ℕ)
    (x : cohomology A r) :
    realLocalization ι B w r ((coeffMap f r).hom x) =
      (coeffMap ((Rep.resFunctor (realLocalizationHom ι S w :
        Gal(AlgebraicClosure w.Completion/w.Completion) →* GaloisGroupUnramifiedOutside K Ω S)).map f)
          r).hom (realLocalization ι A w r x) := by
  rw [realLocalization_apply, realLocalization_apply, map_coeffMap_hom_apply,
    ← ModuleCat.comp_apply, map_comp_coeffMap, Category.id_comp, Category.comp_id]

/-- Bijectivity of the localization to the real places is preserved by isomorphisms of modules. -/
theorem bijective_realLocalization_of_iso
    {A B : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)} [IsSmoothRep A]
    [IsSmoothRep B] (e : A ≅ B) (r : ℕ)
    (h : Function.Bijective fun (x : cohomology A r) (w : {w : InfinitePlace K // w.IsReal}) =>
      realLocalization ι A w.1 r x) :
    Function.Bijective fun (x : cohomology B r) (w : {w : InfinitePlace K // w.IsReal}) =>
      realLocalization ι B w.1 r x := by
  let Φ : (∀ w : {w : InfinitePlace K // w.IsReal}, cohomology (realLocalModule ι A w.1) r) →
      ∀ w : {w : InfinitePlace K // w.IsReal}, cohomology (realLocalModule ι B w.1) r :=
    fun t w => (coeffMap ((Rep.resFunctor (realLocalizationHom ι S w.1 :
      Gal(AlgebraicClosure w.1.Completion/w.1.Completion) →* GaloisGroupUnramifiedOutside K Ω S)).map
        e.hom) r).hom (t w)
  have hΦ : Function.Bijective Φ := by
    have hw : ∀ w : {w : InfinitePlace K // w.IsReal}, Function.Bijective
        (coeffMap ((Rep.resFunctor (realLocalizationHom ι S w.1 :
          Gal(AlgebraicClosure w.1.Completion/w.1.Completion) →*
            GaloisGroupUnramifiedOutside K Ω S)).map e.hom) r).hom := fun w =>
      bijective_coeffMap_of_iso ((Rep.resFunctor _).mapIso e) r
    refine ⟨fun t t' htt' => funext fun w => (hw w).1 (congrFun htt' w), fun s => ?_⟩
    exact ⟨fun w => ((hw w).2 (s w)).choose, funext fun w => ((hw w).2 (s w)).choose_spec⟩
  have hcomp : (fun (x : cohomology B r) (w : {w : InfinitePlace K // w.IsReal}) =>
      realLocalization ι B w.1 r x) ∘ (coeffMap e.hom r).hom =
      Φ ∘ fun (x : cohomology A r) (w : {w : InfinitePlace K // w.IsReal}) =>
        realLocalization ι A w.1 r x :=
    funext fun x => funext fun w => realLocalization_coeffMap ι e.hom w.1 r x
  refine (Function.Bijective.of_comp_iff _ (bijective_coeffMap_of_iso e r)).1 ?_
  rw [hcomp]
  exact hΦ.comp h

end Transport

section RootsOfUnity

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (HeightOneSpectrum (𝓞 K)))

omit [NumberField K] [IsSepClosure K Ω] in
/-- The Galois action on `μ₂` is trivial. -/
theorem dualizingModule_two_ρ_apply (σ : GaloisGroupUnramifiedOutside K Ω S)
    (x : dualizingModule K Ω S 2) : (dualizingModule K Ω S 2).ρ σ x = x := by
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  change σ (((Additive.toMul x : rootsOfUnity 2 (maximalUnramifiedOutside K Ω S)) :
      (maximalUnramifiedOutside K Ω S)ˣ) : maximalUnramifiedOutside K Ω S) =
    (((Additive.toMul x : rootsOfUnity 2 (maximalUnramifiedOutside K Ω S)) :
      (maximalUnramifiedOutside K Ω S)ˣ) : maximalUnramifiedOutside K Ω S)
  have hx : (((Additive.toMul x : rootsOfUnity 2 (maximalUnramifiedOutside K Ω S)) :
      (maximalUnramifiedOutside K Ω S)ˣ) : maximalUnramifiedOutside K Ω S) *
      (((Additive.toMul x : rootsOfUnity 2 (maximalUnramifiedOutside K Ω S)) :
        (maximalUnramifiedOutside K Ω S)ˣ) : maximalUnramifiedOutside K Ω S) = 1 := by
    rw [← Units.val_mul, ← pow_two]
    exact (congrArg Units.val ((mem_rootsOfUnity 2 _).1 (Additive.toMul x).2)).trans Units.val_one
  rcases mul_self_eq_one_iff.1 hx with h | h <;> rw [h]
  · exact map_one σ
  · rw [map_neg, map_one]

/-- If `S` contains the places above `2`, `μ₂ ≅ ℤ/2` as `G_S`-modules. -/
def dualizingModuleTwoIso
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), ((2 : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) 2 ≅ dualizingModule K Ω S 2 :=
  let e := (nonempty_addEquiv_dualizingModule (Ω := Ω) (S := S) (N := 2) h2).some
  repIsoOfBijective
    (Rep.ofHom ⟨(uliftIntLinearEquivAddHom (zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) 2)
      (dualizingModule K Ω S 2)).symm
        (e.symm.toAddMonoidHom.comp (AddEquiv.ulift : ULift.{u} (ZMod 2) ≃+ ZMod 2).toAddMonoidHom),
      fun σ => LinearMap.ext fun _ => (dualizingModule_two_ρ_apply S σ _).symm⟩)
    ((e.symm.bijective).comp (AddEquiv.ulift : ULift.{u} (ZMod 2) ≃+ ZMod 2).bijective)

end RootsOfUnity

section IndexTwo

variable {G : Type u} [Group G] (U : Subgroup G) {c : G} (hc : c ∉ U)
  (hU : ∀ g, g ∉ U → g * c⁻¹ ∈ U)

/-- On `Ind_U^G(ℤ/2)`, the sum `f(1) + f(c)` of the values at the two cosets. -/
def coindSumTwo (c : G) :
    Rep.coind U.subtype (Rep.res U.subtype (zmodRep.{u} G 2)) →ₗ[ULift.{u} ℤ] ULift.{u} (ZMod 2) where
  toFun f := f.1 1 + f.1 c
  map_add' f g := add_add_add_comm _ _ _ _
  map_smul' a f := by
    change a • f.1 1 + a • f.1 c = a • (f.1 1 + f.1 c)
    rw [smul_add]

theorem coindSumTwo_apply (f : Rep.coind U.subtype (Rep.res U.subtype (zmodRep.{u} G 2))) :
    coindSumTwo U c f = f.1 1 + f.1 c :=
  rfl

/-- The values of a function of `Ind_U^G(ℤ/2)` are constant on the cosets of `U`. -/
theorem coind_zmodRep_apply_mul (f : Rep.coind U.subtype (Rep.res U.subtype (zmodRep.{u} G 2)))
    {u : G} (hu : u ∈ U) (x : G) : f.1 (u * x) = f.1 x :=
  f.2 ⟨u, hu⟩ x

include hc hU in
theorem mul_mem_of_not_mem {g : G} (hg : g ∉ U) : c * g ∈ U := by
  have hgc := hU g hg
  by_contra h
  have h2 := hU (c * g) h
  have e : c = c * g * c⁻¹ * (g * c⁻¹)⁻¹ := by group
  exact hc (e ▸ U.mul_mem h2 (U.inv_mem hgc))

include hc hU in
/-- `f(1) + f(c)` is invariant under `G`. -/
theorem coindSumTwo_ρ (σ : G) (f : Rep.coind U.subtype (Rep.res U.subtype (zmodRep.{u} G 2))) :
    coindSumTwo U c ((Rep.coind U.subtype (Rep.res U.subtype (zmodRep.{u} G 2))).ρ σ f) =
      coindSumTwo U c f := by
  change f.1 (1 * σ) + f.1 (c * σ) = f.1 1 + f.1 c
  rw [one_mul]
  by_cases hσ : σ ∈ U
  · have hcσ : c * σ ∉ U := fun h => hc (by simpa using U.mul_mem h (U.inv_mem hσ))
    have e1 : f.1 σ = f.1 1 := by
      have := coind_zmodRep_apply_mul U f hσ 1
      rwa [mul_one] at this
    have e2 : f.1 (c * σ) = f.1 c := by
      have := coind_zmodRep_apply_mul U f (hU _ hcσ) c
      rwa [inv_mul_cancel_right] at this
    rw [e1, e2]
  · have e1 : f.1 σ = f.1 c := by
      have := coind_zmodRep_apply_mul U f (hU _ hσ) c
      rwa [inv_mul_cancel_right] at this
    have e2 : f.1 (c * σ) = f.1 1 := by
      have := coind_zmodRep_apply_mul U f (mul_mem_of_not_mem U hc hU hσ) 1
      rwa [mul_one] at this
    rw [e1, e2, add_comm]

/-- `f(1) + f(c)` vanishes on the constant functions. -/
theorem coindSumTwo_coindUnit (a : zmodRep.{u} G 2) :
    coindSumTwo U c ((coindUnit U (zmodRep.{u} G 2)).hom a) = 0 := by
  change a + a = 0
  obtain ⟨a⟩ := a
  apply ULift.ext
  change a + a = 0
  rw [← two_mul]
  exact (show (2 : ZMod 2) = 0 from rfl) ▸ zero_mul a

include hc hU in
/-- The map `Ind_U^G(ℤ/2)/(ℤ/2) → ℤ/2`, `f ↦ f(1) + f(c)`. -/
def coindQuotientZModTwo :
    (coindUnitSequence U (zmodRep.{u} G 2)).X₃ ⟶ zmodRep.{u} G 2 :=
  Rep.ofHom ⟨(LinearMap.range (coindUnit U (zmodRep.{u} G 2)).hom.toLinearMap).liftQ
    (coindSumTwo U c) (by
      rintro _ ⟨a, rfl⟩
      exact coindSumTwo_coindUnit U a), fun σ => by
    apply LinearMap.ext
    intro y
    obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective _ y
    exact coindSumTwo_ρ U hc hU σ f⟩

theorem coindQuotientZModTwo_mk (f : Rep.coind U.subtype (Rep.res U.subtype (zmodRep.{u} G 2))) :
    (coindQuotientZModTwo U hc hU).hom
      (Submodule.mkQ (LinearMap.range (coindUnit U (zmodRep.{u} G 2)).hom.toLinearMap) f) =
      f.1 1 + f.1 c :=
  rfl

include hc hU in
theorem bijective_coindQuotientZModTwo :
    Function.Bijective (coindQuotientZModTwo U hc hU).hom := by
  classical
  refine ⟨(injective_iff_map_eq_zero _).2 fun y hy => ?_, fun a => ?_⟩
  · obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective _ y
    rw [coindQuotientZModTwo_mk] at hy
    have h1c : f.1 c = f.1 1 := by
      have hpq : (f.1 1).down + (f.1 c).down = 0 := congrArg ULift.down hy
      apply ULift.ext
      rw [eq_neg_of_add_eq_zero_right hpq]
      exact ZModModule.neg_eq_self _
    refine (Submodule.Quotient.mk_eq_zero _).2 ⟨f.1 1, Subtype.ext (funext fun x => ?_)⟩
    change f.1 1 = f.1 x
    by_cases hx : x ∈ U
    · have := coind_zmodRep_apply_mul U f hx 1
      rw [mul_one] at this
      exact this.symm
    · have := coind_zmodRep_apply_mul U f (hU x hx) c
      rw [inv_mul_cancel_right] at this
      rw [this, h1c]
  · let f : Rep.coind U.subtype (Rep.res U.subtype (zmodRep.{u} G 2)) :=
      ⟨fun x => if x ∈ U then 0 else a, fun u x => by
        have hux : (u : G) * x ∈ U ↔ x ∈ U :=
          ⟨fun h => by simpa using U.mul_mem (U.inv_mem u.2) h, fun h => U.mul_mem u.2 h⟩
        change (if (u : G) * x ∈ U then 0 else a) = if x ∈ U then 0 else a
        simp only [hux]⟩
    refine ⟨Submodule.mkQ _ f, ?_⟩
    rw [coindQuotientZModTwo_mk]
    change (if (1 : G) ∈ U then 0 else a) + (if c ∈ U then 0 else a) = a
    simp [U.one_mem, hc]

include hc hU in
/-- `Ind_U^G(ℤ/2)/(ℤ/2) ≅ ℤ/2` for a subgroup `U` of index `2` with `c ∉ U`. -/
def coindQuotientZModTwoIso : (coindUnitSequence U (zmodRep.{u} G 2)).X₃ ≅ zmodRep.{u} G 2 :=
  repIsoOfBijective (coindQuotientZModTwo U hc hU) (bijective_coindQuotientZModTwo U hc hU)

end IndexTwo

section Main

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K)))

/-- **`Hʳ(G_S, ℤ/2)` and the real places.** If `S` contains the places above `2`, the localization
`Hʳ(G_S, ℤ/2) → ∏_{w real} Hʳ(K_w, ℤ/2)` is bijective for every `r ≥ 3`. -/
theorem bijective_realLocalization_zmodRep_two
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), ((2 : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) {r : ℕ}
    (hr : 3 ≤ r) :
    Function.Bijective fun (x : cohomology (zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) 2) r)
      (w : {w : InfinitePlace K // w.IsReal}) =>
        realLocalization ι (zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) 2) w.1 r x := by
  have hM : ∀ m : zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) 2, 2 • m = 0 :=
    nsmul_zmodRep_eq_zero _ 2
  by_cases hK : IsTotallyComplex K
  · exact bijective_realLocalization_of_odd_or_isTotallyComplex S ι _ two_ne_zero hM h2
      (Or.inr hK) hr
  obtain ⟨w₀, hw₀⟩ : ∃ w : InfinitePlace K, w.IsReal := by
    by_contra h
    push Not at h
    exact hK ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.1 (h w)⟩
  obtain ⟨i, L, _, hL, hLc, hi, hiS, hLi⟩ := exists_isTotallyComplex_intermediateField (Ω := Ω) S h2
  have hc := realLocalizationHom_closureConj_not_mem S ι hi hiS w₀ hw₀ hL hLi
  have hU := mul_inv_realLocalizationHom_closureConj_mem S ι hi hiS w₀ hw₀ hL hLi
  induction r, hr using Nat.le_induction with
  | base =>
    exact bijective_realLocalization_of_iso ι (dualizingModuleTwoIso S h2).symm 3
      (bijective_realLocalization_dualizingModule_two ι S h2)
  | succ r hr ih =>
    refine bijective_realLocalization_succ S ι hi hiS hL hLi hLc two_ne_zero h2 _ hM hr ?_
    exact bijective_realLocalization_of_iso ι (coindQuotientZModTwoIso _ hc hU).symm r ih

end Main

end

end Langlands.GaloisCohomology
