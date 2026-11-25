import Langlands.Cohomology.Profinite.ClassFormation.Basic
import Langlands.Cohomology.Profinite.Corestriction
import Langlands.Cohomology.Profinite.Dimension.Basic
import Langlands.Cohomology.Profinite.Dimension.ProP

namespace Langlands.ProfiniteCohomology

open CategoryTheory

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

theorem isAddTorsion_coind (U : OpenSubgroup G) (B : Rep.{u} (ULift.{u} ℤ) (U : Subgroup G))
    [IsSmoothRep B] (hB : IsAddTorsion B) :
    IsAddTorsion (Rep.coind (U : Subgroup G).subtype B) := by
  classical
  intro f
  have hfin : (Set.range (f.1 : G → B)).Finite := (isLocallyConstant_coind U B f).range_finite
  let N := ∏ v ∈ hfin.toFinset, addOrderOf v
  have hN : 0 < N := Finset.prod_pos fun v _ => (hB v).addOrderOf_pos
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨N, hN, Subtype.ext (funext fun x => ?_)⟩
  show N • f.1 x = 0
  have hv : f.1 x ∈ hfin.toFinset := by simp
  exact addOrderOf_dvd_iff_nsmul_eq_zero.1 (Finset.dvd_prod_of_mem _ hv)

theorem cd_openSubgroup_le (p : ℕ) (U : OpenSubgroup G) : cd p (U : Subgroup G) ≤ cd p G := by
  rw [cd_le_iff]
  intro B _ hB q hq
  have h0 := primaryComponent_cohomology_eq_bot_of_cd_lt (Rep.coind (U : Subgroup G).subtype B)
    (isAddTorsion_coind U B hB) hq
  rw [primaryComponent_eq_bot_iff] at h0 ⊢
  rintro x ⟨k, hk⟩
  have hy : (shapiroIso U B q).inv.hom x = 0 := h0 _ ⟨k, by rw [← map_nsmul, hk, map_zero]⟩
  rw [← Iso.inv_hom_id_apply (shapiroIso U B q) x, hy, map_zero]

end Langlands.ProfiniteCohomology

namespace Langlands.ProfiniteCohomology

open CategoryTheory Topology

universe u

section Extension

variable {G : Type u} [Group G] {H V : Subgroup G} [hVn : V.Normal]

omit hVn in
theorem inv_mul_mem_trans {a b c : G} (h₁ : a⁻¹ * b ∈ V) (h₂ : b⁻¹ * c ∈ V) : a⁻¹ * c ∈ V := by
  have := V.mul_mem h₁ h₂
  rwa [mul_assoc, mul_inv_cancel_left] at this

omit hVn in
theorem inv_mul_mem_symm {a b : G} (h : a⁻¹ * b ∈ V) : b⁻¹ * a ∈ V := by
  have := V.inv_mem h
  rwa [mul_inv_rev, inv_inv] at this

theorem inv_mul_mem_mul {a b a' b' : G} (ha : a⁻¹ * a' ∈ V) (hb : b⁻¹ * b' ∈ V) :
    (a * b)⁻¹ * (a' * b') ∈ V := by
  have h1 : b⁻¹ * (a⁻¹ * a') * b ∈ V := by
    have := hVn.conj_mem _ ha b⁻¹
    simpa using this
  have := V.mul_mem h1 hb
  convert this using 1
  group

theorem inv_mul_mem_contractNth {n : ℕ} (j : Fin (n + 1)) {g g' : Fin (n + 1) → G}
    (h : ∀ i, (g i)⁻¹ * g' i ∈ V) (i : Fin n) :
    (Fin.contractNth j (· * ·) g i)⁻¹ * Fin.contractNth j (· * ·) g' i ∈ V := by
  simp only [Fin.contractNth]
  split_ifs
  · exact h _
  · exact inv_mul_mem_mul (h _) (h _)
  · exact h _

variable (H V) in
theorem exists_mem_inv_mul_mem {x : G} (hx : x ∈ H ⊔ V) : ∃ h ∈ H, h⁻¹ * x ∈ V := by
  obtain ⟨h, hh, v, hv, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hx
  exact ⟨h, hh, by rwa [inv_mul_cancel_left]⟩

variable (H V) in

noncomputable def supSection (x : ↥(H ⊔ V)) : ↥H :=
  ⟨(exists_mem_inv_mul_mem H V x.2).choose, (exists_mem_inv_mul_mem H V x.2).choose_spec.1⟩

variable (H V) in
theorem supSection_spec (x : ↥(H ⊔ V)) : ((supSection H V x : G))⁻¹ * x ∈ V :=
  (exists_mem_inv_mul_mem H V x.2).choose_spec.2

variable (V) in

def ConstOnCosets {X : Type*} {n : ℕ} (c : (Fin n → H) → X) : Prop :=
  ∀ x y : Fin n → H, (∀ i, ((x i : G))⁻¹ * (y i : G) ∈ V) → c x = c y

variable (V) in

noncomputable def supExtend {X : Type*} {n : ℕ} (c : (Fin n → H) → X) : (Fin n → ↥(H ⊔ V)) → X :=
  fun x => c fun i => supSection H V (x i)

theorem supExtend_eq {X : Type*} {n : ℕ} {c : (Fin n → H) → X} (hc : ConstOnCosets V c)
    (x : Fin n → ↥(H ⊔ V)) (y : Fin n → H) (hxy : ∀ i, ((y i : G))⁻¹ * (x i : G) ∈ V) :
    supExtend V c x = c y :=
  hc _ _ fun i => inv_mul_mem_trans (supSection_spec H V (x i)) (inv_mul_mem_symm (hxy i))

theorem supExtend_inclusion {X : Type*} {n : ℕ} {c : (Fin n → H) → X} (hc : ConstOnCosets V c)
    (y : Fin n → H) : supExtend V c (fun i => Subgroup.inclusion le_sup_left (y i)) = c y :=
  supExtend_eq hc _ y fun i => by simp

theorem isLocallyConstant_supExtend [TopologicalSpace G] [IsTopologicalGroup G]
    (hV : IsOpen (V : Set G)) {X : Type*} {n : ℕ} {c : (Fin n → H) → X} (hc : ConstOnCosets V c) :
    IsLocallyConstant (supExtend V c) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hev : ∀ i, ∀ᶠ x' in 𝓝 x, ((x i : G))⁻¹ * (x' i : G) ∈ V := fun i => by
    have hcont : Continuous fun x' : Fin n → ↥(H ⊔ V) => ((x i : G))⁻¹ * (x' i : G) :=
      continuous_const.mul (continuous_subtype_val.comp (continuous_apply i))
    exact hcont.continuousAt.preimage_mem_nhds (hV.mem_nhds (by simp))
  filter_upwards [Filter.eventually_all.2 hev] with x' hx'
  exact supExtend_eq hc x' _ fun i => inv_mul_mem_trans (supSection_spec H V (x i)) (hx' i)

theorem d_supExtend {k : Type u} [CommRing k] (M : Rep.{u} k G) {n : ℕ} {c : (Fin n → H) → M}
    (hc : ConstOnCosets V c) (hfix : ∀ v ∈ V, ∀ x, M.ρ v (c x) = c x) :
    (inhomogeneousCochains.d (Rep.res (H ⊔ V).subtype M) n).hom (supExtend V c) =
      supExtend V ((inhomogeneousCochains.d (Rep.res H.subtype M) n).hom c) := by
  funext x
  simp only [inhomogeneousCochains.d_hom_apply, supExtend]
  congr 1
  · change M.ρ (x 0 : G) _ = M.ρ (supSection H V (x 0) : G) _
    rw [show ((x 0 : G)) = (supSection H V (x 0) : G) * ((supSection H V (x 0) : G)⁻¹ * x 0) by
      group, map_mul, Module.End.mul_apply, hfix _ (supSection_spec H V (x 0))]
  · refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    apply hc
    intro i
    refine inv_mul_mem_trans (supSection_spec H V _) ?_
    have e1 := congrFun (Fin.comp_contractNth (· * ·) (· * ·) (f := Subtype.val)
      (fun _ _ => rfl) j x) i
    have e2 := congrFun (Fin.comp_contractNth (· * ·) (· * ·) (f := Subtype.val)
      (fun _ _ => rfl) j fun i => supSection H V (x i)) i
    simp only [Function.comp_apply] at e1 e2
    rw [e1, e2]
    exact inv_mul_mem_contractNth j (fun i => inv_mul_mem_symm (supSection_spec H V (x i))) i

end Extension

section Cohomology

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G] (M : Rep.{u} k G) [IsSmoothRep M]

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  [IsSmoothRep M] in
theorem constOnCosets_mono {H : Subgroup G} {V V' : Subgroup G} (h : V' ≤ V) {X : Type*} {n : ℕ}
    {c : (Fin n → H) → X} (hc : ConstOnCosets V c) : ConstOnCosets V' c :=
  fun x y hxy => hc x y fun i => h (hxy i)

theorem exists_openNormalSubgroup_constOnCosets {H : Subgroup G} (hH : IsClosed (H : Set G))
    {n : ℕ} {c : (Fin n → H) → M} (hc : IsLocallyConstant c) :
    ∃ V : OpenNormalSubgroup G, ConstOnCosets (V : Subgroup G) c ∧
      ∀ v ∈ (V : Subgroup G), ∀ x, M.ρ v (c x) = c x := by
  have : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  obtain ⟨W, hW⟩ := exists_openNormalSubgroup_fin_of_isLocallyConstant hc
  obtain ⟨V₂, hV₂⟩ := exists_subgroupOf_le W
  have hdisc := (isSmoothRep_iff_forall_exists_openNormalSubgroup M).1 inferInstance
  choose Um hUm using hdisc
  have : Finite (Set.range c) := hc.range_finite.to_subtype
  obtain ⟨V, hV⟩ := OpenNormalSubgroup.exists_le_of_finite
    (fun o : Option (Set.range c) => o.elim V₂ fun m => Um m.1)
  refine ⟨V, fun x y hxy => hW x y fun i => hV₂ ?_, fun v hv x => ?_⟩
  · rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hV none (hxy i)
  · exact (Representation.mem_invariants _ _).1 (hUm (c x)) ⟨v, hV (some ⟨c x, x, rfl⟩) hv⟩

theorem exists_resOfLE_eq {H : Subgroup G} (hH : IsClosed (H : Set G)) (q : ℕ)
    (x : cohomology (Rep.res H.subtype M) q) :
    ∃ (U : Subgroup G) (_ : IsOpen (U : Set G)) (hHU : H ≤ U)
      (y : cohomology (Rep.res U.subtype M) q), (resOfLE M hHU q).hom y = x := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((cochains (Rep.res H.subtype M)).homologyπ q)).1 inferInstance x
  let f : locallyConstantCochains (Rep.res H.subtype M) q :=
    ((cochains (Rep.res H.subtype M)).iCycles q).hom z
  have hflc : IsLocallyConstant f.1 := f.2
  have hdf : (inhomogeneousCochains.d (Rep.res H.subtype M) q).hom f.1 = 0 := by
    have := iCycles_d_apply (cochains (Rep.res H.subtype M)) q (q + 1) z
    rw [cochains_d] at this
    exact congrArg Subtype.val this
  obtain ⟨V, hVc, hVfix⟩ := exists_openNormalSubgroup_constOnCosets M hH hflc
  set U := H ⊔ (V : Subgroup G) with hUdef
  have hUo : IsOpen (U : Set G) := Subgroup.isOpen_mono le_sup_right V.isOpen'
  let F : locallyConstantCochains (Rep.res U.subtype M) q :=
    ⟨supExtend (V : Subgroup G) f.1, isLocallyConstant_supExtend V.isOpen' hVc⟩
  have hF : ((cochains (Rep.res U.subtype M)).d q
      ((ComplexShape.up ℕ).next q)).hom F = 0 := by
    rw [show (ComplexShape.up ℕ).next q = q + 1 by simp, cochains_d]
    apply Subtype.ext
    change (inhomogeneousCochains.d (Rep.res U.subtype M) q).hom
      (supExtend (H := H) (V : Subgroup G) f.1) = 0
    rw [d_supExtend M hVc hVfix, hdf]
    rfl
  obtain ⟨zF, hzF⟩ := exists_iCycles_eq (cochains (Rep.res U.subtype M)) F hF
  refine ⟨U, hUo, le_sup_left, ((cochains _).homologyπ q).hom zF, ?_⟩
  change (HomologicalComplex.homologyMap (cochainsMap (subgroupInclusionOfLE (le_sup_left : H ≤ U))
    (resResHom M _)) q).hom
      (((cochains _).homologyπ q).hom zF) = _
  rw [homologyMap_homologyπ_apply]
  congr 1
  apply (ModuleCat.mono_iff_injective ((cochains (Rep.res H.subtype M)).iCycles q)).1
    inferInstance
  rw [iCycles_cyclesMap_apply, hzF]
  apply Subtype.ext
  funext h
  exact supExtend_inclusion hVc h

theorem exists_res_eq_zero {H : Subgroup G} (hH : IsClosed (H : Set G)) (q : ℕ)
    (x : cohomology M (q + 1)) (hx : (res M H (q + 1)).hom x = 0) :
    ∃ (U : Subgroup G) (_ : IsOpen (U : Set G)) (_ : H ≤ U),
      (res M U (q + 1)).hom x = 0 := by
  obtain ⟨z, rfl⟩ :=
    (ModuleCat.epi_iff_surjective ((cochains M).homologyπ (q + 1))).1 inferInstance x
  let f : locallyConstantCochains M (q + 1) := ((cochains M).iCycles (q + 1)).hom z
  have hx' : ((cochains (Rep.res H.subtype M)).homologyπ (q + 1)).hom
      ((HomologicalComplex.cyclesMap (cochainsMap (subgroupInclusion H)
        (𝟙 _)) (q + 1)).hom z) = 0 := by
    rw [← homologyMap_homologyπ_apply]
    exact hx
  obtain ⟨w, hw⟩ := (homologyπ_eq_zero_iff _ _).1 hx'
  rw [iCycles_cyclesMap_apply] at hw
  generalize hj : (ComplexShape.up ℕ).prev (q + 1) = j at w hw
  have hjq : j = q := by
    rw [← hj]
    simp
  subst hjq
  have hwlc : IsLocallyConstant (w : locallyConstantCochains (Rep.res H.subtype M) j).1 := w.2
  obtain ⟨V₁, hV₁c, hV₁fix⟩ := exists_openNormalSubgroup_constOnCosets M hH hwlc
  obtain ⟨V₂, hV₂⟩ := exists_openNormalSubgroup_fin_of_isLocallyConstant f.2
  obtain ⟨V, hV⟩ := OpenNormalSubgroup.exists_le_of_finite (fun b : Bool => if b then V₁ else V₂)
  set c := (w : locallyConstantCochains (Rep.res H.subtype M) j).1 with hcdef
  have hVc : ConstOnCosets (V : Subgroup G) c := constOnCosets_mono (hV true) hV₁c
  have hVfix : ∀ v ∈ (V : Subgroup G), ∀ x, M.ρ v (c x) = c x :=
    fun v hv => hV₁fix v (hV true hv)
  set U := H ⊔ (V : Subgroup G) with hUdef
  let w' : locallyConstantCochains (Rep.res U.subtype M) j :=
    ⟨supExtend (V : Subgroup G) c, isLocallyConstant_supExtend V.isOpen' hVc⟩
  refine ⟨U, Subgroup.isOpen_mono le_sup_right V.isOpen', le_sup_left, ?_⟩
  change (HomologicalComplex.homologyMap (cochainsMap (subgroupInclusion U)
    (𝟙 (Rep.res U.subtype M))) (j + 1)).hom (((cochains M).homologyπ (j + 1)).hom z) = 0
  rw [homologyMap_homologyπ_apply]
  have hcyc : (HomologicalComplex.cyclesMap (cochainsMap (subgroupInclusion U) (𝟙 (Rep.res U.subtype M))) (j + 1)).hom z =
      ((cochains _).toCycles j (j + 1)).hom w' := by
    apply (ModuleCat.mono_iff_injective ((cochains _).iCycles (j + 1))).1 inferInstance
    rw [iCycles_cyclesMap_apply]
    rw [show ((cochains (Rep.res U.subtype M)).iCycles (j + 1)).hom
      (((cochains _).toCycles j (j + 1)).hom w') =
        ((cochains _).d j (j + 1)).hom w' from
      congrArg (fun φ => ModuleCat.Hom.hom φ w') ((cochains _).toCycles_i j (j + 1))]
    rw [cochains_d]
    apply Subtype.ext
    change _ = (inhomogeneousCochains.d (Rep.res U.subtype M) j).hom
      (supExtend (H := H) (V : Subgroup G) c)
    rw [d_supExtend M hVc hVfix]
    have hw' : (inhomogeneousCochains.d (Rep.res H.subtype M) j).hom c =
        fun h => f.1 fun i => (h i : G) := by
      rw [cochains_d] at hw
      exact congrArg Subtype.val hw
    rw [hw']
    funext u
    change f.1 (fun i => (u i : G)) = f.1 fun i => (supSection H (V : Subgroup G) (u i) : G)
    exact hV₂ _ _ fun i => hV false (inv_mul_mem_symm (supSection_spec H (V : Subgroup G) (u i)))
  rw [hcyc]
  exact congrArg (fun φ => ModuleCat.Hom.hom φ w')
    ((cochains _).toCycles_comp_homologyπ j (j + 1))

end Cohomology

end Langlands.ProfiniteCohomology

namespace Langlands.ProfiniteCohomology

open CategoryTheory

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

theorem cd_le_cd_closedSubgroup {p : ℕ} (hp : p.Prime) {H : Subgroup G}
    (hH : IsClosed (H : Set G)) (hdvd : ¬ Supernatural.ofNat p ∣ superIndex H) :
    cd p G ≤ cd p H := by
  rw [cd_le_iff]
  intro A _ hA q hq
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := by
    cases q with
    | zero => simp at hq
    | succ q => exact ⟨q, rfl⟩
  have h0 := primaryComponent_cohomology_eq_bot_of_cd_lt (Rep.res H.subtype A) hA hq
  rw [primaryComponent_eq_bot_iff] at h0 ⊢
  rintro x ⟨k, hk⟩
  have h1 : (res A H (q' + 1)).hom x = 0 :=
    h0 _ ⟨k, by rw [← map_nsmul, hk, map_zero]⟩
  obtain ⟨U, hUo, hHU, hU⟩ := exists_res_eq_zero A hH q' x h1
  let U' : OpenSubgroup G := ⟨U, hUo⟩
  have : Finite (G ⧸ U) := Subgroup.quotient_finite_of_isOpen U hUo
  have hUne : U.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hndvd : ¬ p ∣ U.index := by
    intro hpU
    apply hdvd
    have h2 : superIndex U ∣ superIndex H := superIndex_dvd_of_le hHU
    rw [superIndex_of_isOpen hUo] at h2
    exact ((Supernatural.ofNat_dvd_ofNat hp.ne_zero hUne).2 hpU).trans h2
  have hU' : (res A (U' : Subgroup G) (q' + 1)).hom x = 0 := hU
  have h2 : U.index • x = 0 := by
    have := congrArg (fun φ => φ.hom x) (res_comp_cores U' A (q' + 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, hU', map_zero] at this
    exact this.symm
  have hcop : Nat.Coprime (p ^ k) U.index :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hndvd)
  have h3 : addOrderOf x ∣ Nat.gcd (p ^ k) U.index :=
    Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero hk) (addOrderOf_dvd_of_nsmul_eq_zero h2)
  rw [hcop.gcd_eq_one, Nat.dvd_one] at h3
  exact AddMonoid.addOrderOf_eq_one_iff.1 h3

section Summand

omit [TotallyDisconnectedSpace G] in

theorem finite_of_isSimpleOrder {p : ℕ} (hp : p.Prime) (A : Rep.{u} (ULift.{u} ℤ) G)
    [IsSmoothRep A] (hsimple : IsSimpleOrder (Subrepresentation A.ρ))
    (hA : ∀ a : A, p • a = 0) : Finite A := by
  by_cases hnt : Nontrivial A
  · obtain ⟨a₀, ha₀⟩ := exists_ne (0 : A)
    obtain ⟨W, hW, hWfin, haW⟩ := exists_finite_stable_submodule A hp.pos
      (fun a => ⟨1, by rw [pow_one]; exact hA a⟩) a₀
    let W' : Subrepresentation A.ρ := ⟨W, fun g v hv => hW g hv⟩
    rcases hsimple.eq_bot_or_eq_top W' with h | h
    · exfalso
      have : a₀ ∈ W'.toSubmodule := haW
      rw [h] at this
      exact ha₀ ((Submodule.mem_bot _).1 this)
    · have hall : ∀ a : A, a ∈ W := fun a => by
        have : a ∈ (⊤ : Subrepresentation A.ρ).toSubmodule := Submodule.mem_top
        rw [← h] at this
        exact this
      exact Finite.of_injective (fun x : A => (⟨x, hall x⟩ : W)) fun x y h => congrArg Subtype.val h
  · rw [not_nontrivial_iff_subsingleton] at hnt
    infer_instance

end Summand

section Coinduction

variable {k : Type u} [CommRing k] (H V : Subgroup G) [hVn : V.Normal] (A : Rep.{u} k H)

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in

noncomputable def coindFixed : Submodule k (Rep.coind H.subtype A) :=
  Representation.invariants ((Rep.coind H.subtype A).ρ.comp V.subtype)

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
theorem coindFixed_le_comap (g : G) :
    coindFixed H V A ≤ (coindFixed H V A).comap ((Rep.coind H.subtype A).ρ g) := by
  intro f hf v
  have hv : g⁻¹ * (v : G) * g ∈ V := by
    have := hVn.conj_mem _ v.2 g⁻¹
    simpa using this
  have h1 : (Rep.coind H.subtype A).ρ (v : G) ((Rep.coind H.subtype A).ρ g f) =
      (Rep.coind H.subtype A).ρ g ((Rep.coind H.subtype A).ρ (g⁻¹ * (v : G) * g) f) := by
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group
  change (Rep.coind H.subtype A).ρ (v : G) ((Rep.coind H.subtype A).ρ g f) =
    (Rep.coind H.subtype A).ρ g f
  rw [h1]
  congr 1
  exact hf ⟨_, hv⟩

noncomputable abbrev coindFixedRep : Rep.{u} k G :=
  (Rep.coind H.subtype A).subrepresentation (coindFixed H V A) (coindFixed_le_comap H V A)

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
theorem isSmoothRep_coindFixedRep (hV : IsOpen (V : Set G)) :
    IsSmoothRep (coindFixedRep H V A) :=
  IsSmoothRep.of_isOpen_stabilizer _ fun m => Subgroup.isOpen_mono (fun v hv => Subtype.ext (m.2 ⟨v, hv⟩)) hV

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] hVn in

noncomputable def coindFixedEval : Rep.res H.subtype (coindFixedRep H V A) ⟶ A :=
  Rep.ofHom ⟨{ toFun := fun m => m.1.1 1
               map_add' := fun _ _ => rfl
               map_smul' := fun _ _ => rfl },
    fun h => by
      ext m
      change m.1.1 (1 * (h : G)) = A.ρ h (m.1.1 1)
      rw [one_mul]
      simpa using m.1.2 h 1⟩

variable {H V A}

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  hVn in
theorem rho_eq_of_inv_mul_mem (hfix : ∀ h : H, (h : G) ∈ V → ∀ a : A, A.ρ h a = a) {h₁ h₂ : H}
    (h : (h₁ : G)⁻¹ * h₂ ∈ V) (a : A) : A.ρ h₁ a = A.ρ h₂ a := by
  have e : h₂ = h₁ * (h₁⁻¹ * h₂) := by group
  rw [e, map_mul, Module.End.mul_apply, hfix (h₁⁻¹ * h₂) (by simpa using h)]

variable (H V) in
omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  hVn in
open scoped Classical in

noncomputable def summandFun (a : A) (x : G) : A :=
  if hx : x ∈ H ⊔ V then A.ρ (supSection H V ⟨x, hx⟩) a else 0

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
theorem summandFun_mul_left (hfix : ∀ h : H, (h : G) ∈ V → ∀ a : A, A.ρ h a = a) (a : A)
    (h : H) (x : G) : summandFun H V a ((h : G) * x) = A.ρ h (summandFun H V a x) := by
  have hmem : (h : G) * x ∈ H ⊔ V ↔ x ∈ H ⊔ V :=
    Subgroup.mul_mem_cancel_left _ (le_sup_left (a := H) (b := V) h.2)
  by_cases hx : x ∈ H ⊔ V
  · have hx' : (h : G) * x ∈ H ⊔ V := hmem.2 hx
    simp only [summandFun, dite_eq_left hx, dite_eq_left hx']
    rw [← Module.End.mul_apply, ← map_mul]
    apply rho_eq_of_inv_mul_mem hfix
    refine inv_mul_mem_trans (supSection_spec H V ⟨_, hx'⟩) ?_
    have := inv_mul_mem_symm (supSection_spec H V ⟨x, hx⟩)
    simpa [mul_assoc] using this
  · have hx' : (h : G) * x ∉ H ⊔ V := fun h' => hx (hmem.1 h')
    simp only [summandFun, dite_eq_right hx, dite_eq_right hx', map_zero]

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
theorem summandFun_mul_right (hfix : ∀ h : H, (h : G) ∈ V → ∀ a : A, A.ρ h a = a) (a : A)
    (k' : H) (x : G) : summandFun H V a (x * k') = summandFun H V (A.ρ k' a) x := by
  have hmem : x * k' ∈ H ⊔ V ↔ x ∈ H ⊔ V :=
    Subgroup.mul_mem_cancel_right _ (le_sup_left (a := H) (b := V) k'.2)
  by_cases hx : x ∈ H ⊔ V
  · have hx' : x * k' ∈ H ⊔ V := hmem.2 hx
    simp only [summandFun, dite_eq_left hx, dite_eq_left hx']
    rw [← Module.End.mul_apply, ← map_mul]
    apply rho_eq_of_inv_mul_mem hfix
    refine inv_mul_mem_trans (supSection_spec H V ⟨_, hx'⟩) ?_
    have h1 := inv_mul_mem_symm (supSection_spec H V ⟨x, hx⟩)
    have h2 : (k' : G)⁻¹ * (x⁻¹ * (supSection H V ⟨x, hx⟩ : G)) * k' ∈ V := by
      have := hVn.conj_mem _ h1 (k' : G)⁻¹
      simpa using this
    simpa [mul_assoc] using h2
  · have hx' : x * k' ∉ H ⊔ V := fun h' => hx (hmem.1 h')
    simp only [summandFun, dite_eq_right hx, dite_eq_right hx']

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
theorem summandFun_mul_right_of_mem (hfix : ∀ h : H, (h : G) ∈ V → ∀ a : A, A.ρ h a = a)
    (a : A) (v : G) (hv : v ∈ V) (x : G) : summandFun H V a (x * v) = summandFun H V a x := by
  have hmem : x * v ∈ H ⊔ V ↔ x ∈ H ⊔ V :=
    Subgroup.mul_mem_cancel_right _ (le_sup_right (a := H) (b := V) hv)
  by_cases hx : x ∈ H ⊔ V
  · have hx' : x * v ∈ H ⊔ V := hmem.2 hx
    simp only [summandFun, dite_eq_left hx, dite_eq_left hx']
    apply rho_eq_of_inv_mul_mem hfix
    refine inv_mul_mem_trans (supSection_spec H V ⟨_, hx'⟩) ?_
    have h1 := inv_mul_mem_symm (supSection_spec H V ⟨x, hx⟩)
    have h2 : v⁻¹ * (x⁻¹ * (supSection H V ⟨x, hx⟩ : G)) ∈ V := V.mul_mem (V.inv_mem hv) h1
    simpa [mul_assoc] using h2
  · have hx' : x * v ∉ H ⊔ V := fun h' => hx (hmem.1 h')
    simp only [summandFun, dite_eq_right hx, dite_eq_right hx']

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
theorem summandFun_one (hfix : ∀ h : H, (h : G) ∈ V → ∀ a : A, A.ρ h a = a) (a : A) :
    summandFun H V a 1 = a := by
  have h1 : (1 : G) ∈ H ⊔ V := one_mem _
  simp only [summandFun, dite_eq_left h1]
  rw [← rho_eq_of_inv_mul_mem hfix (h₁ := 1) ?_ a, map_one, Module.End.one_apply]
  have := V.inv_mem (supSection_spec H V ⟨1, h1⟩)
  simpa using this

end Coinduction

section Splitting

variable {k : Type u} [CommRing k] {H V : Subgroup G} [hVn : V.Normal] {A : Rep.{u} k H}

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
theorem summandFun_add (a b : A) (x : G) :
    summandFun H V (a + b) x = summandFun H V a x + summandFun H V b x := by
  simp only [summandFun]
  split_ifs <;> simp [map_add]

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
theorem summandFun_smul (r : k) (a : A) (x : G) :
    summandFun H V (r • a) x = r • summandFun H V a x := by
  simp only [summandFun]
  split_ifs <;> simp [map_smul]

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in

noncomputable def summandMap (hfix : ∀ h : H, (h : G) ∈ V → ∀ a : A, A.ρ h a = a) :
    A ⟶ Rep.res H.subtype (coindFixedRep H V A) :=
  Rep.ofHom ⟨{ toFun := fun a => ⟨⟨summandFun H V a, fun h x => summandFun_mul_left hfix a h x⟩,
                  fun v => Subtype.ext (funext fun x => summandFun_mul_right_of_mem hfix a v v.2 x)⟩
               map_add' := fun a b => Subtype.ext (Subtype.ext (funext fun x => summandFun_add a b x))
               map_smul' := fun r a =>
                 Subtype.ext (Subtype.ext (funext fun x => summandFun_smul r a x)) },
    fun h => LinearMap.ext fun a => Subtype.ext (Subtype.ext (funext fun x =>
      (summandFun_mul_right hfix a h x).symm))⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in

theorem summandMap_comp_coindFixedEval (hfix : ∀ h : H, (h : G) ∈ V → ∀ a : A, A.ρ h a = a) :
    summandMap hfix ≫ coindFixedEval H V A = 𝟙 A := by
  ext a
  exact summandFun_one hfix a

end Splitting

section Main

theorem cd_closedSubgroup_le {p : ℕ} (hp : p.Prime) {H : Subgroup G} (hH : IsClosed (H : Set G)) :
    cd p H ≤ cd p G := by
  by_cases htop : cd p G = ⊤
  · rw [htop]
    exact le_top
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 htop
  have hcd : cd p G ≤ n := hn ▸ le_rfl
  rw [← hn]
  have : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  rw [cd_le_iff_forall_simple hp]
  intro A _ hsimple hA
  have hfin : Finite A := finite_of_isSimpleOrder hp A hsimple hA

  have hdisc := (isSmoothRep_iff_forall_exists_openNormalSubgroup A).1 inferInstance
  choose W hW using hdisc
  obtain ⟨W₀, hW₀⟩ := OpenNormalSubgroup.exists_le_of_finite W
  obtain ⟨V, hV⟩ := exists_subgroupOf_le W₀
  have hfix : ∀ h : H, (h : G) ∈ (V : Subgroup G) → ∀ a : A, A.ρ h a = a := by
    intro h hh a
    have hh' : h ∈ (W a : Subgroup H) := hW₀ a (hV (Subgroup.mem_subgroupOf.2 hh))
    exact (Representation.mem_invariants _ _).1 (hW a) ⟨h, hh'⟩

  have hM : IsSmoothRep (coindFixedRep H (V : Subgroup G) A) :=
    isSmoothRep_coindFixedRep H (V : Subgroup G) A V.isOpen'
  have hMH : IsSmoothRep (Rep.res H.subtype (coindFixedRep H (V : Subgroup G) A)) :=
    isSmoothRep_res_subtype _ H
  have hMp : ∀ m : coindFixedRep H (V : Subgroup G) A, p • m = 0 := fun m =>
    Subtype.ext (Subtype.ext (funext fun x => hA (m.1.1 x)))

  have hvan : Subsingleton (cohomology (Rep.res H.subtype (coindFixedRep H (V : Subgroup G) A))
      (n + 1)) := by
    refine ⟨fun y₁ y₂ => ?_⟩
    suffices h0 : ∀ y : cohomology (Rep.res H.subtype (coindFixedRep H (V : Subgroup G) A)) (n + 1),
        y = 0 by rw [h0 y₁, h0 y₂]
    intro y
    obtain ⟨U, hUo, hHU, y', rfl⟩ := exists_resOfLE_eq _ hH (n + 1) y
    have hU : cd p U ≤ n := (cd_openSubgroup_le p ⟨U, hUo⟩).trans hcd
    have : IsSmoothRep (Rep.res U.subtype (coindFixedRep H (V : Subgroup G) A)) :=
      isSmoothRep_res_subtype _ U
    have hs := subsingleton_cohomology_of_cd_le hp hU
      (Rep.res U.subtype (coindFixedRep H (V : Subgroup G) A)) (fun m => hMp m) (Nat.lt_succ_self n)
    rw [Subsingleton.elim y' 0, map_zero]

  refine ⟨fun x₁ x₂ => ?_⟩
  have key : ∀ x : cohomology A (n + 1), x =
      (coeffMap (coindFixedEval H (V : Subgroup G) A) (n + 1)).hom
        ((coeffMap (summandMap hfix) (n + 1)).hom x) := by
    intro x
    change x = (coeffMap (summandMap hfix) (n + 1) ≫
      coeffMap (coindFixedEval H (V : Subgroup G) A) (n + 1)).hom x
    rw [← coeffMap_comp, summandMap_comp_coindFixedEval, coeffMap_id]
    rfl
  rw [key x₁, key x₂, Subsingleton.elim ((coeffMap (summandMap hfix) (n + 1)).hom x₁)]

end Main

theorem cd_closedSubgroup_eq {p : ℕ} (hp : p.Prime) {H : Subgroup G} (hH : IsClosed (H : Set G))
    (hdvd : ¬ Supernatural.ofNat p ∣ superIndex H) : cd p H = cd p G :=
  le_antisymm (cd_closedSubgroup_le hp hH) (cd_le_cd_closedSubgroup hp hH hdvd)

theorem cd_eq_of_isProSylow {p : ℕ} (hp : p.Prime) {P : Subgroup G} (hP : IsProSylow p P) :
    cd p P = cd p G :=
  cd_closedSubgroup_eq hp hP.1 hP.2.2

end Langlands.ProfiniteCohomology
