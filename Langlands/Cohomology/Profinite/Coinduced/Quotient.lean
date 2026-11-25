import Langlands.Cohomology.Profinite.Coinduced.Acyclic
import Langlands.Cohomology.Profinite.OpenNormal
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Separation.CompletelyRegular

namespace Langlands.ProfiniteCohomology

open Topology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def cosetSelectors (N : Subgroup G) : Set (Set G) :=
  {T | IsClosed T ∧ ∃ K : Subgroup G, K.Normal ∧ IsClosed (K : Set G) ∧ K ≤ N ∧
    (∀ t ∈ T, ∀ k ∈ K, t * k ∈ T) ∧ (∀ x : G, ∃ t ∈ T, (t : G ⧸ N) = x) ∧
    (∀ t ∈ T, ∀ t' ∈ T, (t : G ⧸ N) = t' → t⁻¹ * t' ∈ K)}

omit [IsTopologicalGroup G] in
theorem univ_mem_cosetSelectors (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    Set.univ ∈ cosetSelectors N :=
  ⟨isClosed_univ, N, inferInstance, hN, le_rfl, fun _ _ _ _ => Set.mem_univ _,
    fun x => ⟨x, Set.mem_univ _, rfl⟩, fun _ _ _ _ h => QuotientGroup.eq.mp h⟩

variable [CompactSpace G]

theorem sInter_mem_cosetSelectors (N : Subgroup G) (hN : IsClosed (N : Set G))
    {c : Set (Set G)} (hcS : c ⊆ cosetSelectors N) (hc : IsChain (· ⊆ ·) c) (hne : c.Nonempty) :
    ⋂₀ c ∈ cosetSelectors N := by
  have : Nonempty c := hne.to_subtype
  choose K hKn hKc hKN hKmul hKex hKuniq using fun T : c => (hcS T.2).2
  refine ⟨isClosed_sInter fun T hT => (hcS hT).1, ⨅ T : c, K T, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨fun n hn g => Subgroup.mem_iInf.2 fun T =>
      (hKn T).conj_mem _ (Subgroup.mem_iInf.1 hn T) g⟩
  · rw [Subgroup.coe_iInf]
    exact isClosed_iInter hKc
  · exact (iInf_le _ (Classical.arbitrary c)).trans (hKN _)
  · intro t ht k hk
    exact Set.mem_sInter.2 fun T hT =>
      hKmul ⟨T, hT⟩ t (Set.mem_sInter.1 ht T hT) k (Subgroup.mem_iInf.1 hk ⟨T, hT⟩)
  · intro x
    have : IsClosed (N : Set G) := hN
    have : T2Space (G ⧸ N) := inferInstance
    have hne' : (⋂ T : c, ((T : Set G) ∩ {t | (t : G ⧸ N) = x})).Nonempty := by
      refine IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _ ?_ ?_ ?_ ?_
      · intro T T'
        rcases hc.total T.2 T'.2 with h | h
        · exact ⟨T, le_rfl, Set.inter_subset_inter_left _ h⟩
        · exact ⟨T', Set.inter_subset_inter_left _ h, le_rfl⟩
      · intro T
        obtain ⟨t, ht, htx⟩ := hKex T x
        exact ⟨t, ht, htx⟩
      · intro T
        exact ((hcS T.2).1.inter (isClosed_eq QuotientGroup.continuous_mk continuous_const)).isCompact
      · intro T
        exact (hcS T.2).1.inter (isClosed_eq QuotientGroup.continuous_mk continuous_const)
    obtain ⟨t, ht⟩ := hne'
    rw [Set.mem_iInter] at ht
    refine ⟨t, Set.mem_sInter.2 fun T hT => (ht ⟨T, hT⟩).1, ?_⟩
    exact (ht (Classical.arbitrary c)).2
  · intro t ht t' ht' h
    exact Subgroup.mem_iInf.2 fun T =>
      hKuniq T t (Set.mem_sInter.1 ht T T.2) t' (Set.mem_sInter.1 ht' T T.2) h

variable [TotallyDisconnectedSpace G]

theorem exists_closed_transversal (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    ∃ T : Set G, IsClosed T ∧ (∀ x : G, ∃ t ∈ T, (t : G ⧸ N) = x) ∧
      ∀ t ∈ T, ∀ t' ∈ T, (t : G ⧸ N) = t' → t = t' := by
  obtain ⟨T, hTmin⟩ := zorn_superset (cosetSelectors N) fun c hcS hc => by
    rcases c.eq_empty_or_nonempty with rfl | hne
    · exact ⟨Set.univ, univ_mem_cosetSelectors N hN, fun s hs => absurd hs (Set.notMem_empty s)⟩
    · exact ⟨⋂₀ c, sInter_mem_cosetSelectors N hN hcS hc hne, fun s hs => Set.sInter_subset_of_mem hs⟩
  obtain ⟨hTc, K, hKn, hKc, hKN, hKmul, hKex, hKuniq⟩ := hTmin.prop
  suffices hK : ∀ x ∈ K, x = 1 by
    refine ⟨T, hTc, hKex, fun t ht t' ht' h => ?_⟩
    have := hK _ (hKuniq t ht t' ht' h)
    rw [inv_mul_eq_one] at this
    exact this
  intro x hxK
  by_contra hx1

  have hxnhds : ({x}ᶜ : Set G) ∈ 𝓝 (1 : G) :=
    isOpen_compl_singleton.mem_nhds (Ne.symm hx1)
  obtain ⟨U, -, hU⟩ := (OpenNormalSubgroup.hasBasis_nhds_one (G := G)).mem_iff.mp hxnhds
  have hxU : x ∉ (U : Subgroup G) := fun h => hU h rfl
  let W : Subgroup G := K ⊔ (U : Subgroup G)
  have hWopen : IsOpen (W : Set G) :=
    Subgroup.isOpen_mono le_sup_right U.toOpenSubgroup.isOpen
  have : W.Normal := Subgroup.sup_normal K (U : Subgroup G)
  have : DiscreteTopology (G ⧸ W) := QuotientGroup.discreteTopology hWopen
  let r : G ⧸ W → G ⧸ (U : Subgroup G) := fun D => ((Quotient.out D : G) : G ⧸ (U : Subgroup G))
  let T' : Set G := T ∩ {g | (g : G ⧸ (U : Subgroup G)) = r (g : G ⧸ W)}
  have hT'c : IsClosed T' :=
    hTc.inter (isClosed_eq QuotientGroup.continuous_mk
      ((continuous_of_discreteTopology (f := r)).comp QuotientGroup.continuous_mk))
  have hK'n : (K ⊓ (U : Subgroup G)).Normal := Subgroup.normal_inf_normal _ _
  have hT'mem : T' ∈ cosetSelectors N := by
    refine ⟨hT'c, K ⊓ (U : Subgroup G), hK'n,
      hKc.inter U.toOpenSubgroup.isClosed, inf_le_left.trans hKN, ?_, ?_, ?_⟩
    · rintro t ⟨ht, htr⟩ k ⟨hkK, hkU⟩
      refine ⟨hKmul t ht k hkK, ?_⟩
      have h1 : ((t * k : G) : G ⧸ (U : Subgroup G)) = (t : G ⧸ (U : Subgroup G)) :=
        QuotientGroup.eq.mpr (by simpa using (U : Subgroup G).inv_mem hkU)
      have h2 : ((t * k : G) : G ⧸ W) = (t : G ⧸ W) :=
        QuotientGroup.eq.mpr (by simpa using W.inv_mem (le_sup_left (b := (U : Subgroup G)) hkK))
      simp only [Set.mem_ofPred_eq] at htr ⊢
      rw [h1, h2]
      exact htr
    · intro y
      obtain ⟨t, ht, hty⟩ := hKex y
      obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul W t
      obtain ⟨k, hk, u, hu, hku⟩ := Subgroup.mem_sup_of_normal_right.mp w.2
      refine ⟨t * k, ⟨hKmul t ht k hk, ?_⟩, ?_⟩
      · simp only [Set.mem_ofPred_eq, r]
        have h2 : ((t * k : G) : G ⧸ W) = (t : G ⧸ W) :=
          QuotientGroup.eq.mpr (by simpa using W.inv_mem (le_sup_left (b := (U : Subgroup G)) hk))
        rw [h2, hw, ← hku, ← mul_assoc]
        exact QuotientGroup.eq.mpr (by convert hu using 1; group)
      · rw [← hty]
        exact QuotientGroup.eq.mpr (by simpa using hKN hk)
    · rintro t ⟨ht, htr⟩ t' ⟨ht', ht'r⟩ h
      have hK1 := hKuniq t ht t' ht' h
      refine ⟨hK1, ?_⟩
      have hW : (t : G ⧸ W) = t' := QuotientGroup.eq.mpr (le_sup_left (b := (U : Subgroup G)) hK1)
      simp only [Set.mem_ofPred_eq] at htr ht'r
      have : (t : G ⧸ (U : Subgroup G)) = t' := by rw [htr, ht'r, hW]
      exact QuotientGroup.eq.mp this
  have hTT' : T ⊆ T' := hTmin.2 hT'mem Set.inter_subset_left
  obtain ⟨t, ht, -⟩ := hKex 1
  have htx : t * x ∈ T := hKmul t ht x hxK

  obtain ⟨t₀, ⟨ht₀, ht₀r⟩, -⟩ := (⟨t, hTT' ht, rfl⟩ : ∃ t₀ ∈ T', t₀ = t)
  have hsame : (t : G ⧸ N) = (t * x : G) := QuotientGroup.eq.mpr (by simpa using hKN hxK)
  have hmem := (hT'mem.2.choose_spec)

  have h1 := (hTT' ht).2
  have h2 := (hTT' htx).2
  have hW : (t : G ⧸ W) = (t * x : G) :=
    QuotientGroup.eq.mpr (by simpa using le_sup_left (b := (U : Subgroup G)) hxK)
  simp only [Set.mem_ofPred_eq] at h1 h2
  have : (t : G ⧸ (U : Subgroup G)) = (t * x : G) := by rw [h1, h2, hW]
  exact hxU (by simpa using QuotientGroup.eq.mp this)

theorem exists_continuous_section (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    ∃ s : G ⧸ N → G, Continuous s ∧ (∀ c, (s c : G ⧸ N) = c) ∧ s 1 = 1 := by
  have : IsClosed (N : Set G) := hN
  have : T2Space (G ⧸ N) := inferInstance
  obtain ⟨T, hTc, hex, huniq⟩ := exists_closed_transversal N hN
  have : CompactSpace T := isCompact_iff_compactSpace.mp hTc.isCompact
  let f : T → G ⧸ N := fun t => (t : G)
  have hf : Function.Bijective f := by
    refine ⟨fun t t' h => Subtype.ext (huniq t t.2 t' t'.2 h), fun c => ?_⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
    obtain ⟨t, ht, htx⟩ := hex x
    exact ⟨⟨t, ht⟩, htx⟩
  let e : T ≃ₜ G ⧸ N := (QuotientGroup.continuous_mk.comp continuous_subtype_val :
    Continuous f).homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hf)
  let s₀ : G ⧸ N → G := fun c => (e.symm c : G)
  have hs₀ : ∀ c, (s₀ c : G ⧸ N) = c := fun c => e.apply_symm_apply c
  have h1 : s₀ 1 ∈ N := by
    have := hs₀ 1
    rw [← QuotientGroup.mk_one, QuotientGroup.eq] at this
    simpa using this
  refine ⟨fun c => s₀ c * (s₀ 1)⁻¹,
    (continuous_subtype_val.comp e.symm.continuous).mul continuous_const, fun c => ?_, ?_⟩
  · calc ((s₀ c * (s₀ 1)⁻¹ : G) : G ⧸ N) = (s₀ c : G ⧸ N) :=
          QuotientGroup.eq.mpr (by convert h1 using 1; group)
      _ = c := hs₀ c
  · exact mul_inv_cancel _

end Langlands.ProfiniteCohomology

namespace Langlands.ProfiniteCohomology

open CategoryTheory Filter Topology

universe u

section Iso

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

noncomputable def cohomologyIsoOfIso {A B : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B]
    (e : A ≅ B) (n : ℕ) : cohomology A n ≅ cohomology B n where
  hom := map (.id G) e.hom n
  inv := map (.id G) e.inv n
  hom_inv_id := by rw [← map_id_comp, e.hom_inv_id, map_id]
  inv_hom_id := by rw [← map_id_comp, e.inv_hom_id, map_id]

end Iso

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] (X : Type u) [AddCommGroup X] [Module k X]

section Restriction

variable (N : Subgroup G) [N.Normal] {s : G ⧸ N → G} (hs : Continuous s)
  (hsec : ∀ c, (s c : G ⧸ N) = c)

include hsec in

theorem inv_section_mul_mem (x : G) : (s (x : G ⧸ N))⁻¹ * x ∈ N :=
  QuotientGroup.eq.mp (hsec x)

def sectionRetraction (x : G) : N :=
  ⟨(s (x : G ⧸ N))⁻¹ * x, inv_section_mul_mem N hsec x⟩

theorem coe_sectionRetraction (x : G) :
    (sectionRetraction N hsec x : G) = (s (x : G ⧸ N))⁻¹ * x :=
  rfl

include hs in
theorem continuous_sectionRetraction : Continuous (sectionRetraction N hsec) :=
  Continuous.subtype_mk ((hs.comp QuotientGroup.continuous_mk).inv.mul continuous_id) _

theorem section_mul_sectionRetraction (x : G) :
    s (x : G ⧸ N) * (sectionRetraction N hsec x : G) = x := by
  rw [coe_sectionRetraction, mul_inv_cancel_left]

include hsec in
theorem mk_section_mul (c : G ⧸ N) (m : N) : ((s c * m : G) : G ⧸ N) = c :=
  (QuotientGroup.eq.mpr (by rw [mul_inv_rev, inv_mul_cancel_right]; exact N.inv_mem m.2) :
    ((s c * m : G) : G ⧸ N) = (s c : G ⧸ N)).trans (hsec c)

theorem sectionRetraction_section_mul (c : G ⧸ N) (m : N) :
    sectionRetraction N hsec (s c * m) = m := by
  apply Subtype.ext
  rw [coe_sectionRetraction, mk_section_mul N hsec, inv_mul_cancel_left]

include hs in

def restrictSlice (f : LocallyConstant G X) (m : N) : LocallyConstant (G ⧸ N) X :=
  ⟨fun c => f (s c * m), f.isLocallyConstant.comp_continuous (hs.mul continuous_const)⟩

theorem isLocallyConstant_restrictSlice (f : LocallyConstant G X) :
    IsLocallyConstant (restrictSlice X N hs f) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro m₀
  have hc : Continuous fun m : N => (m₀ : G)⁻¹ * m := continuous_const.mul continuous_subtype_val
  have h1 : Tendsto (fun m : N => (m₀ : G)⁻¹ * m) (𝓝 m₀) (𝓝 1) := by
    simpa using hc.tendsto m₀
  filter_upwards [h1.eventually (eventually_forall_mul_eq f)] with m hm
  ext c
  have := hm (s c * m₀)
  simp only [mul_assoc, mul_inv_cancel_left] at this
  exact this

noncomputable def restrictCoindLinear :
    LocallyConstant G X →ₗ[k] LocallyConstant N (LocallyConstant (G ⧸ N) X) where
  toFun f := ⟨restrictSlice X N hs f, isLocallyConstant_restrictSlice X N hs f⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def unrestrictCoind (F : LocallyConstant N (LocallyConstant (G ⧸ N) X)) :
    LocallyConstant G X where
  toFun x := F (sectionRetraction N hsec x) (x : G ⧸ N)
  isLocallyConstant := by
    have hF : IsLocallyConstant fun p : N × (G ⧸ N) => F p.1 p.2 := by
      rw [IsLocallyConstant.iff_eventually_eq]
      rintro ⟨m₀, c₀⟩
      have h1 : ∀ᶠ m in 𝓝 m₀, F m = F m₀ := F.isLocallyConstant.eventually_eq m₀
      have h2 : ∀ᶠ c in 𝓝 c₀, F m₀ c = F m₀ c₀ := (F m₀).isLocallyConstant.eventually_eq c₀
      filter_upwards [h1.prod_nhds h2] with p hp
      rw [hp.1, hp.2]
    exact hF.comp_continuous
      ((continuous_sectionRetraction N hs hsec).prodMk QuotientGroup.continuous_mk)

theorem mk_mul_mem (x : G) (m : N) : ((x * m : G) : G ⧸ N) = x :=
  QuotientGroup.eq.mpr (by rw [mul_inv_rev, inv_mul_cancel_right]; exact N.inv_mem m.2)

theorem sectionRetraction_mul (x : G) (m : N) :
    sectionRetraction N hsec (x * m) = sectionRetraction N hsec x * m := by
  apply Subtype.ext
  rw [coe_sectionRetraction, mk_mul_mem, Subgroup.coe_mul, coe_sectionRetraction, mul_assoc]

noncomputable def resDiscreteCoindIso :
    Rep.res N.subtype (discreteCoind k G X) ≅ discreteCoind k N (LocallyConstant (G ⧸ N) X) :=
  have hcomm : ∀ (m : N) (f : LocallyConstant G X),
      restrictCoindLinear (k := k) X N hs (discreteCoindRep k G X m f) =
        discreteCoindRep k N (LocallyConstant (G ⧸ N) X) m (restrictCoindLinear (k := k) X N hs f) := by
    intro m f
    ext m' c
    change f (s c * m' * m) = f (s c * ((m' * m : N) : G))
    rw [Subgroup.coe_mul, mul_assoc]
  { hom := Rep.ofHom ⟨restrictCoindLinear (k := k) X N hs, fun m => LinearMap.ext (hcomm m)⟩
    inv := Rep.ofHom ⟨{ toFun := unrestrictCoind X N hs hsec
                        map_add' := fun _ _ => rfl
                        map_smul' := fun _ _ => rfl }, fun m => by
      ext F x
      change F (sectionRetraction N hsec x * m) (x : G ⧸ N) =
        F (sectionRetraction N hsec (x * m)) ((x * m : G) : G ⧸ N)
      rw [sectionRetraction_mul, mk_mul_mem]⟩
    hom_inv_id := by
      ext f x
      change f (s (x : G ⧸ N) * (sectionRetraction N hsec x : G)) = f x
      rw [section_mul_sectionRetraction]
    inv_hom_id := by
      ext F m c
      change F (sectionRetraction N hsec (s c * m)) ((s c * m : G) : G ⧸ N) = F m c
      rw [sectionRetraction_section_mul N hsec, mk_section_mul N hsec] }

variable [TotallyDisconnectedSpace G]

instance isSmoothRep_res_discreteCoind : IsSmoothRep (Rep.res N.subtype (discreteCoind k G X)) :=
  isSmoothRep_res_subtype _ N

theorem isZero_cohomology_res_discreteCoind (hN : IsClosed (N : Set G)) (n : ℕ) :
    Limits.IsZero (cohomology (Rep.res N.subtype (discreteCoind k G X)) (n + 1)) := by
  obtain ⟨s, hs, hsec, -⟩ := exists_continuous_section N hN
  have : CompactSpace N := isCompact_iff_compactSpace.mp hN.isCompact
  exact (isZero_cohomology_discreteCoind k N (LocallyConstant (G ⧸ N) X) n).of_iso
    (cohomologyIsoOfIso (resDiscreteCoindIso X N hs hsec) (n + 1))

end Restriction

section Invariants

variable (N : Subgroup G) [N.Normal]

variable {X N} in

theorem apply_eq_of_mem_invariants {f : LocallyConstant G X}
    (hf : f ∈ Representation.invariants ((discreteCoindRep k G X).comp N.subtype)) {x y : G}
    (h : (x : G ⧸ N) = y) : f x = f y := by
  have hn : x⁻¹ * y ∈ N := QuotientGroup.eq.mp h
  have := congrArg (fun φ : LocallyConstant G X => φ x) (hf ⟨x⁻¹ * y, hn⟩)
  change f (x * (x⁻¹ * y)) = f x at this
  rw [mul_inv_cancel_left] at this
  exact this.symm

noncomputable def descendInvariant (f : Representation.invariants ((discreteCoindRep k G X).comp N.subtype)) :
    LocallyConstant (G ⧸ N) X where
  toFun c := (f : LocallyConstant G X) c.out
  isLocallyConstant := by
    intro S
    rw [← (QuotientGroup.isQuotientMap_mk N).isOpen_preimage]
    have h : (QuotientGroup.mk ⁻¹' ((fun c : G ⧸ N => (f : LocallyConstant G X) c.out) ⁻¹' S)) =
        (f : LocallyConstant G X) ⁻¹' S := by
      ext x
      simp only [Set.mem_preimage]
      rw [apply_eq_of_mem_invariants f.2 (QuotientGroup.out_eq' (x : G ⧸ N))]
    rw [h]
    exact (f : LocallyConstant G X).isLocallyConstant S

theorem descendInvariant_mk (f : Representation.invariants ((discreteCoindRep k G X).comp N.subtype)) (x : G) :
    descendInvariant X N f x = (f : LocallyConstant G X) x :=
  apply_eq_of_mem_invariants f.2 (QuotientGroup.out_eq' (x : G ⧸ N))

noncomputable def invariantsDiscreteCoindQuotientEquiv :
    Representation.invariants ((discreteCoindRep k G X).comp N.subtype) ≃ₗ[k] LocallyConstant (G ⧸ N) X where
  toFun := descendInvariant X N
  invFun g := ⟨g.comap ⟨QuotientGroup.mk, QuotientGroup.continuous_mk⟩, fun n => by
    ext x
    change g ((x * n : G) : G ⧸ N) = g (x : G ⧸ N)
    rw [QuotientGroup.mk_mul, QuotientGroup.eq_one_iff (n : G) |>.mpr n.2, mul_one]⟩
  map_add' f f' := by
    ext c
    rfl
  map_smul' r f := by
    ext c
    rfl
  left_inv f := by
    ext x
    exact descendInvariant_mk X N f x
  right_inv g := by
    ext c
    change g ((c.out : G) : G ⧸ N) = g c
    rw [QuotientGroup.out_eq']

noncomputable def quotientToInvariantsDiscreteCoindIso :
    (discreteCoind k G X).quotientToInvariants N ≅ discreteCoind k (G ⧸ N) X :=
  have hcomm : ∀ (q : G ⧸ N) (f : Representation.invariants ((discreteCoindRep k G X).comp N.subtype)),
      invariantsDiscreteCoindQuotientEquiv X N ((discreteCoind k G X).ρ.quotientToInvariants N q f) =
        discreteCoindRep k (G ⧸ N) X q (invariantsDiscreteCoindQuotientEquiv X N f) := by
    intro q f
    induction q using QuotientGroup.induction_on with
    | H g =>
      ext c
      change (f : LocallyConstant G X) (c.out * g) =
        (f : LocallyConstant G X) ((c * (g : G ⧸ N)).out)
      apply apply_eq_of_mem_invariants f.2
      rw [QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.out_eq']
  { hom := Rep.ofHom ⟨(invariantsDiscreteCoindQuotientEquiv X N).toLinearMap,
      fun q => LinearMap.ext (hcomm q)⟩
    inv := Rep.ofHom ⟨(invariantsDiscreteCoindQuotientEquiv X N).symm.toLinearMap, fun q => by
      refine LinearMap.ext fun g => ?_
      apply (invariantsDiscreteCoindQuotientEquiv X N).injective
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        LinearEquiv.apply_symm_apply]
      rw [hcomm, LinearEquiv.apply_symm_apply]⟩
    hom_inv_id := by
      ext f x
      exact congrArg (fun φ : Representation.invariants ((discreteCoindRep k G X).comp N.subtype) =>
        (φ : LocallyConstant G X) x) ((invariantsDiscreteCoindQuotientEquiv X N).symm_apply_apply f)
    inv_hom_id := by
      ext g c
      exact congrArg (fun φ : LocallyConstant (G ⧸ N) X => φ c)
        ((invariantsDiscreteCoindQuotientEquiv X N).apply_symm_apply g) }

instance isSmoothRep_quotientToInvariants_discreteCoind :
    IsSmoothRep ((discreteCoind k G X).quotientToInvariants N) :=
  isSmoothRep_quotientToInvariants _ N

theorem isZero_cohomology_quotientToInvariants_discreteCoind (n : ℕ) :
    Limits.IsZero (cohomology ((discreteCoind k G X).quotientToInvariants N) (n + 1)) :=
  (isZero_cohomology_discreteCoind k (G ⧸ N) X n).of_iso
    (cohomologyIsoOfIso (quotientToInvariantsDiscreteCoindIso X N) (n + 1))

end Invariants

end Langlands.ProfiniteCohomology
