import Langlands.Cohomology.Profinite.InflationRestriction.Higher
import Langlands.Cohomology.Profinite.InflationRestriction.Transgression

namespace Langlands.ProfiniteCohomology

open CategoryTheory

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{u} k G) [IsSmoothRep A] (N : Subgroup G) [N.Normal]

section Restriction

noncomputable def resInv : cohomology A 1 →ₗ[k] cohomologyConjInvariants A N 1 :=
  (res A N 1).hom.codRestrict _ (res_mem_cohomologyConjInvariants A N)

@[simp]
theorem coe_resInv_apply (h : cohomology A 1) :
    (resInv A N h : cohomology (Rep.res N.subtype A) 1) = (res A N 1).hom h :=
  rfl

theorem cocycleOneApply_cocyclesMap (y : cocycles A 1) (n : N) :
    cocycleOneApply A N ((cocyclesMap (subgroupInclusion N) (𝟙 (Rep.res N.subtype A)) 1).hom y)
      n = cocycleOneApplyG A y n := by
  simp only [cocycleOneApply, cocyclesMap, iCycles_cyclesMap_apply]
  rfl

theorem res_π (y : cocycles A 1) :
    (res A N 1).hom ((cohomologyπ A 1).hom y) = (cohomologyπ _ 1).hom
      ((cocyclesMap (subgroupInclusion N) (𝟙 (Rep.res N.subtype A)) 1).hom y) := by
  rw [res, map]
  erw [homologyMap_homologyπ_apply]
  rfl

theorem isTgLift_cocycleOneApplyG (y : cocycles A 1) :
    IsTgLift A N (cocycleOneApply A N ((cocyclesMap (subgroupInclusion N)
      (𝟙 (Rep.res N.subtype A)) 1).hom y)) (cocycleOneApplyG A y) where
  map_one := cocycle_one_apply_one A (iCycles_d_apply _ 1 2 y)
  mul_right g n := by
    rw [cocycleOneApply_cocyclesMap, cocycleOneApplyG_mul]
  conj h n := by
    rw [cocycleOneApply_cocyclesMap, cocycleOneApply_cocyclesMap]
    have e : h * (conjHom N h n : G) = n * h := by
      simp only [coe_conjHom_apply]; group
    have h1 := cocycleOneApplyG_mul A y h (conjHom N h n)
    rw [e, cocycleOneApplyG_mul A y n h] at h1
    rw [show A.ρ h (cocycleOneApplyG A y (conjHom N h n)) =
      cocycleOneApplyG A y n + A.ρ n (cocycleOneApplyG A y h) - cocycleOneApplyG A y h by
        rw [h1]; abel]
    abel

theorem isLocallyConstant_cocycleOneApplyG (y : cocycles A 1) :
    IsLocallyConstant (cocycleOneApplyG A y) :=
  (((cochains A).iCycles 1).hom y).2.comp_continuous (continuous_pi fun _ => continuous_id)

theorem isTransgression_res (h : cohomology A 1) :
    IsTransgression A N ((res A N 1).hom h) 0 := by
  obtain ⟨y, rfl⟩ := homologyπ_surjective (cochains A) 1 h
  refine ⟨_, _, isTgLift_cocycleOneApplyG A N y, isLocallyConstant_cocycleOneApplyG A y,
    (res_π A N y).symm, ?_⟩
  have h0 : cocycleOf 2 (tgCochain (isCocycleOne_cocycleOneApply A N _)
      (isTgLift_cocycleOneApplyG A N y) (isLocallyConstant_cocycleOneApplyG A y))
      (tgCochain_d _ _ _) = 0 := by
    rw [cocycleOf_eq_iff, map_zero]
    apply Subtype.ext
    funext c
    apply Subtype.ext
    change (0 : A) = A.ρ _ (cocycleOneApplyG A y _) - cocycleOneApplyG A y _ +
      cocycleOneApplyG A y _
    rw [cocycleOneApplyG_mul]
    abel
  simp only [tgClass, h0, map_zero]

end Restriction

section Inflation

variable {A N}

theorem infl_tgClass (z : cocycles (Rep.res N.subtype A) 1) {y : G → A}
    (hy : IsTgLift A N (cocycleOneApply A N z) y) (hyc : IsLocallyConstant y) :
    (infl A N 2).hom (tgClass z hy hyc) = 0 := by
  simp only [tgClass]
  rw [infl, map]
  erw [homologyMap_homologyπ_apply]
  refine (homologyπ_succ_eq_zero_iff _ 1 _).2 ⟨liftCochain A hyc, ?_⟩
  rw [iCycles_cyclesMap_apply, iCycles_cocycleOf]
  exact (cochainsMap_tgCochain _ hy hyc).symm

end Inflation

section Exactness

variable [CompactSpace G] [TotallyDisconnectedSpace G] (hN : IsClosed (N : Set G))

include hN in

theorem infl_transgression (h : cohomologyConjInvariants A N 1) :
    (infl A N 2).hom (transgression A N hN h) = 0 := by
  obtain ⟨z, y, hy, hyc, -, ht⟩ := isTransgression_transgression A N hN h
  rw [← ht]
  exact infl_tgClass z hy hyc

theorem transgression_resInv (h : cohomology A 1) :
    transgression A N hN (resInv A N h) = 0 :=
  (transgression_eq_iff A N hN _ 0).2 (isTransgression_res A N h)

theorem exists_resInv_eq (h : cohomologyConjInvariants A N 1)
    (hh : transgression A N hN h = 0) : ∃ g, resInv A N g = h := by
  obtain ⟨z, y, hy, hyc, hz, ht⟩ := (transgression_eq_iff A N hN h 0).1 hh
  have hxc := isCocycleOne_cocycleOneApply A N z
  obtain ⟨W, hW⟩ := (homologyπ_succ_eq_zero_iff _ 1 _).1 ht
  rw [iCycles_cocycleOf] at hW
  let Wf : G → A := fun g => ((W.1 fun _ => (g : G ⧸ N)) : A)
  have hWf : ∀ g h : G, A.ρ g (Wf h) - Wf (g * h) + Wf g = tgDiff A y g h := by
    intro g h
    have e := congrArg (fun v : locallyConstantCochains (A.quotientToInvariants N) 2 =>
      ((v.1 ![(g : G ⧸ N), (h : G ⧸ N)] : Representation.invariants (A.ρ.comp N.subtype)) : A)) hW
    have hd := congrArg Subtype.val
      (cochains_d_one_apply (A.quotientToInvariants N) W ![(g : G ⧸ N), (h : G ⧸ N)])
    rw [← hy.tgDiff_out hxc g h]
    exact hd.symm.trans e
  have hW1 : Wf 1 = 0 := by
    have := hWf 1 1
    simp only [one_mul, map_one, Module.End.one_apply, tgDiff, hy.map_one, sub_self,
      add_zero] at this
    simpa using this
  let y' : G → A := fun g => y g - Wf g
  have hWc : IsLocallyConstant Wf :=
    (W.2.comp_continuous (continuous_pi fun _ => QuotientGroup.continuous_mk)).comp Subtype.val
  have hy'c : IsLocallyConstant y' := hyc.sub hWc
  have hcoc : ∀ g h : G, tgDiff A y' g h = 0 := by
    intro g h
    have := hWf g h
    simp only [tgDiff, y', map_sub] at this ⊢
    rw [← sub_eq_zero.mpr this.symm]
    abel
  have hd' : ((cochains A).d 1 (1 + 1)).hom (liftCochain A hy'c) = 0 := by
    apply Subtype.ext
    funext g
    exact (cochains_d_liftCochain A hy'c g).trans (hcoc (g 0) (g 1))
  refine ⟨(cohomologyπ A 1).hom (cocycleOf 1 (liftCochain A hy'c) hd'), Subtype.ext ?_⟩
  rw [coe_resInv_apply, res_π, ← hz]
  congr 1
  apply iCycles_injective
  rw [iCycles_cyclesMap_apply, iCycles_cocycleOf]
  apply Subtype.ext
  funext g
  change y' (g 0 : G) = (((cochains (Rep.res N.subtype A)).iCycles 1).hom z).1 g
  rw [fin_one_eq_const g]
  change y (g 0 : G) - Wf (g 0 : G) = cocycleOneApply A N z (g 0)
  have hm : ((g 0 : G) : G ⧸ N) = ((1 : G) : G ⧸ N) := by
    rw [QuotientGroup.mk_one]
    exact (QuotientGroup.eq_one_iff _).2 (g 0).2
  have hWn : Wf (g 0 : G) = Wf 1 := by
    change ((W.1 fun _ => ((g 0 : G) : G ⧸ N)) : A) = ((W.1 fun _ => ((1 : G) : G ⧸ N)) : A)
    rw [hm]
  rw [hWn, hW1, sub_zero, show ((g 0 : N) : G) = 1 * (g 0 : G) from (one_mul _).symm,
    hy.mul_right, hy.map_one, zero_add, map_one, Module.End.one_apply]

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
theorem comp_vecCons_mk (g h : G) :
    (⇑(QuotientGroup.mk' N) ∘ ![g, h]) = ![(g : G ⧸ N), (h : G ⧸ N)] := by
  funext i
  fin_cases i <;> rfl

theorem exists_transgression_eq (t : cohomology (A.quotientToInvariants N) 2)
    (ht : (infl A N 2).hom t = 0) : ∃ h, transgression A N hN h = t := by
  obtain ⟨ζ, rfl⟩ := homologyπ_surjective (cochains (A.quotientToInvariants N)) 2 t
  rw [infl, map] at ht
  erw [homologyMap_homologyπ_apply] at ht
  obtain ⟨y₀, hy₀⟩ := (homologyπ_succ_eq_zero_iff _ 1 _).1 ht
  rw [iCycles_cyclesMap_apply] at hy₀
  set Zf : locallyConstantCochains (A.quotientToInvariants N) 2 :=
    ((cochains (A.quotientToInvariants N)).iCycles 2).hom ζ with hZf
  let ZA : G → G → A := fun g h =>
    ((Zf.1 ![(g : G ⧸ N), (h : G ⧸ N)] : Representation.invariants (A.ρ.comp N.subtype)) : A)
  let Y₀ : G → A := fun g => y₀.1 fun _ => g
  have hY₀ : ∀ g h, tgDiff A Y₀ g h = ZA g h := by
    intro g h
    have e := congrArg (fun v : locallyConstantCochains A 2 => v.1 ![g, h]) hy₀
    have hd := cochains_d_one_apply A y₀ ![g, h]
    refine hd.symm.trans (e.trans ?_)
    change (((Zf.1 (⇑(QuotientGroup.mk' N) ∘ ![g, h])) :
      Representation.invariants (A.ρ.comp N.subtype)) : A) = _
    rw [comp_vecCons_mk]
  set c : A := Y₀ 1 with hcdef
  have hc : c ∈ Representation.invariants (A.ρ.comp N.subtype) := by
    have := hY₀ 1 1
    simp only [tgDiff, one_mul, map_one, Module.End.one_apply, sub_self, zero_add] at this
    rw [hcdef, this]
    exact (Zf.1 _).2
  let Y : G → A := fun g => Y₀ g - c
  have hYdiff : ∀ g h, tgDiff A Y g h = ZA g h - A.ρ g c := by
    intro g h
    rw [← hY₀]
    simp only [tgDiff, Y, map_sub]
    abel
  have hZA : ∀ g g' h h' : G, (g : G ⧸ N) = g' → (h : G ⧸ N) = h' → ZA g h = ZA g' h' := by
    intro g g' h h' e1 e2
    simp only [ZA, e1, e2]
  have hρc : ∀ (g : G) (n : N), A.ρ (g * n) c = A.ρ g c := by
    intro g n
    rw [map_mul, Module.End.mul_apply]
    exact congrArg (A.ρ g) (hc n)
  have hY1 : Y 1 = 0 := sub_self _
  have hmk : ∀ n : N, ((n : G) : G ⧸ N) = ((1 : G) : G ⧸ N) := fun n => by
    rw [QuotientGroup.mk_one]
    exact (QuotientGroup.eq_one_iff _).2 n.2
  have hR : ∀ (g : G) (n : N), tgDiff A Y g n = 0 := by
    intro g n
    rw [hYdiff, hZA g g n 1 rfl (hmk n), ← hYdiff]
    simp [tgDiff, hY1]
  have hL : ∀ (n : N) (h : G), tgDiff A Y n h = 0 := by
    intro n h
    rw [hYdiff, hZA n 1 h h (hmk n) rfl, show A.ρ (n : G) c = A.ρ 1 c by
      rw [map_one]; exact hc n, ← hYdiff]
    simp [tgDiff, hY1]
  have hmr : ∀ (g : G) (n : N), Y (g * n) = Y g + A.ρ g (Y n) := by
    intro g n
    have := hR g n
    simp only [tgDiff] at this
    rw [← sub_eq_zero, ← neg_eq_zero, ← this]
    abel
  have hYc : IsLocallyConstant Y :=
    (y₀.2.comp_continuous (continuous_pi fun _ => continuous_id)).sub (IsLocallyConstant.const c)

  let zc : locallyConstantCochains (Rep.res N.subtype A) 1 :=
    ⟨fun g => Y (g 0 : G), hYc.comp_continuous (continuous_subtype_val.comp (continuous_apply 0))⟩
  have hzc : ((cochains (Rep.res N.subtype A)).d 1 (1 + 1)).hom zc = 0 :=
    (cochains_d_one_eq_zero_iff (Rep.res N.subtype A) zc).2 fun a b => hmr a b
  set z := cocycleOf 1 zc hzc with hzdef
  have hX : cocycleOneApply A N z = fun n : N => Y n := by
    funext n
    simp only [cocycleOneApply, hzdef, iCycles_cocycleOf]
    rfl
  have hlift : IsTgLift A N (cocycleOneApply A N z) Y := by
    rw [hX]
    refine ⟨hY1, hmr, fun h n => ?_⟩
    have h1 := hL n h
    have e : (n : G) * h = h * (conjHom N h n : G) := by
      simp only [coe_conjHom_apply]; group
    simp only [tgDiff] at h1
    rw [e, hmr] at h1
    rw [← sub_eq_zero, ← neg_eq_zero, ← h1]
    abel
  have hinv : (cohomologyπ _ 1).hom z ∈ cohomologyConjInvariants A N 1 := fun g =>
    (cohomologyConj_π_eq_iff A N z g).2 ⟨Y g, hlift.conj g⟩
  refine ⟨⟨_, hinv⟩, (transgression_eq_iff A N hN _ _).2 ⟨z, Y, hlift, hYc, rfl, ?_⟩⟩

  let w : locallyConstantCochains (A.quotientToInvariants N) 1 :=
    ⟨fun _ => ⟨-c, (Representation.invariants (A.ρ.comp N.subtype)).neg_mem hc⟩,
      IsLocallyConstant.const _⟩
  have hw : ((cochains (A.quotientToInvariants N)).d 1 (1 + 1)).hom w =
      tgCochain (isCocycleOne_cocycleOneApply A N z) hlift hYc - Zf := by
    apply Subtype.ext
    funext cc
    apply Subtype.ext
    have hd := congrArg Subtype.val (cochains_d_one_apply (A.quotientToInvariants N) w cc)
    refine hd.trans ?_
    have hq := quotientToInvariants_ρ_apply_coe (A := A) (N := N) (cc 0)
      ⟨-c, (Representation.invariants (A.ρ.comp N.subtype)).neg_mem hc⟩
    simp only [Submodule.coe_add, Submodule.coe_sub]
    change _ - (-c) + (-c) = tgDiff A Y (cc 0).out (cc 1).out - ((Zf.1 cc : _) : A)
    rw [hq, hYdiff]
    have ecc : ![((cc 0).out : G ⧸ N), ((cc 1).out : G ⧸ N)] = cc := by
      funext i
      fin_cases i <;> exact QuotientGroup.out_eq' _
    simp only [ZA, ecc, map_neg]
    abel
  have e := cohomologyπ_cocycleOf_eq 1 Zf _ (iCycles_d_apply _ 2 3 ζ) (tgCochain_d _ hlift hYc) w hw
  refine e.trans ?_
  congr 1
  rw [cocycleOf_eq_iff]

end Exactness

end Langlands.ProfiniteCohomology

namespace Langlands.ProfiniteCohomology

open CategoryTheory Limits

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G] (A : Rep.{u} k G) [IsSmoothRep A]
  (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G))

theorem fiveTerm_exact :
    Function.Injective (infl A N 1).hom ∧
      LinearMap.range (infl A N 1).hom = LinearMap.ker (resInv A N) ∧
      LinearMap.range (resInv A N) = LinearMap.ker (transgression A N hN) ∧
      LinearMap.range (transgression A N hN) = LinearMap.ker (infl A N 2).hom := by
  refine ⟨infl_one_injective A N, ?_, ?_, ?_⟩
  · ext h
    constructor
    · rintro ⟨y, rfl⟩
      rw [LinearMap.mem_ker]
      apply Subtype.ext
      rw [coe_resInv_apply, ZeroMemClass.coe_zero]
      have := congrArg (fun φ => ModuleCat.Hom.hom φ y) (infl_comp_res A N 0)
      simpa using this
    · intro hh
      exact exists_infl_one_eq A N h (congrArg Subtype.val hh)
  · ext h
    constructor
    · rintro ⟨g, rfl⟩
      exact transgression_resInv A N hN g
    · intro hh
      exact exists_resInv_eq A N hN h hh
  · ext t
    constructor
    · rintro ⟨h, rfl⟩
      exact infl_transgression A N hN h
    · intro ht
      exact exists_transgression_eq A N hN t ht

include hN in

theorem infRes_exact {q : ℕ} (hq : q ≠ 0)
    (hA : ∀ i, 0 < i → i < q → IsZero (cohomology (Rep.res N.subtype A) i)) :
    Function.Injective (infl A N q).hom ∧
      LinearMap.range (infl A N q).hom = LinearMap.ker (res A N q).hom :=
  ⟨infl_injective_of_isZero hN hq hA, range_infl_eq_ker_res hN hq hA⟩

end Langlands.ProfiniteCohomology
