import Langlands.Cohomology.Profinite.Comparison.Discrete
import Langlands.Cohomology.Profinite.Comparison.FilteredHomology
import Langlands.Cohomology.Profinite.LowDegree

namespace Langlands.ProfiniteCohomology

open CategoryTheory Limits groupCohomology

universe u

section Conjugation

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G) (S : Subgroup G) [S.Normal]

/-- Conjugation `s ↦ g⁻¹ s g` on a normal subgroup. -/
def conjHom (g : G) : S →* S where
  toFun s := ⟨g⁻¹ * s * g, ‹S.Normal›.conj_mem' (s : G) s.2 g⟩
  map_one' := by ext; simp
  map_mul' s t := by ext; simp only [Subgroup.coe_mul]; group

@[simp]
theorem coe_conjHom_apply (g : G) (s : S) : (conjHom S g s : G) = g⁻¹ * s * g := rfl

/-- The action of `g` on coefficients, compatible with `conjHom S g`. -/
noncomputable def conjMor (g : G) :
    Rep.res (conjHom S g) (Rep.res S.subtype A) ⟶ Rep.res S.subtype A :=
  Rep.ofHom ⟨A.ρ g, fun s => by
    ext a
    simp only [LinearMap.comp_apply, MonoidHom.coe_comp, Function.comp_apply,
      Subgroup.coe_subtype, coe_conjHom_apply]
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group⟩

@[simp]
theorem conjMor_hom_apply (g : G) (a : A) : (conjMor A S g).hom a = A.ρ g a := rfl

end Conjugation

section Complex

variable {R : Type u} [Ring R] (K : CochainComplex (ModuleCat.{u} R) ℕ)

theorem homologyπ_succ_eq_zero_iff (n : ℕ) (z : K.cycles (n + 1)) :
    (K.homologyπ (n + 1)).hom z = 0 ↔
      ∃ w : K.X n, (K.d n (n + 1)).hom w = (K.iCycles (n + 1)).hom z := by
  have h := homologyπ_eq_zero_iff K z
  rw [CochainComplex.prev_nat_succ] at h
  exact h

theorem exists_iCycles_eq_of_d_eq_zero (n : ℕ) (x : K.X n) (hx : (K.d n (n + 1)).hom x = 0) :
    ∃ z : K.cycles n, (K.iCycles n).hom z = x := by
  refine exists_iCycles_eq K x ?_
  rw [CochainComplex.next]
  exact hx

theorem homologyπ_surjective (n : ℕ) : Function.Surjective (K.homologyπ n).hom :=
  (ModuleCat.epi_iff_surjective _).1 inferInstance

theorem iCycles_injective (n : ℕ) : Function.Injective (K.iCycles n).hom :=
  (ModuleCat.mono_iff_injective _).1 inferInstance

end Complex

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Comparison

variable (A : Rep.{u} k G) [IsSmoothRep A]

omit [IsTopologicalGroup G] in

theorem isLocallyConstant_cochain_zero (w : (Fin 0 → G) → A) : IsLocallyConstant w := by
  have h : w = fun _ => w Fin.elim0 := funext fun x => congrArg w (Subsingleton.elim _ _)
  rw [h]
  exact IsLocallyConstant.const _

theorem toGroupCohomology_one_injective :
    Function.Injective (toGroupCohomology A 1).hom := by
  rw [injective_iff_map_eq_zero]
  intro h hh
  obtain ⟨z, rfl⟩ := homologyπ_surjective (cochains A) 1 h
  have hh' : (HomologicalComplex.homologyMap (cochainsι A) 1).hom
      (((cochains A).homologyπ 1).hom z) = 0 := hh
  rw [homologyMap_homologyπ_apply] at hh'
  obtain ⟨w, hw⟩ := (homologyπ_succ_eq_zero_iff _ 0 _).1 hh'
  rw [iCycles_cyclesMap_apply] at hw
  refine (homologyπ_succ_eq_zero_iff (cochains A) 0 z).2
    ⟨⟨w, isLocallyConstant_cochain_zero A w⟩, ?_⟩
  exact (ModuleCat.mono_iff_injective ((cochainsι A).f 1)).1 inferInstance
    ((hom_f_d_apply (cochainsι A) 0 1 _).trans hw)

end Comparison

section InflationRestriction

variable (A : Rep.{u} k G) [IsSmoothRep A] (N : Subgroup G) [N.Normal]

noncomputable def invariantsIncl :
    Rep.res (1 : N →* PUnit.{u + 1})
        (Rep.res (1 : PUnit.{u + 1} →* G ⧸ N) (A.quotientToInvariants N)) ⟶
      Rep.res N.subtype A :=
  Rep.ofHom ⟨Submodule.subtype _, fun n => by
    ext x
    simp only [LinearMap.comp_apply, MonoidHom.comp_apply, MonoidHom.one_apply, map_one,
      Module.End.one_apply, Submodule.subtype_apply]
    exact (x.2 n).symm⟩

theorem infl_comp_res (n : ℕ) :
    infl A N (n + 1) ≫ res A N (n + 1) = 0 := by
  let B := Rep.res (1 : PUnit.{u + 1} →* G ⧸ N) (A.quotientToInvariants N)
  have hfac : cochainsMap (quotientMap N)
        (Rep.ofHom (A.ρ.quotientToInvariants_lift N)) ≫
      cochainsMap (subgroupInclusion N) (𝟙 (Rep.res N.subtype A)) =
      cochainsMap (A := A.quotientToInvariants N) (B := B) ⟨1, continuous_const⟩ (𝟙 _) ≫
        cochainsMap (A := B) ⟨1, continuous_const⟩ (invariantsIncl A N) := by
    ext m x : 3
    apply Subtype.ext
    funext h
    change (((x : locallyConstantCochains (A.quotientToInvariants N) m).1
        fun i => ((h i : G) : G ⧸ N)) : A) =
      (((x : locallyConstantCochains (A.quotientToInvariants N) m).1 fun _ => 1) : A)
    congr 2
    exact congrArg _ (funext fun i => (QuotientGroup.eq_one_iff _).2 (h i).2)
  have hB : IsZero (cohomology B (n + 1)) :=
    (isZero_groupCohomology_succ_of_subsingleton B n).of_iso (isoGroupCohomology B (n + 1))
  change HomologicalComplex.homologyMap _ (n + 1) ≫ HomologicalComplex.homologyMap _ (n + 1) = 0
  rw [← HomologicalComplex.homologyMap_comp, hfac, HomologicalComplex.homologyMap_comp]
  have h0 := hB.eq_of_tgt (HomologicalComplex.homologyMap (cochainsMap
    (A := A.quotientToInvariants N) (B := B) ⟨1, continuous_const⟩ (𝟙 _)) (n + 1)) 0
  rw [h0]
  exact Limits.zero_comp

theorem map_toGroupCohomology_apply (n : ℕ)
    (y : cohomology (A.quotientToInvariants N) n) :
    (groupCohomology.map (QuotientGroup.mk' N) (Rep.ofHom (A.ρ.quotientToInvariants_lift N)) n).hom
        ((toGroupCohomology (A.quotientToInvariants N) n).hom y) =
      (toGroupCohomology A n).hom ((infl A N n).hom y) := by
  have := congrArg (fun φ => ModuleCat.Hom.hom φ y)
    (infl_comp_toGroupCohomology A N n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
  exact this.symm

theorem map_subtype_toGroupCohomology_apply (n : ℕ) (h : cohomology A n) :
    (groupCohomology.map N.subtype (𝟙 _) n).hom ((toGroupCohomology A n).hom h) =
      (toGroupCohomology (Rep.res N.subtype A) n).hom ((res A N n).hom h) := by
  have := congrArg (fun φ => ModuleCat.Hom.hom φ h)
    (res_comp_toGroupCohomology A N n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
  exact this.symm

theorem infl_one_injective : Function.Injective (infl A N 1).hom := by
  intro y y' hyy'
  have hinj : Function.Injective (H1InfRes A N).f.hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  exact toGroupCohomology_one_injective _ (hinj
    ((map_toGroupCohomology_apply A N 1 y).trans ((congrArg _ hyy').trans
      (map_toGroupCohomology_apply A N 1 y').symm)))

omit [IsTopologicalGroup G] in

theorem isLocallyConstant_of_comp_isQuotientMap {X Y Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {q : X → Y} (hq : Topology.IsQuotientMap q) {f : Y → Z}
    (hf : IsLocallyConstant (f ∘ q)) : IsLocallyConstant f := fun S =>
  hq.isOpen_preimage.mp (hf S)

theorem exists_infl_one_eq (h : cohomology A 1)
    (hres : (res A N 1).hom h = 0) : ∃ y, (infl A N 1).hom y = h := by
  have hg : (groupCohomology.map N.subtype (𝟙 _) 1).hom
      ((toGroupCohomology A 1).hom h) = 0 := by
    rw [map_subtype_toGroupCohomology_apply, hres, map_zero]
  have hker : (toGroupCohomology A 1).hom h ∈ LinearMap.ker (H1InfRes A N).g.hom := hg
  rw [← (H1InfRes_exact A N).moduleCat_range_eq_ker] at hker
  obtain ⟨y', hy'⟩ := hker
  obtain ⟨Y, rfl⟩ := homologyπ_surjective (inhomogeneousCochains (A.quotientToInvariants N)) 1 y'
  obtain ⟨z, rfl⟩ := homologyπ_surjective (cochains A) 1 h
  have hy0 := hy'
  change (HomologicalComplex.homologyMap (groupCohomology.cochainsMap (QuotientGroup.mk' N)
      (Rep.ofHom (A.ρ.quotientToInvariants_lift N))) 1).hom
      (((inhomogeneousCochains (A.quotientToInvariants N)).homologyπ 1).hom Y) =
    (HomologicalComplex.homologyMap (cochainsι A) 1).hom
      (((cochains A).homologyπ 1).hom z) at hy'
  rw [homologyMap_homologyπ_apply, homologyMap_homologyπ_apply, ← sub_eq_zero, ← map_sub] at hy'
  obtain ⟨w, hw⟩ := (homologyπ_succ_eq_zero_iff _ 0 _).1 hy'
  rw [map_sub, iCycles_cyclesMap_apply, iCycles_cyclesMap_apply] at hw

  let Yc := ((inhomogeneousCochains (A.quotientToInvariants N)).iCycles 1).hom Y
  let w' : locallyConstantCochains A 0 := ⟨w, isLocallyConstant_cochain_zero A w⟩
  let D : locallyConstantCochains A 1 := ((cochains A).d 0 1).hom w'
  let Z : locallyConstantCochains A 1 := ((cochains A).iCycles 1).hom z
  have hD : ((cochainsι A).f 1).hom D = (inhomogeneousCochains A).d 0 1 w :=
    hom_f_d_apply (cochainsι A) 0 1 w'
  have hF : IsLocallyConstant (((groupCohomology.cochainsMap (QuotientGroup.mk' N)
      (Rep.ofHom (A.ρ.quotientToInvariants_lift N))).f 1).hom Yc : (Fin 1 → G) → A) := by
    rw [sub_eq_iff_eq_add.mp hw.symm, ← hD]
    exact D.2.add Z.2
  let q : (Fin 1 → G) → (Fin 1 → G ⧸ N) := Pi.map fun _ => QuotientGroup.mk
  have hq : Topology.IsQuotientMap q :=
    (IsOpenQuotientMap.piMap fun _ => QuotientGroup.isOpenQuotientMap_mk).isQuotientMap
  have hYq : IsLocallyConstant ((Yc : (Fin 1 → G ⧸ N) → _) ∘ q) :=
    IsLocallyConstant.desc _ Subtype.val hF Subtype.val_injective
  have hY : IsLocallyConstant (Yc : (Fin 1 → G ⧸ N) → _) :=
    isLocallyConstant_of_comp_isQuotientMap hq hYq
  let Ylc : locallyConstantCochains (A.quotientToInvariants N) 1 := ⟨Yc, hY⟩
  have hd : ((cochains (A.quotientToInvariants N)).d 1 (1 + 1)).hom Ylc = 0 := by
    apply (ModuleCat.mono_iff_injective ((cochainsι (A.quotientToInvariants N)).f 2)).1
      inferInstance
    rw [map_zero]
    exact (hom_f_d_apply (cochainsι (A.quotientToInvariants N)) 1 2 Ylc).trans
      (iCycles_d_apply _ 1 2 Y)
  obtain ⟨zY, hzY⟩ := exists_iCycles_eq_of_d_eq_zero (cochains (A.quotientToInvariants N)) 1 Ylc hd
  refine ⟨((cochains (A.quotientToInvariants N)).homologyπ 1).hom zY, ?_⟩
  apply toGroupCohomology_one_injective A
  refine (map_toGroupCohomology_apply A N 1 _).symm.trans ?_
  have hcyc : (HomologicalComplex.cyclesMap (cochainsι (A.quotientToInvariants N)) 1).hom zY
      = Y := by
    apply iCycles_injective
    rw [iCycles_cyclesMap_apply, hzY]
    rfl
  change (groupCohomology.map (QuotientGroup.mk' N) (Rep.ofHom (A.ρ.quotientToInvariants_lift N))
      1).hom ((HomologicalComplex.homologyMap (cochainsι (A.quotientToInvariants N)) 1).hom
        (((cochains (A.quotientToInvariants N)).homologyπ 1).hom zY)) = _
  rw [homologyMap_homologyπ_apply, hcyc]
  exact hy0

end InflationRestriction

end Langlands.ProfiniteCohomology

namespace Langlands.ProfiniteCohomology

open CategoryTheory groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Formulas

variable (A : Rep.{u} k G) [IsSmoothRep A]

theorem cochains_d_zero_apply (a : locallyConstantCochains A 0) (g : Fin 1 → G) :
    (((cochains A).d 0 1).hom a).1 g =
      A.ρ (g 0) (a.1 Fin.elim0) - a.1 Fin.elim0 := by
  rw [cochains_d_zero_one]
  change (inhomogeneousCochains.d A 0).hom a.1 g = _
  rw [inhomogeneousCochains.d_hom_apply]
  rw [Fin.sum_univ_one, Subsingleton.elim (fun i : Fin 0 => g i.succ) Fin.elim0,
    Subsingleton.elim (Fin.contractNth 0 (fun x1 x2 => x1 * x2) g) Fin.elim0]
  simp [sub_eq_add_neg]

theorem cochains_d_one_apply (f : locallyConstantCochains A 1) (g : Fin 2 → G) :
    (((cochains A).d 1 2).hom f).1 g =
      A.ρ (g 0) (f.1 fun _ => g 1) - f.1 (fun _ => g 0 * g 1) + f.1 (fun _ => g 0) := by
  have h := cochains_d A 1
  simp only [Nat.reduceAdd] at h
  rw [h]
  change (inhomogeneousCochains.d A 1).hom f.1 g = _
  rw [inhomogeneousCochains.d_hom_apply, Fin.sum_univ_two]
  have e1 : (fun i : Fin 1 => g i.succ) = fun _ => g 1 := funext fun i => by
    rw [Subsingleton.elim i 0]; rfl
  have e2 : Fin.contractNth 0 (· * ·) g = fun _ => g 0 * g 1 := funext fun i => by
    rw [Subsingleton.elim i 0, Fin.contractNth_apply_of_eq _ _ _ _ rfl]; rfl
  have e3 : Fin.contractNth 1 (· * ·) g = fun _ => g 0 := funext fun i => by
    rw [Subsingleton.elim i 0, Fin.contractNth_apply_of_lt _ _ _ _ (by simp)]; rfl
  rw [e1, e2, e3]
  simp only [Fin.val_zero, zero_add, pow_one, neg_smul, one_smul, Fin.val_one, Nat.reduceAdd,
    even_two, Even.neg_pow, one_pow]
  abel

omit [IsTopologicalGroup G] in
theorem fin_one_eq_const (g : Fin 1 → G) : g = fun _ => g 0 :=
  funext fun i => by rw [Subsingleton.elim i 0]

theorem cochains_d_one_eq_zero_iff (f : locallyConstantCochains A 1) :
    ((cochains A).d 1 2).hom f = 0 ↔
      ∀ g h : G, f.1 (fun _ => g * h) = f.1 (fun _ => g) + A.ρ g (f.1 fun _ => h) := by
  constructor
  · intro hf g h
    have := congrArg (fun c : locallyConstantCochains A 2 => c.1 ![g, h]) hf
    simp only [cochains_d_one_apply] at this
    change A.ρ g (f.1 fun _ => h) - f.1 (fun _ => g * h) + f.1 (fun _ => g) = 0 at this
    rw [← sub_eq_zero, ← neg_eq_zero, ← this]
    abel
  · intro hf
    apply Subtype.ext
    funext x
    rw [cochains_d_one_apply, hf]
    change _ = (0 : A)
    abel

theorem cocycle_one_apply_one {f : locallyConstantCochains A 1}
    (hf : ((cochains A).d 1 2).hom f = 0) : f.1 (fun _ => 1) = 0 := by
  have := (cochains_d_one_eq_zero_iff A f).1 hf 1 1
  simp only [mul_one, map_one, Module.End.one_apply] at this
  simpa using this

end Formulas

section Conj

variable (A : Rep.{u} k G) [IsSmoothRep A] (N : Subgroup G) [N.Normal]

theorem continuous_conjHom (g : G) : Continuous (conjHom N g) :=
  Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _

noncomputable def cohomologyConj (n : ℕ) (g : G) :
    cohomology (Rep.res N.subtype A) n ⟶ cohomology (Rep.res N.subtype A) n :=
  map ⟨conjHom N g, continuous_conjHom N g⟩
    (conjMor A N g) n

def cohomologyConjInvariants (n : ℕ) : Submodule k (cohomology (Rep.res N.subtype A) n) where
  carrier := {x | ∀ g : G, (cohomologyConj A N n g).hom x = x}
  add_mem' hx hy g := by rw [map_add, hx g, hy g]
  zero_mem' g := map_zero _
  smul_mem' r x hx g := by rw [map_smul, hx g]

noncomputable abbrev cocycleOneApply (z : cocycles (Rep.res N.subtype A) 1) (n : N) : A :=
  (((cochains (Rep.res N.subtype A)).iCycles 1).hom z).1 fun _ => n

theorem cohomologyConj_π_eq_iff (z : cocycles (Rep.res N.subtype A) 1) (g : G) :
    (cohomologyConj A N 1 g).hom ((cohomologyπ _ 1).hom z) = (cohomologyπ _ 1).hom z ↔
      ∃ a : A, ∀ n : N, A.ρ g (cocycleOneApply A N z (conjHom N g n)) -
        cocycleOneApply A N z n = A.ρ n a - a := by
  rw [cohomologyConj, cohomologyπ_map_apply, ← sub_eq_zero, ← map_sub]
  change ((cochains (Rep.res N.subtype A)).homologyπ (0 + 1)).hom _ = 0 ↔ _
  rw [homologyπ_succ_eq_zero_iff, map_sub, iCycles_cyclesMap_apply]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w.1 Fin.elim0, fun n => ?_⟩
    have := congrArg (fun c : locallyConstantCochains (Rep.res N.subtype A) 1 => c.1 fun _ => n) hw
    exact this.symm.trans (cochains_d_zero_apply (Rep.res N.subtype A) w fun _ => n)
  · rintro ⟨a, ha⟩
    refine ⟨⟨fun _ => a, IsLocallyConstant.const _⟩, ?_⟩
    apply Subtype.ext
    funext x
    rw [cochains_d_zero_apply, fin_one_eq_const x]
    exact (ha (x 0)).symm

theorem cocycleOneApply_mul (z : cocycles (Rep.res N.subtype A) 1) (a b : N) :
    cocycleOneApply A N z (a * b) = cocycleOneApply A N z a + A.ρ a (cocycleOneApply A N z b) :=
  (cochains_d_one_eq_zero_iff (Rep.res N.subtype A) _).1
    (iCycles_d_apply _ 1 2 z) a b

noncomputable abbrev cocycleOneApplyG (y : cocycles A 1) (g : G) : A :=
  (((cochains A).iCycles 1).hom y).1 fun _ => g

theorem cocycleOneApplyG_mul (y : cocycles A 1) (a b : G) :
    cocycleOneApplyG A y (a * b) = cocycleOneApplyG A y a + A.ρ a (cocycleOneApplyG A y b) :=
  (cochains_d_one_eq_zero_iff A _).1 (iCycles_d_apply _ 1 2 y) a b

theorem res_mem_cohomologyConjInvariants (h : cohomology A 1) :
    (res A N 1).hom h ∈ cohomologyConjInvariants A N 1 := by
  obtain ⟨y, rfl⟩ := homologyπ_surjective (cochains A) 1 h
  intro g
  rw [res, map]
  erw [homologyMap_homologyπ_apply]
  refine (cohomologyConj_π_eq_iff A N _ g).2 ⟨cocycleOneApplyG A y g, fun n => ?_⟩
  have hY : ∀ n : N, cocycleOneApply A N ((cocyclesMap (subgroupInclusion N) (𝟙 (Rep.res N.subtype A)) 1).hom y) n = cocycleOneApplyG A y n := fun n => by
    simp only [cocycleOneApply, cocyclesMap, iCycles_cyclesMap_apply]
    rfl
  rw [hY, hY]
  have e : (g : G) * (conjHom N g n : G) = n * g := by simp; group
  have h1 := cocycleOneApplyG_mul A y g (conjHom N g n)
  rw [e, cocycleOneApplyG_mul A y n g] at h1
  have h2 : A.ρ g (cocycleOneApplyG A y (conjHom N g n)) =
      cocycleOneApplyG A y n + A.ρ n (cocycleOneApplyG A y g) - cocycleOneApplyG A y g := by
    rw [h1]
    abel
  rw [h2]
  abel

end Conj

end Langlands.ProfiniteCohomology

noncomputable section

namespace Langlands.ProfiniteCohomology

open CategoryTheory

universe u

section Counting

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The classes vanishing on a normal subgroup `N` are as many as `H¹(G/N, A^N)` (inflation is
injective with image the kernel of restriction). -/
theorem card_ker_res_one (A : Rep.{u} k G) [IsSmoothRep A] (N : Subgroup G) [N.Normal] :
    Nat.card (LinearMap.ker (res A N 1).hom) =
      Nat.card (cohomology (A.quotientToInvariants N) 1) := by
  have hmem : ∀ y : cohomology (A.quotientToInvariants N) 1,
      (infl A N 1).hom y ∈ LinearMap.ker (res A N 1).hom := fun y => by
    rw [LinearMap.mem_ker]
    have h := infl_comp_res A N 0
    exact congrArg (fun φ => φ.hom y) h
  refine (Nat.card_congr (Equiv.ofBijective (fun y => (⟨(infl A N 1).hom y, hmem y⟩ :
    LinearMap.ker (res A N 1).hom)) ⟨fun y y' h => infl_one_injective A N
      (congrArg Subtype.val h), fun z => ?_⟩)).symm
  obtain ⟨y, hy⟩ := exists_infl_one_eq A N z.1 z.2
  exact ⟨y, Subtype.ext hy⟩

/-- The `G/N`-invariants of `A^N` are the `G`-invariants of `A`. -/
def invariantsQuotientEquiv (A : Rep.{u} k G) (N : Subgroup G) [N.Normal] :
    (A.quotientToInvariants N).ρ.invariants ≃ A.ρ.invariants where
  toFun x := ⟨((x : A.quotientToInvariants N) : A), fun g => by
    have := x.2 (QuotientGroup.mk g)
    exact congrArg Subtype.val this⟩
  invFun a := ⟨⟨(a : A), fun n => a.2 n⟩, fun q => by
    induction q using QuotientGroup.induction_on with
    | H g => exact Subtype.ext (a.2 g)⟩
  left_inv x := rfl
  right_inv a := rfl

end Counting

end Langlands.ProfiniteCohomology

end
