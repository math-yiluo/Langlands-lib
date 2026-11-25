import Langlands.Cohomology.Profinite.Coinduced.Quotient
import Langlands.Cohomology.Profinite.Comparison.Continuous
import Langlands.Cohomology.Profinite.InflationRestriction.DegreeOne

namespace Langlands.ProfiniteCohomology

open CategoryTheory

universe u

variable {k G : Type u} [CommRing k] [Group G]

section Algebra

variable (A : Rep.{u} k G) (N : Subgroup G) [N.Normal]

def tgDiff (y : G → A) (g h : G) : A :=
  A.ρ g (y h) - y (g * h) + y g

def IsCocycleOne (x : N → A) : Prop :=
  ∀ a b : N, x (a * b) = x a + A.ρ a (x b)

structure IsTgLift (x : N → A) (y : G → A) : Prop where
  map_one : y 1 = 0
  mul_right : ∀ (g : G) (n : N), y (g * n) = y g + A.ρ g (x n)
  conj : ∀ (h : G) (n : N),
    A.ρ h (x (conjHom N h n)) - x n = A.ρ n (y h) - y h

variable {A N} {x : N → A} {y : G → A}

theorem IsTgLift.mul_left (hy : IsTgLift A N x y) (n : N) (g : G) :
    y (n * g) = A.ρ n (y g) + x n := by
  have e : (n : G) * g = g * (conjHom N g n : G) := by
    simp only [coe_conjHom_apply]; group
  rw [e, hy.mul_right, ← sub_add_cancel (A.ρ g _) (x n), hy.conj]
  abel

theorem IsTgLift.tgDiff_mul_right (hy : IsTgLift A N x y) (g h : G) (n : N) :
    tgDiff A y g (h * n) = tgDiff A y g h := by
  simp only [tgDiff]
  rw [hy.mul_right, ← mul_assoc, hy.mul_right, map_add, ← Module.End.mul_apply, ← map_mul]
  abel

theorem IsTgLift.tgDiff_mul_left (hx : IsCocycleOne A N x) (hy : IsTgLift A N x y) (g : G) (n : N)
    (h : G) : tgDiff A y (g * n) h = tgDiff A y g h := by
  simp only [tgDiff]
  have e : g * n * h = g * h * (conjHom N h n : G) := by simp; group
  rw [e, hy.mul_right, hy.mul_right]
  have hc := hy.conj h n
  have : A.ρ (g * n) (y h) = A.ρ g (A.ρ n (y h)) := by rw [map_mul]; rfl
  rw [this, show A.ρ n (y h) = y h + (A.ρ h (x (conjHom N h n)) - x n) by
    rw [hc]; abel, map_add, map_sub, map_mul (A.ρ) g h, Module.End.mul_apply]
  abel

theorem IsTgLift.tgDiff_mem_invariants (hx : IsCocycleOne A N x) (hy : IsTgLift A N x y)
    (g h : G) (n : N) : A.ρ n (tgDiff A y g h) = tgDiff A y g h := by
  have e1 : tgDiff A y (n * g) h = A.ρ n (tgDiff A y g h) := by
    simp only [tgDiff]
    rw [mul_assoc, hy.mul_left, hy.mul_left, map_mul, Module.End.mul_apply, map_add, map_sub]
    abel
  have e2 : (n : G) * g = g * (conjHom N g n : G) := by
    simp only [coe_conjHom_apply]; group
  rw [← e1, e2, hy.tgDiff_mul_left hx]

theorem IsTgLift.tgDiff_mul_mul (hx : IsCocycleOne A N x) (hy : IsTgLift A N x y) (g h : G)
    (m n : N) : tgDiff A y (g * m) (h * n) = tgDiff A y g h := by
  rw [hy.tgDiff_mul_left hx, hy.tgDiff_mul_right]

end Algebra

section Cochains

variable [TopologicalSpace G] [IsTopologicalGroup G] (A : Rep.{u} k G) [IsSmoothRep A]
  (N : Subgroup G) [N.Normal]

omit [IsTopologicalGroup G] in

def liftCochain {y : G → A} (hy : IsLocallyConstant y) : locallyConstantCochains A 1 :=
  ⟨fun g => y (g 0), hy.comp_continuous (continuous_apply 0)⟩

theorem isLocallyConstant_tgDiff {y : G → A} (hy : IsLocallyConstant y) :
    IsLocallyConstant fun g : Fin 2 → G => tgDiff A y (g 0) (g 1) := by
  have h1 : IsLocallyConstant fun g : Fin 2 → G => A.ρ (g 0) (y (g 1)) :=
    isLocallyConstant_ρ_apply A (continuous_apply 0) (hy.comp_continuous (continuous_apply 1))
  have h2 : IsLocallyConstant fun g : Fin 2 → G => y (g 0 * g 1) :=
    hy.comp_continuous ((continuous_apply 0).mul (continuous_apply 1))
  have h3 : IsLocallyConstant fun g : Fin 2 → G => y (g 0) :=
    hy.comp_continuous (continuous_apply 0)
  exact (h1.sub h2).add h3

theorem cochains_d_liftCochain {y : G → A} (hy : IsLocallyConstant y) (g : Fin 2 → G) :
    (((cochains A).d 1 2).hom (liftCochain A hy)).1 g = tgDiff A y (g 0) (g 1) := by
  rw [cochains_d_one_apply]
  rfl

variable {A N} {x : N → A} {y : G → A}

omit [IsTopologicalGroup G] [IsSmoothRep A] in
theorem IsTgLift.tgDiff_out (hx : IsCocycleOne A N x) (hy : IsTgLift A N x y) (g h : G) :
    tgDiff A y (Quotient.out (g : G ⧸ N)) (Quotient.out (h : G ⧸ N)) = tgDiff A y g h := by
  obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul N g
  obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul N h
  change tgDiff A y (g : G ⧸ N).out (h : G ⧸ N).out = _
  rw [hm, hn, hy.tgDiff_mul_mul hx]

omit [IsTopologicalGroup G] in

noncomputable def tgCochain (hx : IsCocycleOne A N x) (hy : IsTgLift A N x y)
    (hyc : IsLocallyConstant y) : locallyConstantCochains (A.quotientToInvariants N) 2 :=
  ⟨fun c => ⟨tgDiff A y (c 0).out (c 1).out, fun n => hy.tgDiff_mem_invariants hx _ _ n⟩, by
    let q : (Fin 2 → G) → (Fin 2 → G ⧸ N) := Pi.map fun _ => QuotientGroup.mk
    have hq : Topology.IsQuotientMap q :=
      (IsOpenQuotientMap.piMap fun _ => QuotientGroup.isOpenQuotientMap_mk).isQuotientMap
    refine isLocallyConstant_of_comp_isQuotientMap hq ?_
    refine IsLocallyConstant.desc _ Subtype.val ?_ Subtype.val_injective
    have : (Subtype.val ∘ ((fun c : Fin 2 → G ⧸ N => (⟨tgDiff A y (c 0).out (c 1).out,
        fun n => hy.tgDiff_mem_invariants hx _ _ n⟩ :
          Representation.invariants (A.ρ.comp N.subtype))) ∘ q)) =
        fun g : Fin 2 → G => tgDiff A y (g 0) (g 1) := by
      funext g
      exact hy.tgDiff_out hx (g 0) (g 1)
    rw [this]
    exact isLocallyConstant_tgDiff A hyc⟩

variable (A N) in

theorem cochainsMap_mk_injective (n : ℕ) :
    Function.Injective ((cochainsMap (A := A.quotientToInvariants N) (B := A)
      (quotientMap N)
      (Rep.ofHom (A.ρ.quotientToInvariants_lift N))).f n).hom := by
  intro w w' h
  apply Subtype.ext
  funext c
  have := congrFun (congrArg Subtype.val h) fun i => (c i).out
  have hc : (⇑(QuotientGroup.mk' N) ∘ fun i => (c i).out) = c :=
    funext fun i => QuotientGroup.out_eq' (c i)
  change ((w.1 (⇑(QuotientGroup.mk' N) ∘ fun i => (c i).out)) : A) =
    ((w'.1 (⇑(QuotientGroup.mk' N) ∘ fun i => (c i).out)) : A) at this
  rw [hc] at this
  exact Subtype.ext this

theorem cochainsMap_tgCochain (hx : IsCocycleOne A N x) (hy : IsTgLift A N x y)
    (hyc : IsLocallyConstant y) :
    ((cochainsMap (quotientMap N)
      (Rep.ofHom (A.ρ.quotientToInvariants_lift N))).f 2).hom (tgCochain hx hy hyc) =
      ((cochains A).d 1 2).hom (liftCochain A hyc) := by
  apply Subtype.ext
  funext g
  rw [cochains_d_liftCochain]
  exact hy.tgDiff_out hx (g 0) (g 1)

theorem cochains_d_d_apply {B : Rep.{u} k G} [IsSmoothRep B] (i j l : ℕ)
    (v : (cochains B).X i) :
    ((cochains B).d j l).hom (((cochains B).d i j).hom v) = 0 := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, HomologicalComplex.d_comp_d]
  rfl

theorem tgCochain_d (hx : IsCocycleOne A N x) (hy : IsTgLift A N x y) (hyc : IsLocallyConstant y) :
    ((cochains (A.quotientToInvariants N)).d 2 (2 + 1)).hom (tgCochain hx hy hyc) = 0 := by
  apply cochainsMap_mk_injective A N 3
  rw [map_zero]
  refine (hom_f_d_apply _ 2 3 _).trans ?_
  rw [cochainsMap_tgCochain]
  exact cochains_d_d_apply 1 2 3 _

end Cochains

section CocycleOf

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] {B : Rep.{u} k H}
  [IsSmoothRep B]

noncomputable def cocycleOf (n : ℕ) (v : locallyConstantCochains B n)
    (hv : ((cochains B).d n (n + 1)).hom v = 0) : cocycles B n :=
  Classical.choose (exists_iCycles_eq_of_d_eq_zero (cochains B) n v hv)

theorem iCycles_cocycleOf (n : ℕ) (v : locallyConstantCochains B n)
    (hv : ((cochains B).d n (n + 1)).hom v = 0) :
    ((cochains B).iCycles n).hom (cocycleOf n v hv) = v :=
  Classical.choose_spec (exists_iCycles_eq_of_d_eq_zero (cochains B) n v hv)

theorem cocycleOf_eq_iff (n : ℕ) (v : locallyConstantCochains B n)
    (hv : ((cochains B).d n (n + 1)).hom v = 0) (z : cocycles B n) :
    cocycleOf n v hv = z ↔ ((cochains B).iCycles n).hom z = v :=
  ⟨fun h => h ▸ iCycles_cocycleOf n v hv, fun h =>
    iCycles_injective _ n ((iCycles_cocycleOf n v hv).trans h.symm)⟩

theorem cohomologyπ_cocycleOf_eq (n : ℕ) (v v' : locallyConstantCochains B (n + 1))
    (hv : ((cochains B).d (n + 1) (n + 1 + 1)).hom v = 0)
    (hv' : ((cochains B).d (n + 1) (n + 1 + 1)).hom v' = 0)
    (w : locallyConstantCochains B n) (hw : ((cochains B).d n (n + 1)).hom w = v' - v) :
    (cohomologyπ B (n + 1)).hom (cocycleOf (n + 1) v' hv') =
      (cohomologyπ B (n + 1)).hom (cocycleOf (n + 1) v hv) := by
  rw [← sub_eq_zero, ← map_sub]
  refine (homologyπ_succ_eq_zero_iff _ n _).2 ⟨w, ?_⟩
  rw [map_sub, iCycles_cocycleOf, iCycles_cocycleOf]
  exact hw

end CocycleOf

end Langlands.ProfiniteCohomology

namespace Langlands.ProfiniteCohomology

open CategoryTheory

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{u} k G) [IsSmoothRep A] (N : Subgroup G) [N.Normal]

section Class

theorem isCocycleOne_cocycleOneApply (z : cocycles (Rep.res N.subtype A) 1) :
    IsCocycleOne A N (cocycleOneApply A N z) :=
  cocycleOneApply_mul A N z

variable {A N}

noncomputable def tgClass (z : cocycles (Rep.res N.subtype A) 1) {y : G → A}
    (hy : IsTgLift A N (cocycleOneApply A N z) y) (hyc : IsLocallyConstant y) :
    cohomology (A.quotientToInvariants N) 2 :=
  (cohomologyπ _ 2).hom (cocycleOf 2 (tgCochain (isCocycleOne_cocycleOneApply A N z) hy hyc)
    (tgCochain_d _ hy hyc))

omit [IsTopologicalGroup G] in

theorem quotientToInvariants_ρ_apply_coe (c : G ⧸ N) (w : Representation.invariants (A.ρ.comp N.subtype)) :
    (((A.quotientToInvariants N).ρ c w : Representation.invariants (A.ρ.comp N.subtype)) : A) =
      A.ρ c.out w := by
  conv_lhs => rw [← QuotientGroup.out_eq' c]
  rfl

theorem tgClass_eq (z z' : cocycles (Rep.res N.subtype A) 1)
    (hzz : (cohomologyπ _ 1).hom z = (cohomologyπ _ 1).hom z') {y y' : G → A}
    (hy : IsTgLift A N (cocycleOneApply A N z) y) (hyc : IsLocallyConstant y)
    (hy' : IsTgLift A N (cocycleOneApply A N z') y') (hyc' : IsLocallyConstant y') :
    tgClass z hy hyc = tgClass z' hy' hyc' := by

  have h0 : (cohomologyπ _ (0 + 1)).hom (z' - z) = 0 := by
    rw [map_sub, ← hzz, sub_self]
  obtain ⟨w, hw⟩ := (homologyπ_succ_eq_zero_iff _ 0 _).1 h0
  set a : A := w.1 Fin.elim0
  have ha : ∀ n : N, cocycleOneApply A N z' n - cocycleOneApply A N z n = A.ρ n a - a := by
    intro n
    have := congrArg (fun c : locallyConstantCochains (Rep.res N.subtype A) 1 => c.1 fun _ => n) hw
    simp only [map_sub] at this
    exact this.symm.trans (cochains_d_zero_apply (Rep.res N.subtype A) w fun _ => n)

  set V : G → A := fun g => y' g - y g - (A.ρ g a - a)
  have hVr : ∀ (g : G) (n : N), V (g * n) = V g := by
    intro g n
    simp only [V, hy.mul_right, hy'.mul_right, map_mul, Module.End.mul_apply]
    rw [show cocycleOneApply A N z' n = cocycleOneApply A N z n + (A.ρ n a - a) by
      rw [← ha]; abel, map_add, map_sub]
    abel
  have hVi : ∀ (h : G) (n : N), A.ρ n (V h) = V h := by
    intro h n
    have c1 := hy.conj h n
    have c2 := hy'.conj h n
    rw [show cocycleOneApply A N z' (conjHom N h n) =
      cocycleOneApply A N z (conjHom N h n) +
        (A.ρ (conjHom N h n) a - a) by rw [← ha]; abel,
      show cocycleOneApply A N z' n = cocycleOneApply A N z n + (A.ρ n a - a) by rw [← ha]; abel,
      map_add, map_sub, ← Module.End.mul_apply, ← map_mul,
      coe_conjHom_apply] at c2
    simp only [V, map_sub, ← Module.End.mul_apply, ← map_mul]
    rw [show h * (h⁻¹ * (n : G) * h) = n * h by group] at c2
    rw [← sub_eq_zero]
    have e : A.ρ n (y' h) - y' h = A.ρ n (y h) - y h + (A.ρ (n * h) a - A.ρ h a - (A.ρ n a - a)) := by
      rw [← c1, ← c2]; abel
    rw [show A.ρ (n : G) (y' h) = y' h + (A.ρ n (y h) - y h + (A.ρ (n * h) a - A.ρ h a -
      (A.ρ n a - a))) by rw [← e]; abel]
    simp only [Module.End.mul_apply, map_mul]
    abel
  have hVc : IsLocallyConstant V :=
    (hyc'.sub hyc).sub ((isLocallyConstant_apply A a).sub (IsLocallyConstant.const a))
  have hVeq : ∀ g g' : G, (g : G ⧸ N) = g' → V g = V g' := by
    intro g g' h
    have hm : g⁻¹ * g' ∈ N := QuotientGroup.eq.mp h
    rw [show g' = g * ((⟨g⁻¹ * g', hm⟩ : N) : G) by simp, hVr]
  let W : locallyConstantCochains (A.quotientToInvariants N) 1 :=
    ⟨fun c => ⟨V (c 0).out, fun n => hVi _ n⟩, by
      let q : (Fin 1 → G) → (Fin 1 → G ⧸ N) := Pi.map fun _ => QuotientGroup.mk
      have hq : Topology.IsQuotientMap q :=
        (IsOpenQuotientMap.piMap fun _ => QuotientGroup.isOpenQuotientMap_mk).isQuotientMap
      refine isLocallyConstant_of_comp_isQuotientMap hq ?_
      refine IsLocallyConstant.desc _ Subtype.val ?_ Subtype.val_injective
      have : (Subtype.val ∘ ((fun c : Fin 1 → G ⧸ N => (⟨V (c 0).out, fun n => hVi _ n⟩ :
          Representation.invariants (A.ρ.comp N.subtype))) ∘ q)) = fun g : Fin 1 → G => V (g 0) := by
        funext g
        exact hVeq _ _ (QuotientGroup.out_eq' _)
      rw [this]
      exact hVc.comp_continuous (continuous_apply 0)⟩
  have hW : ((cochains (A.quotientToInvariants N)).d 1 (1 + 1)).hom W =
      tgCochain (isCocycleOne_cocycleOneApply A N z') hy' hyc' -
        tgCochain (isCocycleOne_cocycleOneApply A N z) hy hyc := by
    apply Subtype.ext
    funext c
    apply Subtype.ext
    have hd := congrArg Subtype.val (cochains_d_one_apply (A.quotientToInvariants N) W c)
    refine hd.trans ?_
    have hq : ∀ (c : G ⧸ N) (w : Representation.invariants (A.ρ.comp N.subtype)),
        ((A.ρ.quotientToInvariants N c w : Representation.invariants (A.ρ.comp N.subtype)) : A) =
          A.ρ c.out w := fun c w => quotientToInvariants_ρ_apply_coe c w
    simp only [Submodule.coe_add, Submodule.coe_sub]
    rw [hq]
    change A.ρ (c 0).out (V (c 1).out) - V (c 0 * c 1).out + V (c 0).out =
      tgDiff A y' (c 0).out (c 1).out - tgDiff A y (c 0).out (c 1).out
    rw [hVeq (c 0 * c 1).out ((c 0).out * (c 1).out) (by
      rw [QuotientGroup.mk_mul, QuotientGroup.out_eq', QuotientGroup.out_eq', QuotientGroup.out_eq'])]
    simp only [V, tgDiff, map_sub, map_mul, Module.End.mul_apply]
    abel
  exact (cohomologyπ_cocycleOf_eq 1 _ _ _ _ W hW).symm

theorem cocycleOneApply_add (z z' : cocycles (Rep.res N.subtype A) 1) :
    cocycleOneApply A N (z + z') = cocycleOneApply A N z + cocycleOneApply A N z' := by
  funext n
  simp only [cocycleOneApply, map_add]
  rfl

theorem cocycleOneApply_smul (r : k) (z : cocycles (Rep.res N.subtype A) 1) :
    cocycleOneApply A N (r • z) = r • cocycleOneApply A N z := by
  funext n
  simp only [cocycleOneApply, map_smul]
  rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] [IsSmoothRep A] in
theorem IsTgLift.add {x x' : N → A} {y y' : G → A} (hy : IsTgLift A N x y)
    (hy' : IsTgLift A N x' y') : IsTgLift A N (x + x') (y + y') where
  map_one := by simp [hy.map_one, hy'.map_one]
  mul_right g n := by
    simp only [Pi.add_apply, hy.mul_right, hy'.mul_right, map_add]
    abel
  conj h n := by
    simp only [Pi.add_apply, map_add]
    rw [show A.ρ h (x _) + A.ρ h (x' _) - (x n + x' n) =
      (A.ρ h (x (conjHom N h n)) - x n) +
        (A.ρ h (x' (conjHom N h n)) - x' n) by abel, hy.conj, hy'.conj]
    abel

omit [TopologicalSpace G] [IsTopologicalGroup G] [IsSmoothRep A] in
theorem IsTgLift.smul (r : k) {x : N → A} {y : G → A} (hy : IsTgLift A N x y) :
    IsTgLift A N (r • x) (r • y) where
  map_one := by simp [hy.map_one]
  mul_right g n := by
    simp only [Pi.smul_apply, hy.mul_right, map_smul, smul_add]
  conj h n := by
    simp only [Pi.smul_apply, map_smul]
    rw [← smul_sub, hy.conj, smul_sub]

theorem tgClass_add (z z' : cocycles (Rep.res N.subtype A) 1) {y y' : G → A}
    (hy : IsTgLift A N (cocycleOneApply A N z) y) (hyc : IsLocallyConstant y)
    (hy' : IsTgLift A N (cocycleOneApply A N z') y') (hyc' : IsLocallyConstant y')
    (hs : IsTgLift A N (cocycleOneApply A N (z + z')) (y + y')) :
    tgClass (z + z') hs (hyc.add hyc') = tgClass z hy hyc + tgClass z' hy' hyc' := by
  simp only [tgClass]
  rw [← map_add]
  congr 1
  rw [cocycleOf_eq_iff, map_add, iCycles_cocycleOf, iCycles_cocycleOf]
  apply Subtype.ext
  funext c
  apply Subtype.ext
  change tgDiff A y _ _ + tgDiff A y' _ _ = tgDiff A (y + y') _ _
  simp only [tgDiff, Pi.add_apply, map_add]
  abel

theorem tgClass_smul (r : k) (z : cocycles (Rep.res N.subtype A) 1) {y : G → A}
    (hy : IsTgLift A N (cocycleOneApply A N z) y) (hyc : IsLocallyConstant y)
    (hs : IsTgLift A N (cocycleOneApply A N (r • z)) (r • y)) :
    tgClass (r • z) hs (hyc.comp (r • ·)) = r • tgClass z hy hyc := by
  simp only [tgClass]
  rw [← map_smul]
  congr 1
  rw [cocycleOf_eq_iff, map_smul, iCycles_cocycleOf]
  apply Subtype.ext
  funext c
  apply Subtype.ext
  change r • tgDiff A y _ _ = tgDiff A (r • y) _ _
  simp only [tgDiff, Pi.smul_apply, map_smul, smul_add, smul_sub]

variable (A N) in

def IsTransgression (h : cohomology (Rep.res N.subtype A) 1)
    (t : cohomology (A.quotientToInvariants N) 2) : Prop :=
  ∃ (z : cocycles (Rep.res N.subtype A) 1) (y : G → A)
    (hy : IsTgLift A N (cocycleOneApply A N z) y) (hyc : IsLocallyConstant y),
    (cohomologyπ _ 1).hom z = h ∧ tgClass z hy hyc = t

theorem IsTransgression.unique {h : cohomology (Rep.res N.subtype A) 1}
    {t t' : cohomology (A.quotientToInvariants N) 2} (ht : IsTransgression A N h t)
    (ht' : IsTransgression A N h t') : t = t' := by
  obtain ⟨z, y, hy, hyc, hz, rfl⟩ := ht
  obtain ⟨z', y', hy', hyc', hz', rfl⟩ := ht'
  exact tgClass_eq z z' (hz.trans hz'.symm) hy hyc hy' hyc'

theorem IsTransgression.add {h h' : cohomology (Rep.res N.subtype A) 1}
    {t t' : cohomology (A.quotientToInvariants N) 2} (ht : IsTransgression A N h t)
    (ht' : IsTransgression A N h' t') : IsTransgression A N (h + h') (t + t') := by
  obtain ⟨z, y, hy, hyc, hz, rfl⟩ := ht
  obtain ⟨z', y', hy', hyc', hz', rfl⟩ := ht'
  have hs : IsTgLift A N (cocycleOneApply A N (z + z')) (y + y') := by
    rw [cocycleOneApply_add]
    exact hy.add hy'
  exact ⟨z + z', y + y', hs, hyc.add hyc', by rw [map_add, hz, hz'],
    tgClass_add z z' hy hyc hy' hyc' hs⟩

theorem IsTransgression.smul (r : k) {h : cohomology (Rep.res N.subtype A) 1}
    {t : cohomology (A.quotientToInvariants N) 2} (ht : IsTransgression A N h t) :
    IsTransgression A N (r • h) (r • t) := by
  obtain ⟨z, y, hy, hyc, hz, rfl⟩ := ht
  have hs : IsTgLift A N (cocycleOneApply A N (r • z)) (r • y) := by
    rw [cocycleOneApply_smul]
    exact hy.smul r
  exact ⟨r • z, r • y, hs, hyc.comp (r • ·), by rw [map_smul, hz], tgClass_smul r z hy hyc hs⟩

end Class

section Existence

variable [CompactSpace G] [TotallyDisconnectedSpace G]

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
theorem isLocallyConstant_cocycleOneApply (z : cocycles (Rep.res N.subtype A) 1) :
    IsLocallyConstant (cocycleOneApply A N z) :=
  (((cochains (Rep.res N.subtype A)).iCycles 1).hom z).2.comp_continuous
    (continuous_pi fun _ => continuous_id)

theorem exists_isTgLift (hN : IsClosed (N : Set G)) (z : cocycles (Rep.res N.subtype A) 1)
    (hz : (cohomologyπ _ 1).hom z ∈ cohomologyConjInvariants A N 1) :
    ∃ y : G → A, IsTgLift A N (cocycleOneApply A N z) y ∧ IsLocallyConstant y := by
  set X := cocycleOneApply A N z with hXdef
  have hXlc : IsLocallyConstant X := isLocallyConstant_cocycleOneApply A N z
  have hXc : IsCocycleOne A N X := isCocycleOne_cocycleOneApply A N z
  have hX1 : X 1 = 0 := by
    have := hXc 1 1
    simpa using this
  obtain ⟨s, hs, hsec, hs1⟩ := exists_continuous_section N hN
  have : CompactSpace N := isCompact_iff_compactSpace.mp hN.isCompact
  let φ : G ⧸ N → N → A := fun c n =>
    A.ρ (s c) (X (conjHom N (s c) n)) - X n
  let S : G ⧸ N → Set A := fun c => {a | ∀ n, φ c n = A.ρ n a - a}
  have hne : ∀ c, ∃ a, a ∈ S c := fun c => (cohomologyConj_π_eq_iff A N z (s c)).1 (hz (s c))
  let b₀ : G ⧸ N → A := fun c => Classical.epsilon fun a => a ∈ S c
  have hb₀ : ∀ c, b₀ c ∈ S c := fun c => Classical.epsilon_spec (hne c)
  have hΦ : IsLocallyConstant fun p : (G ⧸ N) × N => φ p.1 p.2 := by
    have hconj : Continuous fun p : (G ⧸ N) × N => conjHom N (s p.1) p.2 :=
      Continuous.subtype_mk (((hs.comp continuous_fst).inv.mul
        (continuous_subtype_val.comp continuous_snd)).mul (hs.comp continuous_fst)) _
    exact (isLocallyConstant_ρ_apply A (hs.comp continuous_fst)
      (hXlc.comp_continuous hconj)).sub (hXlc.comp_continuous continuous_snd)
  have hφ : ∀ c₀, ∀ᶠ c in nhds c₀, φ c = φ c₀ := by
    intro c₀
    have key := (isCompact_univ : IsCompact (Set.univ : Set N)).eventually_forall_of_forall_eventually
      (x₀ := c₀) (P := fun c n => φ c n = φ c₀ n) fun n _ => by
        have h1 := hΦ.eventually_eq (c₀, n)
        have h2 : ∀ᶠ p in nhds (c₀, n), φ c₀ p.2 = φ c₀ n :=
          (continuous_snd.tendsto (c₀, n)).eventually
            ((hΦ.comp_continuous (continuous_const.prodMk continuous_id)).eventually_eq n)
        filter_upwards [h1, h2] with p hp1 hp2
        exact hp1.trans hp2.symm
    filter_upwards [key] with c hc
    funext n
    exact hc n (Set.mem_univ n)
  have hb₀lc : IsLocallyConstant b₀ := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro c₀
    filter_upwards [hφ c₀] with c hc
    simp only [b₀, S, hc]
  let b : G ⧸ N → A := fun c => b₀ c - b₀ 1
  have hφ1 : ∀ n, φ 1 n = 0 := by
    intro n
    have e : conjHom N 1 n = n := Subtype.ext (by simp)
    simp only [φ, hs1, e, map_one, Module.End.one_apply, sub_self]
  have hb : ∀ c n, φ c n = A.ρ n (b c) - b c := by
    intro c n
    have h1 := hb₀ c n
    have h2 := hb₀ 1 n
    rw [hφ1] at h2
    simp only [b, map_sub]
    rw [h1, ← sub_eq_zero]
    rw [show A.ρ (n : G) (b₀ c) - b₀ c - (A.ρ n (b₀ c) - A.ρ n (b₀ 1) - (b₀ c - b₀ 1)) =
      A.ρ n (b₀ 1) - b₀ 1 by abel, ← h2]
  have hr1 : sectionRetraction N hsec 1 = 1 :=
    Subtype.ext (by rw [coe_sectionRetraction, QuotientGroup.mk_one, hs1]; simp)
  refine ⟨fun g => b g + A.ρ (s g) (X (sectionRetraction N hsec g)), ⟨?_, ?_, ?_⟩, ?_⟩
  · simp [b, hs1, hr1, hX1]
  · intro g n
    beta_reduce
    rw [mk_mul_mem N g n, sectionRetraction_mul N hsec, hXc, map_add, ← Module.End.mul_apply,
      ← map_mul, section_mul_sectionRetraction N hsec]
    abel
  · intro h n
    set c : G ⧸ N := (h : G ⧸ N) with hcdef
    set m : N := sectionRetraction N hsec h with hmdef
    have hh : s c * (m : G) = h := section_mul_sectionRetraction N hsec h
    set n' : N := conjHom N (s c) n with hn'def
    have F1 : conjHom N h n = conjHom N m n' :=
      Subtype.ext (by simp only [coe_conjHom_apply, hn'def]; rw [← hh]; group)
    have e : m * conjHom N m n' = n' * m :=
      Subtype.ext (by simp only [Subgroup.coe_mul, coe_conjHom_apply]; group)
    have F2 := hXc m (conjHom N m n')
    rw [e, hXc n' m] at F2
    have F2' : A.ρ m (X (conjHom N m n')) = X n' + A.ρ n' (X m) - X m := by
      rw [F2]; abel
    have F3 := hb c n
    have F4 : s c * (n' : G) = n * s c := by
      simp only [hn'def, coe_conjHom_apply]; group
    show A.ρ h (X (conjHom N h n)) - X n =
      A.ρ n (b c + A.ρ (s c) (X m)) - (b c + A.ρ (s c) (X m))
    rw [F1, ← hh, map_mul, Module.End.mul_apply, F2', map_sub, map_add,
      ← Module.End.mul_apply (A.ρ (s c)) (A.ρ n'), ← map_mul, F4, map_mul, Module.End.mul_apply]
    have F3' : A.ρ (s c) (X n') = X n + (A.ρ n (b c) - b c) := by
      rw [← F3]; simp only [φ, hn'def]; abel
    rw [F3', map_add]
    abel
  · exact ((hb₀lc.sub (IsLocallyConstant.const _)).comp_continuous
      QuotientGroup.continuous_mk).add
      (isLocallyConstant_ρ_apply A (hs.comp QuotientGroup.continuous_mk)
        (hXlc.comp_continuous (continuous_sectionRetraction N hs hsec)))

theorem exists_isTransgression (hN : IsClosed (N : Set G)) (h : cohomology (Rep.res N.subtype A) 1)
    (hh : h ∈ cohomologyConjInvariants A N 1) : ∃ t, IsTransgression A N h t := by
  obtain ⟨z, rfl⟩ := homologyπ_surjective (cochains (Rep.res N.subtype A)) 1 h
  obtain ⟨y, hy, hyc⟩ := exists_isTgLift A N hN z hh
  exact ⟨tgClass z hy hyc, z, y, hy, hyc, rfl, rfl⟩

noncomputable def transgression (hN : IsClosed (N : Set G)) :
    cohomologyConjInvariants A N 1 →ₗ[k] cohomology (A.quotientToInvariants N) 2 where
  toFun h := Classical.choose (exists_isTransgression A N hN h.1 h.2)
  map_add' h h' :=
    (Classical.choose_spec (exists_isTransgression A N hN (h + h').1 (h + h').2)).unique
      ((Classical.choose_spec (exists_isTransgression A N hN h.1 h.2)).add
        (Classical.choose_spec (exists_isTransgression A N hN h'.1 h'.2)))
  map_smul' r h :=
    (Classical.choose_spec (exists_isTransgression A N hN (r • h).1 (r • h).2)).unique
      ((Classical.choose_spec (exists_isTransgression A N hN h.1 h.2)).smul r)

theorem isTransgression_transgression (hN : IsClosed (N : Set G))
    (h : cohomologyConjInvariants A N 1) : IsTransgression A N h (transgression A N hN h) :=
  Classical.choose_spec (exists_isTransgression A N hN h.1 h.2)

theorem transgression_eq_iff (hN : IsClosed (N : Set G)) (h : cohomologyConjInvariants A N 1)
    (t : cohomology (A.quotientToInvariants N) 2) :
    transgression A N hN h = t ↔ IsTransgression A N h t :=
  ⟨fun e => e ▸ isTransgression_transgression A N hN h,
    fun ht => (isTransgression_transgression A N hN h).unique ht⟩

end Existence

end Langlands.ProfiniteCohomology
