import Langlands.BushnellKutzko.SplitTypeJacquet.IntegralOrder
import Langlands.Group.GL.IntegralReduction
import Langlands.Representation.Conductor.PrincipalCongruence
import Langlands.Representation.Geometric.WeylDefinitions
import Langlands.Representation.Smooth.Definitions

/-! # Unit groups of standard orders and reduction modulo the maximal ideal

For a block shape `B` of `n = m + 1`, the unit group `J0 F (blkOf B)` of the standard order is
the preimage of the standard parabolic `P_B(k)` under reduction `GL_n(𝔬) → GL_n(k)`, and
`J1 F (blkOf B)` maps into its unipotent radical. The principal congruence subgroup of level one
is the kernel of reduction; on its fixed vectors the action of `GL_n(𝔬)` descends to
`GL_n(k)`. -/

open Matrix ValuativeRel Langlands.GeneralLinear Langlands.Geometric

noncomputable section

namespace Langlands.BushnellKutzko.SplitTypeJacquet

universe uF uV

/-- The block function of a block shape: the block of each coordinate. -/
def blkOf {n : ℕ} (B : BlockShape n) : Fin n → ℕ := fun a => (blockIndex B a : ℕ)

variable {F : Type uF} [Field F] [ValuativeRel F] {m : ℕ}

variable (F m) in
/-- `GL_{m+1}(𝔬)` inside `GL_{m+1}(F)`. -/
abbrev Kint : Subgroup (GL (Fin (m + 1)) F) :=
  Conductor.integralSubgroup (ValuativeRel.valuation F).integer m

theorem mem_Kint_iff (g : GL (Fin (m + 1)) F) :
    g ∈ Kint F m ↔ (∀ a b, valuation F (g a b) ≤ 1) ∧
      (∀ a b, valuation F ((g⁻¹ : GL (Fin (m + 1)) F) a b) ≤ 1) := by
  rw [Conductor.mem_integralSubgroup]
  simp only [Valuation.mem_integer_iff]

theorem J0_le_Kint (blk : Fin (m + 1) → ℕ) : J0 F blk ≤ Kint F m := fun g hg =>
  (mem_Kint_iff g).mpr ⟨fun a b => (hg.1 a b).1, fun a b => (hg.2 a b).1⟩

variable (F m) in
/-- Reduction `GL_{m+1}(𝔬) → GL_{m+1}(k)`. -/
abbrev red : Kint F m →* GeneralLinear (m + 1) 𝓀[F] :=
  IntegralReduction.reduction (ValuativeRel.valuation F).integer m

theorem red_apply (g : Kint F m) (a b : Fin (m + 1))
    (h : (g : GL (Fin (m + 1)) F) a b ∈ (ValuativeRel.valuation F).integer) :
    red F m g a b = IsLocalRing.residue _ ⟨(g : GL (Fin (m + 1)) F) a b, h⟩ := by
  rw [IntegralReduction.reduction_apply]
  congr 1
  apply Subtype.ext
  exact IntegralReduction.integralEquiv_symm_apply_val _ m g a b

theorem residue_eq_zero_iff_val {x : F} (h : x ∈ (ValuativeRel.valuation F).integer) :
    IsLocalRing.residue _ (⟨x, h⟩ : (ValuativeRel.valuation F).integer) = 0 ↔
      valuation F x < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff]
  exact (valuation F).mem_maximalIdeal_iff

theorem red_apply_eq_zero_iff (g : Kint F m) (a b : Fin (m + 1)) :
    red F m g a b = 0 ↔ valuation F ((g : GL (Fin (m + 1)) F) a b) < 1 := by
  have h : (g : GL (Fin (m + 1)) F) a b ∈ (ValuativeRel.valuation F).integer :=
    (Valuation.mem_integer_iff _ _).mpr (((mem_Kint_iff _).mp g.2).1 a b)
  rw [red_apply g a b h, residue_eq_zero_iff_val h]

theorem red_apply_eq_one_apply_iff (g : Kint F m) (a b : Fin (m + 1)) :
    red F m g a b = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝓀[F]) a b ↔
      valuation F ((g : GL (Fin (m + 1)) F) a b - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a b)
        < 1 := by
  have h : (g : GL (Fin (m + 1)) F) a b ∈ (ValuativeRel.valuation F).integer :=
    (Valuation.mem_integer_iff _ _).mpr (((mem_Kint_iff _).mp g.2).1 a b)
  have h1 : (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a b ∈
      (ValuativeRel.valuation F).integer := by
    rw [Valuation.mem_integer_iff]
    by_cases hab : a = b <;> simp [hab, Matrix.one_apply]
  have hsub : (g : GL (Fin (m + 1)) F) a b - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a b ∈
      (ValuativeRel.valuation F).integer := Subring.sub_mem _ h h1
  have hone : (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝓀[F]) a b =
      IsLocalRing.residue _ ⟨(1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a b, h1⟩ := by
    by_cases hab : a = b
    · subst hab
      simp only [Matrix.one_apply_eq]
      rw [← map_one (IsLocalRing.residue _)]
      congr 1
    · simp only [Matrix.one_apply_ne hab]
      rw [← map_zero (IsLocalRing.residue _)]
      congr 1
  rw [red_apply g a b h, hone, ← sub_eq_zero, ← map_sub, ← residue_eq_zero_iff_val hsub]
  rfl

/-- The residue of an integral element, extended by zero to nonintegral elements. -/
def resF (x : F) : 𝓀[F] :=
  if h : valuation F x ≤ 1 then
    IsLocalRing.residue _ (⟨x, (Valuation.mem_integer_iff _ _).mpr h⟩ :
      (ValuativeRel.valuation F).integer)
  else 0

theorem resF_of_le {x : F} (h : valuation F x ≤ 1) :
    resF x = IsLocalRing.residue _ (⟨x, (Valuation.mem_integer_iff _ _).mpr h⟩ :
      (ValuativeRel.valuation F).integer) := by
  simp [resF, h]

theorem resF_add {x y : F} (hx : valuation F x ≤ 1) (hy : valuation F y ≤ 1) :
    resF (x + y) = resF x + resF y := by
  rw [resF_of_le (Valuation.map_add_le _ hx hy), resF_of_le hx, resF_of_le hy, ← map_add]
  rfl

theorem resF_zero : resF (0 : F) = 0 := by
  rw [resF_of_le (by simp)]
  exact map_zero _

theorem resF_one : resF (1 : F) = 1 := by
  rw [resF_of_le (by simp)]
  exact map_one _

theorem resF_eq_zero_iff {x : F} (hx : valuation F x ≤ 1) : resF x = 0 ↔ valuation F x < 1 := by
  rw [resF_of_le hx, residue_eq_zero_iff_val]

theorem resF_one_apply (a b : Fin (m + 1)) :
    resF ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a b) =
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝓀[F]) a b := by
  by_cases hab : a = b
  · subst hab; simp [resF_one]
  · simp [Matrix.one_apply_ne hab, resF_zero]

theorem red_apply_resF (g : Kint F m) (a b : Fin (m + 1)) :
    red F m g a b = resF ((g : GL (Fin (m + 1)) F) a b) := by
  have h := ((mem_Kint_iff _).mp g.2).1 a b
  rw [resF_of_le h, red_apply g a b]

/-- **The unit group of the standard order is the preimage of the standard parabolic.** -/
theorem red_mem_parabolic_iff {B : BlockShape (m + 1)} (g : Kint F m) :
    red F m g ∈ B.parabolic 𝓀[F] ↔ (g : GL (Fin (m + 1)) F) ∈ J0 F (blkOf B) := by
  have key : ∀ g : Kint F m, red F m g ∈ B.parabolic 𝓀[F] →
      InOrd (blkOf B) ((g : GL (Fin (m + 1)) F) : Matrix _ _ F) := by
    intro g hg a b
    refine ⟨((mem_Kint_iff _).mp g.2).1 a b, fun hab => ?_⟩
    rw [← red_apply_eq_zero_iff]
    rw [BlockShape.mem_parabolic_iff] at hg
    have := hg (blockIndex B a) (blockIndex B b) (B.indexEquiv.symm a).2
      (B.indexEquiv.symm b).2 hab
    have ea : B.index (blockIndex B a) (B.indexEquiv.symm a).2 = a :=
      B.indexEquiv.apply_symm_apply a
    have eb : B.index (blockIndex B b) (B.indexEquiv.symm b).2 = b :=
      B.indexEquiv.apply_symm_apply b
    rwa [ea, eb] at this
  constructor
  · intro hg
    refine ⟨key g hg, ?_⟩
    have := key g⁻¹ (by rw [map_inv]; exact (B.parabolic 𝓀[F]).inv_mem hg)
    simpa using this
  · intro hg
    rw [BlockShape.mem_parabolic_iff]
    intro i j a b hij
    rw [red_apply_eq_zero_iff]
    refine (hg.1 _ _).2 ?_
    simp only [blkOf, blockIndex_index]
    exact hij

theorem red_mem_unipotentSubgroup_of_mem_J1 {B : BlockShape (m + 1)} (g : Kint F m)
    (hg : (g : GL (Fin (m + 1)) F) ∈ J1 F (blkOf B)) :
    red F m g ∈ B.unipotentSubgroup 𝓀[F] := by
  rw [BlockShape.mem_unipotentSubgroup_iff]
  refine ⟨(red_mem_parabolic_iff g).mpr hg.1, fun i a b => ?_⟩
  have h1 := (red_apply_eq_one_apply_iff g (B.index i a) (B.index i b)).mpr
    ((hg.2 _ _).2 (by simp [blkOf]))
  rw [h1]
  by_cases hab : a = b
  · subst hab; simp
  · simp [Matrix.one_apply_ne (fun h => hab ((B.index i).injective h)), hab]

theorem coe_one_apply_integer (a b : Fin (m + 1)) :
    (((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (ValuativeRel.valuation F).integer) a b :
      (ValuativeRel.valuation F).integer) : F) =
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a b := by
  by_cases hab : a = b
  · subst hab; simp
  · simp [Matrix.one_apply_ne hab]

theorem red_eq_one_iff (g : Kint F m) :
    red F m g = 1 ↔ ∀ a b, valuation F ((g : GL (Fin (m + 1)) F) a b -
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a b) < 1 := by
  constructor
  · intro h a b
    rw [← red_apply_eq_one_apply_iff, h]
    rfl
  · intro h
    apply Matrix.GeneralLinearGroup.ext
    intro a b
    exact (red_apply_eq_one_apply_iff g a b).mpr (h a b)

/-- The principal congruence subgroup of level one is the kernel of reduction. -/
theorem mem_principalLevel_one_iff (g : GL (Fin (m + 1)) F) :
    g ∈ Conductor.principalLevelSubgroup F m 1 ↔ ∃ h : g ∈ Kint F m, red F m ⟨g, h⟩ = 1 := by
  constructor
  · rintro ⟨g0, hg0, rfl⟩
    refine ⟨⟨g0, rfl⟩, (red_eq_one_iff _).mpr fun a b => ?_⟩
    rw [SetLike.mem_coe, Conductor.mem_integralPrincipalCongruence] at hg0
    have := hg0 a b
    rw [pow_one] at this
    have hv := (valuation F).mem_maximalIdeal_iff.mp this
    simpa [coe_one_apply_integer] using hv
  · rintro ⟨⟨g0, rfl⟩, hred⟩
    refine ⟨g0, ?_, rfl⟩
    rw [SetLike.mem_coe, Conductor.mem_integralPrincipalCongruence]
    intro a b
    rw [pow_one]
    apply (valuation F).mem_maximalIdeal_iff.mpr
    have := (red_eq_one_iff _).mp hred a b
    simpa [coe_one_apply_integer] using this

theorem principalLevel_one_le_Kint :
    Conductor.principalLevelSubgroup F m 1 ≤ Kint F m := fun g hg =>
  ((mem_principalLevel_one_iff g).mp hg).1

/-- The principal congruence subgroup of level one lies in every `J1`. -/
theorem principalLevel_one_le_J1 (blk : Fin (m + 1) → ℕ) :
    Conductor.principalLevelSubgroup F m 1 ≤ J1 F blk := by
  intro g hg
  obtain ⟨h, hred⟩ := (mem_principalLevel_one_iff g).mp hg
  have hsub := (red_eq_one_iff ⟨g, h⟩).mp hred
  have hsub' : ∀ a b, valuation F (((g⁻¹ : GL (Fin (m + 1)) F) : Matrix _ _ F) a b -
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a b) < 1 := by
    have hg' : g⁻¹ ∈ Conductor.principalLevelSubgroup F m 1 :=
      (Conductor.principalLevelSubgroup F m 1).inv_mem hg
    obtain ⟨h', hred'⟩ := (mem_principalLevel_one_iff _).mp hg'
    exact (red_eq_one_iff ⟨_, h'⟩).mp hred'
  exact mem_J1_of_inRad
    (fun a b => by rw [Matrix.sub_apply]; exact ⟨(hsub a b).le, fun _ => hsub a b⟩)
    (fun a b => by rw [Matrix.sub_apply]; exact ⟨(hsub' a b).le, fun _ => hsub' a b⟩)

/-- Reduction-trivial elements are normalized by `GL_{m+1}(𝔬)`. -/
theorem conj_mem_principalLevel_one {g k : GL (Fin (m + 1)) F} (hg : g ∈ Kint F m)
    (hk : k ∈ Conductor.principalLevelSubgroup F m 1) :
    g * k * g⁻¹ ∈ Conductor.principalLevelSubgroup F m 1 := by
  obtain ⟨hkK, hred⟩ := (mem_principalLevel_one_iff k).mp hk
  rw [mem_principalLevel_one_iff]
  refine ⟨(Kint F m).mul_mem ((Kint F m).mul_mem hg hkK) ((Kint F m).inv_mem hg), ?_⟩
  have e : (⟨g * k * g⁻¹, (Kint F m).mul_mem ((Kint F m).mul_mem hg hkK)
      ((Kint F m).inv_mem hg)⟩ : Kint F m) = ⟨g, hg⟩ * ⟨k, hkK⟩ * (⟨g, hg⟩)⁻¹ := rfl
  rw [e, map_mul, map_mul, hred, mul_one, map_inv, mul_inv_cancel]

section Descent

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GL (Fin (m + 1)) F) V)

/-- The vectors fixed by the principal congruence subgroup of level one. -/
abbrev fixK1 : Submodule ℂ V := fixedVectors π (Conductor.principalLevelSubgroup F m 1)

theorem mem_fixK1_iff (x : V) :
    x ∈ fixK1 π ↔ ∀ k ∈ Conductor.principalLevelSubgroup F m 1, π k x = x := by
  constructor
  · intro hx k hk
    exact hx ⟨k, hk⟩
  · intro h k
    exact h k.val k.property

theorem apply_mem_fixK1 {g : GL (Fin (m + 1)) F} (hg : g ∈ Kint F m) {x : V}
    (hx : x ∈ fixK1 π) : π g x ∈ fixK1 π := by
  rw [mem_fixK1_iff] at hx ⊢
  intro k hk
  have hk' : g⁻¹ * k * g ∈ Conductor.principalLevelSubgroup F m 1 := by
    have := conj_mem_principalLevel_one ((Kint F m).inv_mem hg) hk
    simpa using this
  calc π k (π g x) = π g (π (g⁻¹ * k * g) x) := by
        simp only [← Module.End.mul_apply, ← map_mul]; congr 2; group
    _ = π g x := by rw [hx _ hk']

/-- The action of `GL_{m+1}(𝔬)` on the vectors fixed by the principal congruence subgroup. -/
def kintAction : Kint F m →* Module.End ℂ (fixK1 π) where
  toFun g := (π g).restrict (fun x hx => apply_mem_fixK1 π g.2 hx)
  map_one' := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp [Module.End.mul_apply]

theorem ker_red_le_ker_kintAction :
    (red F m).ker ≤ (kintAction π).toHomUnits.ker := by
  intro g hg
  rw [MonoidHom.mem_ker] at hg ⊢
  apply Units.ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have hk : (g : GL (Fin (m + 1)) F) ∈ Conductor.principalLevelSubgroup F m 1 :=
    (mem_principalLevel_one_iff _).mpr ⟨g.2, hg⟩
  exact x.2 ⟨_, hk⟩

/-- The action of `GL_{m+1}(k)` on the vectors fixed by the principal congruence subgroup. -/
def descended : Representation ℂ (GeneralLinear (m + 1) 𝓀[F]) (fixK1 π) :=
  (Units.coeHom (Module.End ℂ (fixK1 π))).comp
    (MonoidHom.liftOfRightInverse (red F m)
      (IntegralReduction.lift (ValuativeRel.valuation F).integer m)
      (fun γ => IntegralReduction.reduction_lift (ValuativeRel.valuation F).integer m γ)
      ⟨(kintAction π).toHomUnits, ker_red_le_ker_kintAction π⟩)

theorem descended_red (g : Kint F m) (x : fixK1 π) :
    ((descended π (red F m g) x : fixK1 π) : V) = π g x := by
  rw [descended, MonoidHom.comp_apply, MonoidHom.liftOfRightInverse_comp_apply]
  rfl

end Descent

end Langlands.BushnellKutzko.SplitTypeJacquet
