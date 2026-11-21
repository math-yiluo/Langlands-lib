import Langlands.BushnellKutzko.CriticalDerivedReduction
import Langlands.BushnellKutzko.LatticeChainLayers
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-! # Filtered calculations for the critical derived lift -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.CriticalDerived

universe uO uF uV uR uE

section Basic

variable {O : Type uO} {F : Type uF} {V : Type uV} [CommRing O] [Field F]
  [Algebra O F] [AddCommGroup V] [Module O V] [Module F V] [IsScalarTower O F V]
  (𝓛 : LatticeChain O F V)

local notation "P" => 𝓛.endFiltration
local notation "L" => 𝓛.lattice

/-- Two representatives determine the same homogeneous symbol in degree `d`. -/
def SymbolEq (d : ℤ) (x y : Module.End F V) : Prop :=
  x ∈ P d ∧ y ∈ P d ∧ x - y ∈ P (d + 1)

/-- A unit and its inverse lie in the two opposite filtration degrees. -/
def Shifts (d : ℤ) (g : (Module.End F V)ˣ) : Prop :=
  (g : Module.End F V) ∈ P d ∧ (↑(g⁻¹) : Module.End F V) ∈ P (-d)

variable {𝓛} {d e : ℤ} {x y z x' y' : Module.End F V}

namespace SymbolEq

theorem refl (hx : x ∈ P d) : SymbolEq 𝓛 d x x :=
  ⟨hx, hx, by simp⟩

theorem symm (h : SymbolEq 𝓛 d x y) : SymbolEq 𝓛 d y x :=
  ⟨h.2.1, h.1, by simpa only [neg_sub] using neg_mem h.2.2⟩

theorem trans (h : SymbolEq 𝓛 d x y) (h' : SymbolEq 𝓛 d y z) : SymbolEq 𝓛 d x z :=
  ⟨h.1, h'.2.1, by simpa only [sub_add_sub_cancel] using add_mem h.2.2 h'.2.2⟩

theorem add (h : SymbolEq 𝓛 d x y) (h' : SymbolEq 𝓛 d x' y') : SymbolEq 𝓛 d (x + x') (y + y') :=
  ⟨add_mem h.1 h'.1, add_mem h.2.1 h'.2.1, by
    rw [show x + x' - (y + y') = (x - y) + (x' - y') by abel]
    exact add_mem h.2.2 h'.2.2⟩

theorem mul (h : SymbolEq 𝓛 d x y) (h' : SymbolEq 𝓛 e x' y') : SymbolEq 𝓛 (d + e) (x * x') (y * y') := by
  refine ⟨𝓛.mul_mem_endFiltration h.1 h'.1, 𝓛.mul_mem_endFiltration h.2.1 h'.2.1, ?_⟩
  rw [show x * x' - y * y' = (x - y) * x' + y * (x' - y') by noncomm_ring]
  have h₁ := 𝓛.mul_mem_endFiltration h.2.2 h'.1
  have h₂ := 𝓛.mul_mem_endFiltration h.2.1 h'.2.2
  rw [show d + 1 + e = d + e + 1 by omega] at h₁
  rw [← add_assoc] at h₂
  exact add_mem h₁ h₂

theorem sum {I : Type*} (s : Finset I) {f g : I → Module.End F V}
    (h : ∀ i ∈ s, SymbolEq 𝓛 d (f i) (g i)) : SymbolEq 𝓛 d (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact refl (zero_mem _)
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem lowerDepth (h : x ∈ P d) (hy : y ∈ P e) (hde : d < e) : SymbolEq 𝓛 d (x + y) x := by
  have hy' := 𝓛.endFiltration_antitone (show d + 1 ≤ e by omega) hy
  exact ⟨add_mem h (𝓛.endFiltration_antitone (by omega) hy'), h, by simpa only [add_sub_cancel_left] using hy'⟩

theorem not_mem_succ (h : SymbolEq 𝓛 d x y) (hy : y ∉ P (d + 1)) : x ∉ P (d + 1) := by
  intro hx
  exact hy (by simpa only [sub_sub_cancel] using sub_mem hx h.2.2)

end SymbolEq

namespace Shifts

variable {g h : (Module.End F V)ˣ}

theorem mem_lattice_iff (hg : Shifts 𝓛 d g) (i : ℤ) (v : V) :
    (g : Module.End F V) v ∈ L (i + d) ↔ v ∈ L i := by
  refine ⟨fun hv => ?_, hg.1 i v⟩
  have hh := hg.2 (i + d) _ hv
  simpa only [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply, add_neg_cancel_right] using hh

theorem map_lattice (hg : Shifts 𝓛 d g) (i : ℤ) :
    (L i).map ((g : Module.End F V).restrictScalars O) = L (i + d) := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact (hg.mem_lattice_iff i v).mpr hv
  · intro v hv
    let w := (↑(g⁻¹) : Module.End F V) v
    have hw : (g : Module.End F V) w = v := by
      simp only [w, ← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply]
    exact ⟨w, (hg.mem_lattice_iff i w).mp (hw.symm ▸ hv), hw⟩

theorem mem_stabilizer (hg : Shifts 𝓛 d g) : g ∈ 𝓛.stabilizer :=
  𝓛.mem_stabilizer.mpr fun i => ⟨i + d, hg.map_lattice i⟩

theorem not_mem_succ (hg : Shifts 𝓛 d g) : (g : Module.End F V) ∉ P (d + 1) := by
  intro h
  apply (𝓛.lattice_succ_lt 0).not_ge
  intro v hv
  apply (hg.mem_lattice_iff 1 v).mp
  simpa only [zero_add, add_comm d 1] using h 0 v hv

theorem of_stabilizer (g : 𝓛.stabilizer) : Shifts 𝓛 (𝓛.stabilizerValuation g) g.val := by
  refine ⟨fun i v hv => (𝓛.mem_lattice_stabilizer_iff g i v).mpr hv, fun i v hv => ?_⟩
  apply (𝓛.mem_lattice_stabilizer_iff g _ _).mp
  simpa only [← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply, add_neg_cancel_right,
    neg_add_cancel_right] using hv

theorem stabilizerValuation_eq (hg : Shifts 𝓛 d g) :
    𝓛.stabilizerValuation ⟨g, hg.mem_stabilizer⟩ = d := by
  apply add_left_cancel (a := (0 : ℤ))
  apply 𝓛.injective
  rw [← 𝓛.map_lattice_stabilizer ⟨g, hg.mem_stabilizer⟩, hg.map_lattice]

theorem one : Shifts 𝓛 0 (1 : (Module.End F V)ˣ) := by
  constructor <;> intro i v hv <;> simpa only [inv_one, Units.val_one, Module.End.one_apply,
    neg_zero, add_zero] using hv

theorem mul (hg : Shifts 𝓛 d g) (hh : Shifts 𝓛 e h) : Shifts 𝓛 (d + e) (g * h) := by
  refine ⟨𝓛.mul_mem_endFiltration hg.1 hh.1, ?_⟩
  rw [mul_inv_rev, Units.val_mul, neg_add_rev]
  exact 𝓛.mul_mem_endFiltration hh.2 hg.2

theorem inv (hg : Shifts 𝓛 d g) : Shifts 𝓛 (-d) g⁻¹ :=
  ⟨hg.2, by simpa only [neg_neg, inv_inv] using hg.1⟩

theorem pow (hg : Shifts 𝓛 d g) (n : ℕ) : Shifts 𝓛 ((n : ℤ) * d) (g ^ n) := by
  induction n with
  | zero => simpa only [Nat.cast_zero, zero_mul, pow_zero] using (one (𝓛 := 𝓛))
  | succ n ih => simpa only [pow_succ, Nat.cast_succ, add_mul, one_mul] using ih.mul hg

theorem zpow (hg : Shifts 𝓛 d g) (n : ℤ) : Shifts 𝓛 (n * d) (g ^ n) := by
  cases n with
  | ofNat n => exact hg.pow n
  | negSucc n =>
    rw [show Int.negSucc n = -((n + 1 : ℕ) : ℤ) by simp [Int.negSucc_eq], neg_mul, zpow_neg,
      zpow_natCast]
    exact (hg.pow (n + 1)).inv

end Shifts

namespace SymbolEq

variable {g h : (Module.End F V)ˣ}

theorem inv (hg : Shifts 𝓛 d g) (hh : Shifts 𝓛 d h)
    (hgh : SymbolEq 𝓛 d (g : Module.End F V) h) :
    SymbolEq 𝓛 (-d) (↑(g⁻¹) : Module.End F V) (↑(h⁻¹) : Module.End F V) := by
  refine ⟨hg.2, hh.2, ?_⟩
  have heq : (↑(g⁻¹) : Module.End F V) - (↑(h⁻¹) : Module.End F V) =
      (↑(g⁻¹) : Module.End F V) * -((g : Module.End F V) - (h : Module.End F V)) * (↑(h⁻¹) : Module.End F V) := by
    simp only [neg_sub, mul_sub, sub_mul, ← Units.val_mul]
    rw [mul_assoc g⁻¹ h h⁻¹, mul_inv_cancel, mul_one, inv_mul_cancel, one_mul]
  rw [heq]
  have hm := 𝓛.mul_mem_endFiltration (𝓛.mul_mem_endFiltration hg.2 (neg_mem hgh.2.2)) hh.2
  rwa [show -d + (d + 1) + -d = -d + 1 by omega] at hm

theorem pow (hxy : SymbolEq 𝓛 d x y) (n : ℕ) :
    SymbolEq 𝓛 ((n : ℤ) * d) (x ^ n) (y ^ n) := by
  induction n with
  | zero =>
    simpa only [Nat.cast_zero, zero_mul, pow_zero, Units.val_one] using (refl (Shifts.one (𝓛 := 𝓛)).1)
  | succ n ih => simpa only [pow_succ, Nat.cast_succ, add_mul, one_mul] using ih.mul hxy

theorem unit_pow (hgh : SymbolEq 𝓛 d (g : Module.End F V) h) (n : ℕ) :
    SymbolEq 𝓛 ((n : ℤ) * d) ↑(g ^ n) ↑(h ^ n) := by
  simpa only [Units.val_pow_eq_pow_val] using hgh.pow n

theorem zpow (hg : Shifts 𝓛 d g) (hh : Shifts 𝓛 d h) (hgh : SymbolEq 𝓛 d (g : Module.End F V) h)
    (n : ℤ) : SymbolEq 𝓛 (n * d) ↑(g ^ n) ↑(h ^ n) := by
  cases n with
  | ofNat n => exact hgh.unit_pow n
  | negSucc n =>
    rw [show Int.negSucc n = -((n + 1 : ℕ) : ℤ) by simp [Int.negSucc_eq], neg_mul, zpow_neg,
      zpow_natCast, zpow_neg, zpow_natCast]
    exact (hgh.unit_pow (n + 1)).inv (hg.pow _) (hh.pow _)

end SymbolEq

end Basic

section Restrict

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {V : Type uV} [AddCommGroup V] [Module F V] (𝓛 : LatticeChain 𝒪[F] F V)
  {E : Type uE} [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]

/-- Restriction preserves compositions and units. -/
def restrictEnd : Module.End E V →+* Module.End F V where
  toFun f := f.restrictScalars F
  map_one' := rfl
  map_zero' := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
@[simp] theorem restrictEnd_apply (f : Module.End E V) : restrictEnd f = f.restrictScalars F := rfl

/-- A nonzero vector has a largest depth. -/
theorem exists_exact_lattice_depth {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {v : V} (hv : v ≠ 0) :
    ∃ i : ℤ, StratumEquivalence.ExactDepth 𝓛 v i := by
  let C : Set ℤ := {i | v ∈ 𝓛.lattice i}
  have hne : C.Nonempty := 𝓛.exists_lattice_depth hϖ v
  have hsep : ∃ i, v ∉ 𝓛.lattice i := by
    by_contra! h
    exact hv (𝓛.lattice_eq_zero_of_forall h)
  obtain ⟨i, hi⟩ := hsep
  have hbdd : BddAbove C := ⟨i, fun j hj => le_of_not_ge fun hij => hi (𝓛.antitone hij hj)⟩
  refine ⟨sSup C, Int.csSup_mem hne hbdd, fun h => ?_⟩
  have hle := le_csSup hbdd (show sSup C + 1 ∈ C from h)
  omega

variable {R : Type uR} [CommRing R] [Algebra R E] [Module R V] [IsScalarTower R E V]
  (𝓒 : LatticeChain R E V) (hlat : ∀ i, (𝓒.lattice i : Set V) = 𝓛.lattice i)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
include hlat in
theorem symbolEq_restrict {d : ℤ} {x y : Module.End E V} :
    SymbolEq 𝓛 d (restrictEnd x) (restrictEnd y) ↔ SymbolEq 𝓒 d x y := by
  unfold SymbolEq
  rw [← map_sub restrictEnd]
  exact (and_congr (mem_endFiltration_restrictScalars hlat).symm
    (and_congr (mem_endFiltration_restrictScalars hlat).symm (mem_endFiltration_restrictScalars hlat).symm))

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
include hlat in
theorem shifts_restrict {d : ℤ} {g : (Module.End E V)ˣ} :
    Shifts 𝓛 d (Units.map restrictEnd.toMonoidHom g) ↔ Shifts 𝓒 d g := by
  unfold Shifts
  rw [← map_inv]
  exact and_congr (mem_endFiltration_restrictScalars hlat).symm
    (mem_endFiltration_restrictScalars hlat).symm

include hlat in
/-- An endomorphism congruent in its leading degree to a shifting unit is itself a
shifting unit. This also works for an extension-linear map compared to an ambient unit. -/
theorem exists_unit_of_symbolEq {d : ℤ} {x : Module.End E V} {g : (Module.End F V)ˣ}
    (hg : Shifts 𝓛 d g) (h : SymbolEq 𝓛 d (restrictEnd x) g) :
    ∃ u : (Module.End E V)ˣ, (u : Module.End E V) = x ∧ Shifts 𝓒 d u := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hm (i : ℤ) (v : V) : x v ∈ 𝓛.lattice (i + d) ↔ v ∈ 𝓛.lattice i := by
    refine ⟨fun hv => ?_, fun hv => h.1 i v hv⟩
    by_contra hv'
    have hv0 : v ≠ 0 := fun he => hv' (he ▸ zero_mem _)
    obtain ⟨j, hj, hj'⟩ := exists_exact_lattice_depth 𝓛 hϖ hv0
    have hji : j < i := lt_of_not_ge fun hij => hv' (𝓛.antitone hij hj)
    have hsub := h.2.2 j v hj
    have hdeep := 𝓛.antitone (show j + (d + 1) ≤ i + d by omega) hv
    have hgv : (g : Module.End F V) v ∈ 𝓛.lattice (j + (d + 1)) := by
      change x v - (g : Module.End F V) v ∈ 𝓛.lattice (j + (d + 1)) at hsub
      simpa only [sub_sub_cancel] using sub_mem hdeep hsub
    rw [show j + (d + 1) = j + 1 + d by omega] at hgv
    exact hj' ((hg.mem_lattice_iff (j + 1) v).mp hgv)
  have hinj : Function.Injective x := by
    apply (LinearMap.ker_eq_bot).mp
    apply eq_bot_iff.mpr
    intro v hv
    rw [Submodule.mem_bot]
    apply 𝓛.lattice_eq_zero_of_forall
    intro i
    exact (hm i v).mp (by rw [LinearMap.mem_ker.mp hv]; exact zero_mem _)
  let : FiniteDimensional E V := 𝓒.finiteDimensional
  let u := LinearMap.GeneralLinearGroup.ofLinearEquiv
    (LinearEquiv.ofBijective x ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩)
  have hu : (u : Module.End E V) = x := rfl
  have hm' (i : ℤ) (v : V) : x v ∈ 𝓒.lattice (i + d) ↔ v ∈ 𝓒.lattice i := by
    simpa only [← SetLike.mem_coe, hlat] using hm i v
  refine ⟨u, hu, ?_, ?_⟩
  · intro i v hv
    rw [hu]
    exact (hm' i v).mpr hv
  · intro i v hv
    apply (hm' (i + -d) _).mp
    have heq : x ((↑(u⁻¹) : Module.End E V) v) = v := by
      rw [← hu, ← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply]
    rwa [heq, neg_add_cancel_right]

/-- The lifting test on a single chain, without restriction of scalars. -/
theorem exists_unit_of_symbolEq_self {d : ℤ} {x : Module.End F V} {g : (Module.End F V)ˣ}
    (hg : Shifts 𝓛 d g) (h : SymbolEq 𝓛 d x g) :
    ∃ u : (Module.End F V)ˣ, (u : Module.End F V) = x ∧ Shifts 𝓛 d u := by
  have hx : restrictEnd (F := F) x = x := LinearMap.ext fun _ => rfl
  exact exists_unit_of_symbolEq 𝓛 𝓛 (fun _ => rfl) hg (hx.symm ▸ h)

end Restrict

end Langlands.BushnellKutzko.CriticalDerived
