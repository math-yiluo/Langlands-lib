import Langlands.LinearAlgebra.LocallyFiniteJordan
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.BilinearMap

/-! # Symmetrizing a pairing with locally finite asymmetry -/

noncomputable section

universe v

namespace Langlands.LinearAlgebra

open Module

variable {V : Type v} [AddCommGroup V] [Module ℂ V]

def adjointPairing (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ where
  toFun x :=
    { toFun := fun y => starRingEnd ℂ (B y x)
      map_add' := fun y z => by simp
      map_smul' := fun c y => by simp }
  map_add' x y := by ext z; simp
  map_smul' c x := by ext y; simp

@[simp] theorem adjointPairing_apply (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (x y : V) :
    adjointPairing B x y = starRingEnd ℂ (B y x) := rfl

def otherPrimary (T : End ℂ V) (a : ℂ) : Submodule ℂ V :=
  ⨆ b : ℂ, ⨆ (_ : b ≠ a), T.maxGenEigenspace b

theorem locallyFinite_primarySpan (T : End ℂ V) (hT : IsLocallyFinite T) :
    ⨆ a : ℂ, T.maxGenEigenspace a = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨P, hx⟩ := hT x
  have hP : P.carrier ≤ ⨆ a : ℂ, T.maxGenEigenspace a := by
    calc
      P.carrier = (⊤ : Submodule ℂ P.carrier).map P.carrier.subtype := by simp
      _ = (⨆ a : ℂ, P.restrict.maxGenEigenspace a).map P.carrier.subtype := by
        rw [Module.End.iSup_maxGenEigenspace_eq_top]
      _ ≤ ⨆ a : ℂ, T.maxGenEigenspace a := by
        rw [Submodule.map_iSup]
        exact iSup_le fun a => (Module.End.map_genEigenspace_le P.carrier.subtype
          (by rfl) a ⊤).trans (le_iSup (T.maxGenEigenspace) a)
  exact hP hx

theorem locallyFinite_primaryComplement (T : End ℂ V) (hT : IsLocallyFinite T) (a : ℂ) :
    IsCompl (T.maxGenEigenspace a) (otherPrimary T a) := by
  refine ⟨T.independent_maxGenEigenspace a, ?_⟩
  rw [codisjoint_iff, otherPrimary, ← iSup_split_single (T.maxGenEigenspace) a,
    locallyFinite_primarySpan T hT]

theorem otherPrimary_invariant {T f : End ℂ V} (h : Commute T f) (a : ℂ) :
    ∀ x ∈ otherPrimary T a, f x ∈ otherPrimary T a := by
  change otherPrimary T a ≤ (otherPrimary T a).comap f
  rw [← Submodule.map_le_iff_le_comap, otherPrimary, Submodule.map_iSup]
  apply iSup_le
  intro b
  rw [Submodule.map_iSup]
  apply iSup_le
  intro hb
  exact (Module.End.map_genEigenspace_le f h b ⊤).trans
    (le_iSup_of_le b (le_iSup_of_le hb le_rfl))

theorem locallyFinite_shift_surjective_primary (T : End ℂ V) (hT : IsLocallyFinite T)
    (a b : ℂ) (hab : b ≠ a) :
    Set.SurjOn (⇑(T - a • (1 : End ℂ V)))
      (↑(T.maxGenEigenspace b) : Set V) (↑(T.maxGenEigenspace b) : Set V) := by
  intro x hx
  obtain ⟨P, hxP⟩ := hT x
  let S := P.carrier ⊓ T.maxGenEigenspace b
  have hinv : ∀ y ∈ S, (T - a • 1) y ∈ S := by
    intro y hy
    exact ⟨P.carrier.sub_mem (P.invariant hy.1) (P.carrier.smul_mem a hy.1),
      Module.End.mapsTo_maxGenEigenspace_of_comm
        (Algebra.mul_sub_algebraMap_commutes T a) b hy.2⟩
  let A := (T - a • 1).restrict hinv
  let : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le inf_le_left
  have hA : Function.Injective A := by
    apply (injective_iff_map_eq_zero _).2
    intro y hy
    have hya : y.val ∈ T.genEigenspace a 1 := by
      rw [Module.End.genEigenspace_one, LinearMap.mem_ker]
      exact congrArg Subtype.val hy
    have hyb : y.val ∈ T.maxGenEigenspace a := T.genEigenspace_le_maximal a 1 hya
    have hz : y.val = 0 := (Submodule.disjoint_def.mp
      (T.disjoint_genEigenspace hab ⊤ ⊤)) y.val y.property.2 hyb
    exact Subtype.ext hz
  obtain ⟨y, hy⟩ := LinearMap.surjective_of_injective hA ⟨x, hxP, hx⟩
  exact ⟨y.val, y.property.2, congrArg Subtype.val hy⟩

theorem locallyFinite_shift_surjective_other (T : End ℂ V) (hT : IsLocallyFinite T) (a : ℂ) :
    Set.SurjOn (⇑(T - a • (1 : End ℂ V)))
      (↑(otherPrimary T a) : Set V) (↑(otherPrimary T a) : Set V) := by
  have hle : otherPrimary T a ≤ (otherPrimary T a).map (T - a • 1) := by
    apply iSup_le
    intro b
    apply iSup_le
    intro hb x hx
    obtain ⟨y, hy, hxy⟩ := locallyFinite_shift_surjective_primary T hT a b hb hx
    refine ⟨y, ?_, hxy⟩
    exact Submodule.mem_iSup_of_mem b (Submodule.mem_iSup_of_mem hb hy)
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hle hx
  exact ⟨y, hy, hxy⟩

section Symmetrize

variable (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (T : End ℂ V)
  (hBT : ∀ x y, B (T x) y = starRingEnd ℂ (B y x))

include hBT

theorem asymmetry_isometry (x y : V) : B (T x) (T y) = B x y := by
  rw [hBT, hBT]
  simp

theorem asymmetry_shift_move (x y : V) :
    B ((T - (-1 : ℂ) • 1) x) (T y) = B x ((T - (-1 : ℂ) • 1) y) := by
  simp only [neg_smul, one_smul, sub_neg_eq_add, LinearMap.add_apply,
    Module.End.one_apply, map_add, LinearMap.add_apply]
  rw [asymmetry_isometry B T hBT]
  exact add_comm _ _

theorem asymmetry_shift_move_pow (n : ℕ) (x y : V) :
    B (((T - (-1 : ℂ) • 1) ^ n) x) ((T ^ n) y) =
      B x (((T - (-1 : ℂ) • 1) ^ n) y) := by
  let A := T - (-1 : ℂ) • 1
  have hc : Commute A T := (Algebra.mul_sub_algebraMap_commutes T (-1 : ℂ)).symm
  change B ((A ^ n) x) ((T ^ n) y) = B x ((A ^ n) y)
  induction n generalizing x y with
  | zero => rfl
  | succ n ih =>
    calc
      B ((A ^ (n + 1)) x) ((T ^ (n + 1)) y) =
          B (A ((A ^ n) x)) (T ((T ^ n) y)) := by
        simp only [pow_succ', Module.End.mul_apply]
      _ = B ((A ^ n) x) (A ((T ^ n) y)) := asymmetry_shift_move B T hBT _ _
      _ = B ((A ^ n) x) ((T ^ n) (A y)) :=
        congrArg (B ((A ^ n) x)) (LinearMap.congr_fun (hc.pow_right n).eq y)
      _ = B x ((A ^ n) (A y)) := ih x (A y)
      _ = B x ((A ^ (n + 1)) y) := by rw [pow_succ, Module.End.mul_apply]

theorem primary_orthogonal_other (hT : IsLocallyFinite T)
    {x y : V} (hx : x ∈ T.maxGenEigenspace (-1)) (hy : y ∈ otherPrimary T (-1)) :
    B x y = 0 := by
  obtain ⟨n, hn⟩ := (T.mem_maxGenEigenspace (-1) x).mp hx
  have hsur := (locallyFinite_shift_surjective_other T hT (-1)).iterate n
  obtain ⟨z, _hz, hz⟩ := hsur hy
  have hz' : ((T - (-1 : ℂ) • 1) ^ n) z = y := by
    simpa only [Module.End.pow_apply] using hz
  rw [← hz', ← asymmetry_shift_move_pow B T hBT n x z, hn]
  simp

theorem other_orthogonal_primary (hT : IsLocallyFinite T)
    {x y : V} (hx : x ∈ otherPrimary T (-1)) (hy : y ∈ T.maxGenEigenspace (-1)) :
    B x y = 0 := by
  have hTy : T y ∈ T.maxGenEigenspace (-1) :=
    Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl T) (-1) hy
  have h := primary_orthogonal_other B T hBT hT hTy hx
  rw [hBT] at h
  have h' := congrArg (starRingEnd ℂ) h
  simpa using h'

end Symmetrize

theorem projection_commute_of_invariant {N C : Submodule ℂ V} (hNC : IsCompl N C)
    (f : End ℂ V) (hN : ∀ x ∈ N, f x ∈ N) (hC : ∀ x ∈ C, f x ∈ C) (x : V) :
    N.projection C hNC (f x) = f (N.projection C hNC x) := by
  let P := N.projection C hNC
  let Q := C.projection N hNC.symm
  have hPx : f (P x) ∈ N := hN _ (N.projection_apply_mem hNC x)
  have hQx : f (Q x) ∈ C := hC _ (C.projection_apply_mem hNC.symm x)
  calc
    P (f x) = P (f (P x + Q x)) :=
      congrArg (fun y => P (f y)) (N.projection_add_projection_eq_self hNC x).symm
    _ = f (P x) := by
      rw [map_add, map_add, N.projection_apply_of_mem_left hNC hPx,
        (N.projection_apply_eq_zero_iff hNC).mpr hQx, add_zero]

/-- A nondegenerate pairing whose asymmetry is locally finite has a
nondegenerate hermitian symmetrization. Every commuting isometry preserves it. -/
theorem exists_hermitian_of_locallyFinite_asymmetry
    (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (T : End ℂ V) (hT : IsLocallyFinite T)
    (hBT : ∀ x y, B (T x) y = starRingEnd ℂ (B y x))
    (hnd : ∀ x : V, (∀ y, B x y = 0) → x = 0) :
    ∃ H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ,
      (∀ x y, H y x = starRingEnd ℂ (H x y)) ∧
      (∀ x : V, (∀ y, H x y = 0) → x = 0) ∧
      ∀ f : End ℂ V, Commute T f → (∀ x y, B (f x) (f y) = B x y) →
        ∀ x y, H (f x) (f y) = H x y := by
  let N := T.maxGenEigenspace (-1)
  let C := otherPrimary T (-1)
  have hNC : IsCompl N C := locallyFinite_primaryComplement T hT (-1)
  let P := N.projection C hNC
  let Q := C.projection N hNC.symm
  have hPN (x : V) : P x ∈ N := N.projection_apply_mem hNC x
  have hQC (x : V) : Q x ∈ C := C.projection_apply_mem hNC.symm x
  have hPP (x : V) : P (P x) = P x := N.projection_apply_of_mem_left hNC (hPN x)
  have hQQ (x : V) : Q (Q x) = Q x := C.projection_apply_of_mem_left hNC.symm (hQC x)
  have hPQ (x : V) : P (Q x) = 0 := (N.projection_apply_eq_zero_iff hNC).mpr (hQC x)
  have hQP (x : V) : Q (P x) = 0 := (C.projection_apply_eq_zero_iff hNC.symm).mpr (hPN x)
  have hTN (x : V) (hx : x ∈ N) : T x ∈ N :=
    Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl T) (-1) hx
  have hTC (x : V) (hx : x ∈ C) : T x ∈ C :=
    otherPrimary_invariant (Commute.refl T) (-1) x hx
  let Bp := (B.compl₂ P).comp P
  let Bq := (B.compl₂ Q).comp Q
  let H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ :=
    Bq + adjointPairing Bq + Complex.I • (Bp - adjointPairing Bp)
  have hH (x y : V) : H x y = B (Q x) (Q y) + starRingEnd ℂ (B (Q y) (Q x)) +
      Complex.I * (B (P x) (P y) - starRingEnd ℂ (B (P y) (P x))) := rfl
  refine ⟨H, ?_, ?_, ?_⟩
  · intro x y
    simp only [hH, map_add, map_mul, map_sub]
    simp
    ring
  · intro x hx
    have hminus (y : V) : B ((1 - T) (P x)) (P y) = 0 := by
      have h := hx (P y)
      rw [hH, hQP, hPP] at h
      simp only [map_zero, LinearMap.zero_apply, zero_add] at h
      have hz := (mul_eq_zero.mp h).resolve_left Complex.I_ne_zero
      change B (P x - T (P x)) (P y) = 0
      simpa only [map_sub, LinearMap.sub_apply, hBT] using hz
    have hDP : (1 - T) (P x) = 0 := by
      apply hnd
      intro y
      rw [← N.projection_add_projection_eq_self hNC y, map_add, hminus]
      have hDN : (1 - T) (P x) ∈ N := N.sub_mem (hPN x) (hTN _ (hPN x))
      rw [primary_orthogonal_other B T hBT hT hDN (hQC y), add_zero]
    have hPx : P x = 0 := by
      have hTP : T (P x) = P x := (sub_eq_zero.mp hDP).symm
      have heig : P x ∈ T.genEigenspace 1 1 := by
        simpa only [Module.End.mem_genEigenspace_one, one_smul] using hTP
      exact (Submodule.disjoint_def.mp (T.disjoint_genEigenspace
        (show (-1 : ℂ) ≠ 1 by norm_num) ⊤ ⊤)) (P x) (hPN x)
          (T.genEigenspace_le_maximal 1 1 heig)
    have hplus (y : V) : B ((T - (-1 : ℂ) • 1) (Q x)) (Q y) = 0 := by
      have h := hx (Q y)
      rw [hH, hPQ, hQQ] at h
      simp only [map_zero, LinearMap.zero_apply, sub_self, mul_zero, add_zero] at h
      simpa only [neg_smul, one_smul, sub_neg_eq_add, LinearMap.add_apply,
        Module.End.one_apply, map_add, LinearMap.add_apply, hBT, add_comm] using h
    have hAQ : (T - (-1 : ℂ) • 1) (Q x) = 0 := by
      apply hnd
      intro y
      rw [← N.projection_add_projection_eq_self hNC y, map_add, hplus]
      have hAC : (T - (-1 : ℂ) • 1) (Q x) ∈ C := by
        simpa only [neg_smul, one_smul, sub_neg_eq_add, LinearMap.add_apply,
          Module.End.one_apply] using C.add_mem (hTC _ (hQC x)) (hQC x)
      rw [other_orthogonal_primary B T hBT hT hAC (hPN y), zero_add]
    have hQx : Q x = 0 := by
      have hQN : Q x ∈ N := (T.mem_maxGenEigenspace (-1) (Q x)).mpr
        ⟨1, by simpa only [pow_one] using hAQ⟩
      exact (Submodule.disjoint_def.mp hNC.disjoint) (Q x) hQN (hQC x)
    have hsum : P x + Q x = x := N.projection_add_projection_eq_self hNC x
    simpa only [hPx, hQx, zero_add] using hsum.symm
  · intro f hf hBf x y
    have hN : ∀ z ∈ N, f z ∈ N := Module.End.mapsTo_maxGenEigenspace_of_comm hf (-1)
    have hC : ∀ z ∈ C, f z ∈ C := otherPrimary_invariant hf (-1)
    have hPf (z : V) : P (f z) = f (P z) := projection_commute_of_invariant hNC f hN hC z
    have hQf (z : V) : Q (f z) = f (Q z) :=
      projection_commute_of_invariant hNC.symm f hC hN z
    simp only [hH, hPf, hQf, hBf]

end Langlands.LinearAlgebra
