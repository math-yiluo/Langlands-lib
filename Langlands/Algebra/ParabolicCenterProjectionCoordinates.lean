import Langlands.Algebra.ParabolicCenterProjectionLevi
import Langlands.Algebra.AbelianEnvelopingPolynomial
import Langlands.Algebra.ParabolicCenterProjectionFiniteStatement

/-! # The Harish-Chandra map of the centre through the parabolic projection -/

noncomputable section

universe v w

set_option autoImplicit false

namespace Langlands.Algebra.ParabolicCenterProjection.GradingData

open LieAlgebra Langlands.Algebra.LieWeightProjection Langlands.Archimedean.Kostant
  Langlands.Archimedean.VermaPBW

attribute [local instance 100] LieRing.ofAssociativeRing

variable {g : Type v} [LieRing g] [LieAlgebra ℂ g] {H : g} (D : GradingData g H)
  {m : Type w} [LieRing m] [LieAlgebra ℂ m] {j : m →ₗ⁅ℂ⁆ g}
  (hj : Function.Injective j) (hrange : ∀ X : g, X ∈ Set.range j ↔ ⁅H, X⁆ = 0)

local notation "Ug" => UniversalEnvelopingAlgebra ℂ g
local notation "Um" => UniversalEnvelopingAlgebra ℂ m

/-- The basis indices of grading zero. -/
abbrev zeroIndex : Type v := {c : D.ι // D.φ c = 0}

theorem wt_H_eq_zero_of_φ (c : D.zeroIndex) : D.wt c.1 ⟨H, D.H_mem⟩ = 0 := by
  rw [(D.φ_eq_zero_iff c.1).mp c.2, LinearMap.zero_apply]

/-- The Levi indices of grading zero are the indices of grading zero. -/
def zeroIndexEquiv : D.leviZeroIndex ≃ D.zeroIndex where
  toFun a := ⟨a.1.1, a.2⟩
  invFun c := ⟨⟨c.1, D.wt_H_eq_zero_of_φ c⟩, c.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The basis of the Levi Cartan subalgebra indexed by the indices of grading zero. -/
def cartanBasis : Module.Basis D.zeroIndex ℂ (D.leviCartan hj hrange) :=
  (D.leviCartanBasis hj hrange).reindex D.zeroIndexEquiv

/-- The inclusion of the Levi Cartan subalgebra into `g`. -/
def cartanToG : D.leviCartan hj hrange →ₗ⁅ℂ⁆ g := j.comp (D.leviCartan hj hrange).incl

theorem cartanToG_basis (c : D.zeroIndex) : D.cartanToG hj hrange (D.cartanBasis hj hrange c) =
    D.basis c.1 := by
  rw [cartanToG, LieHom.comp_apply, cartanBasis, Module.Basis.reindex_apply,
    D.incl_leviCartanBasis, D.j_leviBasis]
  rfl

theorem zeroList_nodup : (orderedSubindices (fun c => D.φ c = 0) (weightOrderedIndices D.φ)).Nodup :=
  orderedSubindices_nodup _ (weightOrderedIndices_nodup D.φ)

theorem mem_zeroList (a : D.zeroIndex) :
    a ∈ orderedSubindices (fun c => D.φ c = 0) (weightOrderedIndices D.φ) :=
  mem_orderedSubindices _ a (mem_weightOrderedIndices D.φ a.1)

/-- The centre of the enveloping algebra of the Levi Cartan subalgebra as a polynomial ring. -/
def cartanPoly : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (D.leviCartan hj hrange)) ≃ₐ[ℂ]
    MvPolynomial D.zeroIndex ℂ :=
  (AbelianEnveloping.polyEquiv (D.leviCartan_lie_eq_zero hj hrange) (D.cartanBasis hj hrange)
    D.zeroList_nodup D.mem_zeroList).symm

/-- The Harish-Chandra map of the Levi centre. -/
def leviHC : Subalgebra.center ℂ Um →ₐ[ℂ] MvPolynomial D.zeroIndex ℂ :=
  (D.cartanPoly hj hrange).toAlgHom.comp (D.leviProj hj hrange)

theorem leviHC_injective : Function.Injective (D.leviHC hj hrange) :=
  (D.cartanPoly hj hrange).injective.comp (D.leviProj_injective hj hrange)

/-- The positive generators of `H` lie in the positive right ideal for the grading `φ`. -/
theorem positiveRightIdeal_le :
    positiveRightIdeal H ≤ positiveWeightRightIdeal D.basis D.φ := by
  apply Submodule.span_le.mpr
  rintro _ ⟨k, Y, hY, u, rfl⟩
  have h1 := mem_eigenSpan_of_ad D.basis (fun i => D.wt i ⟨H, D.H_mem⟩) H
    (fun i => D.lie_basis i ⟨H, D.H_mem⟩) (((k + 1 : ℕ) : ℂ)) hY
  have h2 : Submodule.span ℂ (D.basis '' {i | D.wt i ⟨H, D.H_mem⟩ = ((k + 1 : ℕ) : ℂ)}) ≤
      Submodule.span ℂ (D.basis '' {i | 0 < D.φ i}) := by
    apply Submodule.span_mono
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨i, D.re_wt_reg_pos i k hi, rfl⟩
  exact mul_mem_positiveWeightRightIdeal_of_span D.basis D.φ (h2 h1) u

theorem map_positiveWeightRightIdeal_levi {x : Um}
    (hx : x ∈ positiveWeightRightIdeal (D.leviBasis hj hrange) D.φm) :
    Langlands.Algebra.LieEnvelopingEquiv.map j x ∈ positiveWeightRightIdeal D.basis D.φ := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, v, rfl⟩ := hx
    rw [map_mul, Langlands.Algebra.LieEnvelopingEquiv.map_generator, D.j_leviBasis]
    exact Submodule.subset_span ⟨a.1, ha, _, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul t x _ hx => rw [map_smul]; exact Submodule.smul_mem _ t hx

theorem map_comp_incl :
    Langlands.Algebra.LieEnvelopingEquiv.map (D.cartanToG hj hrange) =
      (Langlands.Algebra.LieEnvelopingEquiv.map j).comp
        (Langlands.Algebra.LieEnvelopingEquiv.map (D.leviCartan hj hrange).incl) := by
  apply UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro x
  simp only [LieHom.coe_comp, Function.comp_apply, AlgHom.coe_toLieHom,
    Langlands.Algebra.LieEnvelopingEquiv.map_generator, AlgHom.comp_apply]
  rfl

/-- The Harish-Chandra map of the centre of `U(g)` through the parabolic projection `p`. -/
def hcMap (p : Subalgebra.center ℂ Ug →ₐ[ℂ] Subalgebra.center ℂ Um) :
    Subalgebra.center ℂ Ug →ₐ[ℂ] MvPolynomial D.zeroIndex ℂ :=
  (D.leviHC hj hrange).comp p

theorem sub_hcMap_mem (P : Subalgebra.center ℂ Ug →ₐ[ℂ] Subalgebra.center ℂ Um)
    (hP : ∀ z : Subalgebra.center ℂ Ug, (z : Ug) -
      UniversalEnvelopingAlgebra.lift ℂ ((UniversalEnvelopingAlgebra.ι ℂ).comp j) (P z : Um) ∈
        positiveRightIdeal H)
    (z : Subalgebra.center ℂ Ug) :
    (z : Ug) - Langlands.Algebra.LieEnvelopingEquiv.map (D.cartanToG hj hrange)
      (D.leviProj hj hrange (P z)).val ∈ positiveWeightRightIdeal D.basis D.φ := by
  have h1 := D.positiveRightIdeal_le (hP z)
  have h2 := D.map_positiveWeightRightIdeal_levi hj hrange (D.sub_leviProj_mem hj hrange (P z))
  rw [map_sub] at h2
  rw [D.map_comp_incl hj hrange, AlgHom.comp_apply]
  have := Submodule.add_mem _ h1 h2
  convert this using 1
  change _ = (z : Ug) - Langlands.Algebra.LieEnvelopingEquiv.map j (P z : Um) + _
  abel

/-- **Coordinates of the Harish-Chandra map.** The coefficients of `hcMap z` are the PBW
coordinates of `z` (ordered by decreasing grading) at the exponents supported on the letters of
grading zero. -/
theorem coeff_hcMap (P : Subalgebra.center ℂ Ug →ₐ[ℂ] Subalgebra.center ℂ Um)
    (hP : ∀ z : Subalgebra.center ℂ Ug, (z : Ug) -
      UniversalEnvelopingAlgebra.lift ℂ ((UniversalEnvelopingAlgebra.ι ℂ).comp j) (P z : Um) ∈
        positiveRightIdeal H)
    (z : Subalgebra.center ℂ Ug) (α : D.zeroIndex →₀ ℕ) :
    (D.hcMap hj hrange P z).coeff α = (weightOrderedPBWBasis D.basis D.φ).repr z.val
      (α.embDomain (Function.Embedding.subtype fun c => D.φ c = 0)) := by
  have hmem := D.sub_hcMap_mem hj hrange P hP z
  have hpos := positiveWeightRightIdeal_le_positivePBWSpan D.basis D.φ
    (positiveWeightLieSubalgebra D.basis D.φ D.ev Complex.reAddGroupHom D.re_ev D.reg
      D.lie_reg).incl
    (positiveWeightLieBasis D.basis D.φ D.ev Complex.reAddGroupHom D.re_ev D.reg D.lie_reg)
    (positiveWeightLieSubalgebra_incl_basis D.basis D.φ D.ev Complex.reAddGroupHom D.re_ev D.reg
      D.lie_reg) hmem
  have h0 := positivePBWSpan_coord_zero D.basis D.φ
    (α := α.embDomain (Function.Embedding.subtype fun c => D.φ c = 0)) (fun a ha =>
      Finsupp.embDomain_of_notMem_range _ _ _ (by
        rintro ⟨a', rfl⟩
        exact (ne_of_gt ha) a'.property)) hpos
  rw [map_sub, Finsupp.sub_apply, sub_eq_zero] at h0
  rw [h0, repr_envelopingMap_embDomain D.basis D.φ (D.cartanToG hj hrange) (D.cartanBasis hj hrange)
    (D.cartanToG_basis hj hrange)]
  exact AbelianEnveloping.coeff_polyEquiv_symm _ _ _ _ _ α

/-- **Injectivity of the Harish-Chandra map of the centre of `U(g)`.** -/
theorem hcMap_injective (P : Subalgebra.center ℂ Ug →ₐ[ℂ] Subalgebra.center ℂ Um)
    (hP : ∀ z : Subalgebra.center ℂ Ug, (z : Ug) -
      UniversalEnvelopingAlgebra.lift ℂ ((UniversalEnvelopingAlgebra.ι ℂ).comp j) (P z : Um) ∈
        positiveRightIdeal H) :
    Function.Injective (D.hcMap hj hrange P) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  have ha : D.leviProj hj hrange (P z) = 0 :=
    (D.cartanPoly hj hrange).injective (by rw [map_zero]; exact hz)
  have h := D.sub_hcMap_mem hj hrange P hP z
  rw [ha, ZeroMemClass.coe_zero, map_zero, sub_zero] at h
  apply Subtype.ext
  exact LieCenterProjectionInjective.center_eq_zero_of_mem_positiveWeightRightIdeal D.basis D.φ
    D.ev Complex.reAddGroupHom D.re_ev D.reg D.lie_reg D.exists_shiftPart_ne_zero_g z h

end Langlands.Algebra.ParabolicCenterProjection.GradingData
