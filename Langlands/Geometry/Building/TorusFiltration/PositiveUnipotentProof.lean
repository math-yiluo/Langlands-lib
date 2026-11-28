import Langlands.Geometry.Building.TorusFiltration.CongruenceProof
import Langlands.Geometry.Building.TorusFiltration.InducedShallowReduction
import Langlands.Geometry.Building.TorusFiltration.RadicalStatement
import Langlands.GroupScheme.IntegralModel.CongruencePowers
import Langlands.GroupScheme.Unipotent.GeometricPointsProof
import Mathlib.LinearAlgebra.Matrix.CharP

/-! # Unipotence of positive-depth minimal congruent models -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.BruhatTits.IntegralModels Langlands.GroupScheme Langlands.LocalGalois.Separable
open scoped CategoryTheory.MonObj NNReal ValuativeRel

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Building

private theorem unipotent_of_pPower_points {k : Type u} [Field k] [IsAlgClosed k]
    {p : ℕ} [Fact p.Prime] [CharP k p] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (h : ∀ x : rationalPoints G, ∃ n : ℕ, x ^ (p ^ n) = 1) : IsUnipotent G := by
  let : IsReduced G.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k _ G.X.hom
  apply (perfectFieldUnipotentRationalPoints k G).2
    (isIso_of_forall_rationalPoint_factors G)
  intro n _ _ ρ g
  by_cases hn : IsEmpty n
  · let : IsEmpty n := hn
    exact ⟨1, Subsingleton.elim _ _⟩
  let : Nonempty n := not_isEmpty_iff.mp hn
  obtain ⟨m, hm⟩ := h g
  have hρ := congrArg ρ.rationalMatrix hm
  rw [map_pow, map_one] at hρ
  refine ⟨p ^ m, ?_⟩
  rw [sub_pow_char_pow_of_commute p m (Commute.one_right _), one_pow]
  apply sub_eq_zero.mpr
  exact congrArg (fun A : Matrix.GeneralLinearGroup n k => (A : Matrix n n k)) hρ

private def pPowerSubgroup {G : Type u} [Group G] (p : ℕ)
    (hcomm : ∀ x y : G, Commute x y) : Subgroup G where
  carrier := {x | ∃ n : ℕ, x ^ (p ^ n) = 1}
  one_mem' := ⟨0, one_pow _⟩
  mul_mem' := by
    rintro x y ⟨m, hm⟩ ⟨n, hn⟩
    refine ⟨m + n, ?_⟩
    have hx : x ^ p ^ (m + n) = 1 := by rw [pow_add, pow_mul, hm, one_pow]
    have hy : y ^ p ^ (m + n) = 1 := by rw [add_comm m n, pow_add, pow_mul, hn, one_pow]
    rw [(hcomm x y).mul_pow, hx, hy, one_mul]
  inv_mem' := by
    rintro x ⟨n, hn⟩
    exact ⟨n, by rw [inv_pow, hn, inv_one]⟩

section Models

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (T : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))

local notation "O" => fixedFieldIntegers F
local notation "K" => inertiaFixedField F
local notation "κ" => IsLocalRing.ResidueField O
local notation "pκ" => ringChar κ
local notation "Model" => IntegralModel O K T.toGrp

private theorem fixedFieldResidueChar_prime : Nat.Prime pκ := by
  let : Algebra 𝓀[F] κ := (residueToFixedField F).toAlgebra
  rw [← Algebra.ringChar_eq 𝓀[F] κ]
  exact CharP.prime_ringChar 𝓀[F]

set_option maxHeartbeats 800000 in
private theorem specialFibrePoints_commute (M : Model) (hM : M.IsSmooth)
    (x y : rationalPoints M.specialFibre) : Commute x y := by
  let : HenselianLocalRing O := (fixedFieldIntegers_strictHenselian F).2.1
  obtain ⟨a, rfl⟩ := M.reduction_surjective hM x
  obtain ⟨b, rfl⟩ := M.reduction_surjective hM y
  let : IsCommMonObj T.toGrp.X := T.comm
  have hab : a * b = b * a := M.integralPointMap_injective (by
    rw [map_mul, map_mul]
    exact mul_comm _ _)
  change M.reduction a * M.reduction b = M.reduction b * M.reduction a
  rw [← map_mul, ← map_mul, hab]

set_option maxHeartbeats 800000 in
private theorem pPower_firstCongruence (A M : Model) (hA : A.IsSmooth)
    (h : A.congruenceSubgroup ≤ M.integralPoints) {g : rationalPoints T.toGrp}
    (hg : g ∈ A.congruenceSubgroup) : g ^ pκ ∈ M.congruenceSubgroup := by
  let : IsDiscreteValuationRing O := (fixedFieldIntegers_strictHenselian F).1
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  let C := A.positiveCongruenceModel hπ 1
  have hC : C.IsSmooth := by
    have hs := IntegralModel.dilatationStructure.2 O K T.toGrp A π hπ hA 1
    rw [A.congruenceModel_coe_pnat] at hs
    exact hs.1
  have hCp := (A.integralPoints_positiveCongruenceModel hπ 1).trans A.congruenceSubgroupAt_one
  have hmap : C.integralPoints.map (rationalPoints.map (𝟙 T.toGrp)) ≤ M.integralPoints := by
    rintro _ ⟨x, hx, rfl⟩
    simpa only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id] using h (hCp.le hx)
  obtain ⟨φ⟩ := exists_hom_of_map_integralPoints_le IntegralModel.smoothHomExtension F hC rfl hmap
  have hg' : g ^ pκ ∈ C.congruenceSubgroupAt 1 := by
    change g ^ pκ ∈ (A.positiveCongruenceModel hπ 1).congruenceSubgroupAt 1
    rw [A.congruenceSubgroupAt_positiveCongruenceModel]
    exact A.pow_mem_congruenceSubgroupAt_succ 1 pκ (IntegralModel.residueChar_mem_maximalIdeal (R := O))
      (A.congruenceSubgroupAt_one.ge hg)
  simpa only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id,
    IntegralModel.congruenceSubgroupAt_one] using φ.map_mem_congruenceSubgroupAt 1 hg'

variable [IsAffine T.X.left] (hT : IsTorus T.toGrp)

set_option maxHeartbeats 1600000 in
private theorem positiveModel_unipotent
    (r : ℝ≥0) (M : Model) (hr : 0 < r) (hM : M.IsSmooth)
    (hPts : M.integralPoints = minimalCongruentPoints F T hT r) : IsUnipotent M.specialFibre := by
  let : IsAlgClosed κ := (fixedFieldResidueIsAlgClosure F).isAlgClosed
  let : Fact (Nat.Prime pκ) := ⟨fixedFieldResidueChar_prime F⟩
  let : HenselianLocalRing O := (fixedFieldIntegers_strictHenselian F).2.1
  let : Smooth M.group.X.hom := hM
  let H := pPowerSubgroup pκ (specialFibrePoints_commute F T M hM)
  let Q := (H.comap M.reduction).map M.integralPointMap
  have hker (x : rationalPoints T.toGrp) (n : ℕ) (hx : x ∈ M.integralPoints)
      (hxpow : x ^ (pκ ^ n) ∈ M.congruenceSubgroup) : x ∈ Q := by
    obtain ⟨y, rfl⟩ := hx
    obtain ⟨z, hz, he⟩ := hxpow
    have hyz : z = y ^ (pκ ^ n) := M.integralPointMap_injective (he.trans (map_pow _ _ _).symm)
    refine ⟨y, ⟨n, ?_⟩, rfl⟩
    have hzred := (M.mem_congruenceKernel z).mp hz
    rwa [hyz, map_pow] at hzred
  have hFromFirst (A : Model) (hA : A.IsSmooth) (hAM : A.congruenceSubgroup ≤ M.integralPoints) :
      A.congruenceSubgroup ≤ Q := fun x hx =>
    hker x 1 (hAM hx) (by simpa only [pow_one] using pPower_firstCongruence F T A M hA hAM hx)
  have hQ : M.integralPoints ≤ Q := by
    by_cases h₁ : 1 ≤ r
    · let d := r - 1
      let A := minimalCongruentModel F T hT d
      have hA := minimalCongruentCongruence F T hT d A.val A.property.1 A.property.2.2
      rw [show d + 1 = r from tsub_add_cancel_of_le h₁, ← hPts] at hA
      rw [← hA]
      exact hFromFirst A.val A.property.1 hA.le
    · have hr₁ : r < 1 := lt_of_not_ge h₁
      let q : Set.Iio (1 : ℝ≥0) := ⟨r, hr₁⟩
      have hs : M.integralPoints = (connectedNeronModel F T hT).congruenceSubgroup ⊔
          inducedTorusStandardImages F T r := by
        rw [hPts, ← show (q : ℝ≥0) = r from rfl, minimalCongruentPoints_of_lt_one,
          minimalCongruentShallowSubgroup, ite_eq_right hr.ne']
      rw [hs]
      refine sup_le (hFromFirst (connectedNeronModel F T hT) (connectedNeronModel_isSmooth F T hT)
        (le_sup_left.trans hs.ge)) ?_
      refine iSup_le fun S => iSup_le fun hS => iSup_le fun f => ?_
      obtain ⟨N, hN, hNpts, hNpow⟩ :=
        InducedTorusShallow.exists_model_reduction_pPower F S r hS hr hr₁ (p := pκ)
      have hi : (localGeometricCharacterCongruence F S r).map
          (rationalPoints.map (CommGroupScheme.groupHom f)) ≤ inducedTorusStandardImages F T r :=
        le_iSup_of_le S (le_iSup_of_le hS (le_iSup_of_le f le_rfl))
      have hle : N.integralPoints.map (rationalPoints.map (CommGroupScheme.groupHom f)) ≤
          M.integralPoints := by
        rw [hNpts, hs]
        exact hi.trans le_sup_right
      obtain ⟨φ⟩ := exists_hom_of_map_integralPoints_le IntegralModel.smoothHomExtension F
        (n := CommGroupScheme.groupHom f) hN rfl hle
      rw [← hNpts]
      rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
      obtain ⟨n, hn⟩ := hNpow y
      let z := rationalPoints.map φ.hom y
      refine ⟨z, ⟨n, ?_⟩, φ.integralPointMap_naturality y⟩
      change (M.reduction (rationalPoints.map φ.hom y)) ^ (pκ ^ n) = 1
      rw [φ.reduction_naturality, ← map_pow, hn, map_one]
  apply unipotent_of_pPower_points (p := pκ) M.specialFibre
  intro t
  obtain ⟨x, rfl⟩ := M.reduction_surjective hM t
  obtain ⟨y, hy, he⟩ := hQ ⟨x, rfl⟩
  rwa [M.integralPointMap_injective he] at hy

end Models

/-- Every smooth realizing model at a strictly positive depth has unipotent special fibre. -/
theorem minimalCongruentPositiveUnipotent : MinimalCongruentPositiveUnipotentStatement.{u} := by
  intro F _ _ _ _ T _ hT r M hr hM hPts
  exact positiveModel_unipotent F T hT r M hr hM hPts

end Langlands.Geometry.Building
