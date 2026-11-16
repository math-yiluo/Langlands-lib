import Langlands.Global.RankinSelberg.DualExpansionConj

/-! # The character coefficient along `Y_(n,m)` of a dual function is a dual period -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Topology
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Global
open Langlands.Automorphic.CuspidalWhittaker (IsPeriodic ratVec ratVec_apply PreservesRational)

variable {F : Type u} [Field F] [NumberField F]

local instance dualBridgeSchemeAffine (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance dualBridgeSchemeSmooth (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

variable {m K : ℕ}

section Coordinates

/-- The rectangle coordinates `(X, c)` of the conjugate of `y(A)`, as an additive map. -/
def rectCoordHom : (Fin (m + 1) × Fin K → Adeles F) →+ ((Fin K × Fin m) ⊕ Fin K → Adeles F) where
  toFun A := Sum.elim (rectX A) (rectC A)
  map_zero' := by
    funext s
    cases s <;> simp [rectX, rectC]
  map_add' A B := by
    funext s
    cases s <;> simp [rectX, rectC, add_comm]

theorem preservesRational_rectCoordHom : PreservesRational (rectCoordHom (F := F) (m := m) (K := K)) := by
  intro k
  refine ⟨Sum.elim (fun p => -k (⟨p.2, by omega⟩, ⟨K - 1 - p.1, by omega⟩))
    (fun i => -k (⟨m, by omega⟩, ⟨K - 1 - i, by omega⟩)), ?_⟩
  funext s
  cases s <;> simp [rectCoordHom, rectX, rectC, ratVec]

theorem continuous_rectCoordHom : Continuous (rectCoordHom (F := F) (m := m) (K := K)) := by
  refine continuous_pi fun s => ?_
  cases s with
  | inl p => exact (continuous_apply _).neg
  | inr i => exact (continuous_apply _).neg

theorem surjective_rectCoordHom : Function.Surjective (rectCoordHom (F := F) (m := m) (K := K)) := by
  intro z
  refine ⟨fun p => -(if h : (p.1 : ℕ) < m then z (Sum.inl (⟨K - 1 - p.2, by omega⟩, ⟨p.1, h⟩))
    else z (Sum.inr ⟨K - 1 - p.2, by omega⟩)), ?_⟩
  funext s
  cases s with
  | inl p =>
    simp only [rectCoordHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Sum.elim_inl, rectX, neg_neg]
    rw [dite_eq_left (by simp)]
    congr 2
    ext
    all_goals first | (simp; done) | (simp; omega)
  | inr i =>
    simp only [rectCoordHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Sum.elim_inr, rectC, neg_neg]
    rw [dite_eq_right (by simp)]
    congr 2
    ext
    simp
    omega

variable [CompactSpace (AdeleQuotient F)]

/-- **Changing to the rectangle coordinates** of the conjugated radical. -/
theorem torusIntegral_rectCoords
    (h : (Fin K × Fin m → Adeles F) → (Fin K → Adeles F) → ℂ) (hc : Continuous (Function.uncurry h))
    (hp : ∀ X c (ρ : Fin K × Fin m → F) (σ : Fin K → F),
      h (X + ratVec ρ) (c + ratVec σ) = h X c) :
    Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin (m + 1) × Fin K)
        (fun A => h (rectX A) (rectC A)) =
      Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin K × Fin m) fun X =>
        Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin K) fun c => h X c := by
  obtain ⟨g, hg⟩ : ∃ g : ((Fin K × Fin m) ⊕ Fin K → Adeles F) → ℂ,
      g = fun v => h (fun p => v (Sum.inl p)) (fun i => v (Sum.inr i)) := ⟨_, rfl⟩
  have hgc : Continuous g := by
    rw [hg]
    have hpair : Continuous fun v : ((Fin K × Fin m) ⊕ Fin K → Adeles F) =>
        ((fun p => v (Sum.inl p), fun i => v (Sum.inr i)) :
          (Fin K × Fin m → Adeles F) × (Fin K → Adeles F)) :=
      (continuous_pi fun p => continuous_apply _).prodMk
        (continuous_pi fun i => continuous_apply _)
    exact (hc.comp hpair).congr fun v => rfl
  have hgp : IsPeriodic g := by
    intro v k
    rw [hg]
    show h (fun p => (v + ratVec k) (Sum.inl p)) (fun i => (v + ratVec k) (Sum.inr i)) =
      h (fun p => v (Sum.inl p)) (fun i => v (Sum.inr i))
    have ea : (fun p => (v + ratVec k) (Sum.inl p)) =
        (fun p => v (Sum.inl p)) + ratVec (fun p => k (Sum.inl p)) := funext fun p => rfl
    have eb : (fun i => (v + ratVec k) (Sum.inr i)) =
        (fun i => v (Sum.inr i)) + ratVec (fun i => k (Sum.inr i)) := funext fun i => rfl
    rw [ea, eb, hp]
  have e1 : ∀ A : Fin (m + 1) × Fin K → Adeles F,
      g (rectCoordHom A) = h (rectX A) (rectC A) := by
    intro A
    rw [hg]
    rfl
  have e2 : ∀ (x : Fin K × Fin m → Adeles F) (y : Fin K → Adeles F),
      g (Sum.elim x y) = h x y := by
    intro x y
    rw [hg]
    rfl
  have h1 := Langlands.Automorphic.CuspidalWhittaker.torusIntegral_comp hgp hgc
    preservesRational_rectCoordHom continuous_rectCoordHom surjective_rectCoordHom
  rw [torusIntegral_sum_elim hgp hgc] at h1
  simp only [e1, e2] at h1
  exact h1

end Coordinates

section Bridge

variable [CompactSpace (AdeleQuotient F)] {ψ : AddChar (Adeles F) ℂ}
  (hψF : ∀ a : F, ψ (algebraMap F (Adeles F) a) = 1) (hψc : Continuous ψ) (hψ1 : ∀ x, ‖ψ x‖ = 1)
  {W : Points F (m + K + 1) → ℂ}

omit [CompactSpace (AdeleQuotient F)] in
theorem iota_mem_rationalSubgroup {n : ℕ} {k : Points F n}
    (hk : k ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F n)) :
    iota F n k ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F n) := by
  obtain ⟨c, rfl⟩ := hk
  rw [UnequalAnalytic.iota_rational]
  exact ⟨_, rfl⟩

omit [CompactSpace (AdeleQuotient F)] in
include hψc in
theorem DualData.continuous_rectIntegrand (hW : DualData F m ψ K W) (g : Points F (m + K + 1)) :
    Continuous (Function.uncurry fun (X : Fin K × Fin m → Adeles F) (c : Fin K → Adeles F) =>
      ψ (lastEntry c) * cornerSum F m K W (xcPoint F X c * g)) := by
  have h1 : Continuous fun p : (Fin K × Fin m → Adeles F) × (Fin K → Adeles F) =>
      xcPoint F p.1 p.2 := continuous_xcPoint
  exact ((hψc.comp (continuous_lastEntry.comp continuous_snd)).mul
    (hW.continuous_cornerSum.comp (h1.mul continuous_const))).congr fun _ => rfl

omit [CompactSpace (AdeleQuotient F)] in
include hψF in
theorem DualData.periodic_rectIntegrand (hW : DualData F m ψ K W) (g : Points F (m + K + 1))
    (X : Fin K × Fin m → Adeles F) (c : Fin K → Adeles F) (ρ : Fin K × Fin m → F)
    (σ : Fin K → F) :
    ψ (lastEntry (c + ratVec σ)) * cornerSum F m K W (xcPoint F (X + ratVec ρ) (c + ratVec σ) * g) =
      ψ (lastEntry c) * cornerSum F m K W (xcPoint F X c * g) := by
  have h1 : ψ (lastEntry (c + ratVec σ)) = ψ (lastEntry c) := isPeriodic_lastEntry hψF c σ
  have h2 : cornerSum F m K W (xcPoint F (X + ratVec ρ) (c + ratVec σ) * g) =
      cornerSum F m K W (xcPoint F X (c + ratVec σ) * g) := hW.isPeriodic_rect hψF _ g X ρ
  have h3 : cornerSum F m K W (xcPoint F X (c + ratVec σ) * g) =
      cornerSum F m K W (xcPoint F X c * g) := hW.isPeriodic_col hψF X g c σ
  rw [h1, h2, h3]

include hψF hψc hψ1 in
/-- **The coefficient along `Y_(m+K+1,m)` of the transpose-inverse of a corner sum is the dual
period**: if the corner sum `S` of `W` is left invariant under `GL_(m+K+1)(F)`, then the
projection-character coefficient of `g ↦ S(ᵗg⁻¹)` at `x` is the dual period of `W` at
`w ᵗx⁻¹`, `w = diag(I_m, w_(K+1))`. -/
theorem DualData.coefficient_eq_dualPeriod (hW : DualData F m ψ K W)
    (hWΓ : ∀ k ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F (m + K + 1)), ∀ x,
      cornerSum F m K W (k * x) = cornerSum F m K W x)
    (x : Points F (m + K + 1)) :
    subgroupCharacterCoefficient F (Scheme F (m + K + 1)) (projectionUnipotent F (m + K + 1) m)
        (projectionCharacter F (m + K) m ψ)
        (fun g => cornerSum F m K W (iota F (m + K + 1) g)) x =
      dualPeriod F m K ψ W (wPoint * iota F (m + K + 1) x) := by
  have hfc : Continuous fun g => cornerSum F m K W (iota F (m + K + 1) g) :=
    hW.continuous_cornerSum.comp (UnequalAnalytic.continuous_iota F _)
  have hfΓ : ∀ k ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F (m + K + 1)), ∀ y,
      cornerSum F m K W (iota F (m + K + 1) (k * y)) =
        cornerSum F m K W (iota F (m + K + 1) y) := by
    intro k hk y
    rw [UnequalAnalytic.iota_mul, hWΓ _ (iota_mem_rationalSubgroup hk)]
  rw [coefficient_eq_iterated ψ hψc hψF _ hfc hfΓ x]
  unfold dualPeriod
  set Z := wPoint * iota F (m + K + 1) x with hZ
  have hH : ∀ (l : AdelicSubgroupPoints.rationalSubgroup F (Scheme F K) (upperUnipotent F K))
      (v : unipotentAdelic F K),
      ψ (superSum F (((l : unipotentAdelic F K) * v : unipotentAdelic F K) : Points F K)) *
          rectPeriod F m K ψ (cornerSum F m K W)
            (midPoint F (((l : unipotentAdelic F K) * v : unipotentAdelic F K) : Points F K) * Z) =
        ψ (superSum F (v : Points F K)) *
          rectPeriod F m K ψ (cornerSum F m K W) (midPoint F (v : Points F K) * Z) := by
    intro l v
    rw [Subgroup.coe_mul, superSum_mul F _ _ (isUnitriangular_of_mem_unipotentAdelic F l)
      (isUnitriangular_of_mem_unipotentAdelic F v), AddChar.map_add_eq_mul,
      superSum_rational_char hψF l.property, one_mul,
      hW.rectPeriod_midPoint_rat_mul hψF hψc l.property]
  have hswap : unipotentPeriod F K (fun u => ψ (superSum F
      ((dualConjUnipotent F K u : unipotentAdelic F K) : Points F K)) *
        rectPeriod F m K ψ (cornerSum F m K W)
          (midPoint F ((dualConjUnipotent F K u : unipotentAdelic F K) : Points F K) * Z)) =
      unipotentPeriod F K (fun u => ψ (superSum F (u : Points F K)) *
        rectPeriod F m K ψ (cornerSum F m K W) (midPoint F (u : Points F K) * Z)) := by
    unfold unipotentPeriod
    beta_reduce
    rw [setIntegral_comp_dualConjUnipotent F K (G := fun v : unipotentAdelic F K =>
      ψ (superSum F (v : Points F K)) *
        rectPeriod F m K ψ (cornerSum F m K W) (midPoint F (v : Points F K) * Z)) hH]
  rw [← hswap]
  refine congrArg (unipotentPeriod F K) (funext fun u => ?_)
  rw [coe_dualConjUnipotent]
  have hpt : ∀ A : Fin (m + 1) × Fin K → Adeles F,
      cornerSum F m K W (iota F (m + K + 1)
          (((yHom F m K (Multiplicative.ofAdd A) * brHom F m K u : YGroup F m K) :
            Points F (m + K + 1)) * x)) *
        starRingEnd ℂ (projectionCharacter F (m + K) m ψ
          (yHom F m K (Multiplicative.ofAdd A) * brHom F m K u)) =
      ψ (superSum F (dualConj F K (u : Points F K))) *
        (ψ (lastEntry (rectC A)) * cornerSum F m K W (xcPoint F (rectX A) (rectC A) *
          (midPoint F (dualConj F K (u : Points F K)) * Z))) := by
    intro A
    have hcoe : ((yHom F m K (Multiplicative.ofAdd A) * brHom F m K u : YGroup F m K) :
        Points F (m + K + 1)) = yPoint A * brPoint (u : Points F K) := by
      rw [Subgroup.coe_mul, coe_yHom, coe_brHom, toAdd_ofAdd]
    have hι : iota F (m + K + 1) (yPoint A * brPoint (u : Points F K)) =
        wPoint * (xcPoint F (rectX A) (rectC A) * midPoint F (dualConj F K (u : Points F K))) *
          wPoint := by
      rw [← wPoint_iota_conj]
      simp only [← mul_assoc]
      rw [wPoint_mul_wPoint, one_mul, mul_assoc, wPoint_mul_wPoint, mul_one]
    rw [hcoe, UnequalAnalytic.iota_mul, hι, projectionCharacter_mul, map_mul,
      conj_projectionCharacter_yHom hψ1, conj_projectionCharacter_brHom hψ1]
    have hS : cornerSum F m K W (wPoint * (xcPoint F (rectX A) (rectC A) *
        midPoint F (dualConj F K (u : Points F K))) * wPoint * iota F (m + K + 1) x) =
        cornerSum F m K W (xcPoint F (rectX A) (rectC A) *
          (midPoint F (dualConj F K (u : Points F K)) * Z)) := by
      rw [hZ, mul_assoc, mul_assoc, hWΓ _ wPoint_mem_rationalSubgroup]
      simp only [mul_assoc]
    rw [hS]
    ring
  rw [Langlands.Automorphic.CuspidalWhittaker.torusIntegral_congr hpt,
    Langlands.Automorphic.CuspidalWhittaker.torusIntegral_const_mul,
    torusIntegral_rectCoords (fun X c => ψ (lastEntry c) * cornerSum F m K W
      (xcPoint F X c * (midPoint F (dualConj F K (u : Points F K)) * Z)))
      (hW.continuous_rectIntegrand hψc _) (hW.periodic_rectIntegrand hψF _)]
  rfl

end Bridge

end Langlands.Global.RankinSelbergGlobal.Unfolding
