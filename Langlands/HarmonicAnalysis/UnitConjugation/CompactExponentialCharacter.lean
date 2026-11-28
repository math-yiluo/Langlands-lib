import Langlands.HarmonicAnalysis.UnitConjugation.ExponentialCongruenceQuotient
import Langlands.HarmonicAnalysis.UnitConjugation.ExponentialProductStraighteningStatement
import Langlands.Representation.Character.FiniteOrbitCharacter
import Langlands.Representation.Smooth.Definitions

/-! # Characters on small compact unit groups in exponential coordinates -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open Function Filter Metric _root_.Topology Langlands.Representation.Character

universe u v

local notation "B(" R "," h ")" => OpenAddSubgroup.toAddSubgroup
  (IsUltrametricDist.closedBall_openAddSubgroup R h)
local notation "K(" R "," h "," k ")" => normUnitCongruence (R := R) (le_of_lt h) k

variable {F : Type u} {R : Type v} [NontriviallyNormedField F] [CompleteSpace F] [CharZero F]
  [IsUltrametricDist F] [NormedRing R] [NormedAlgebra F R] [IsUltrametricDist R]
  [ProperSpace R] [FiniteDimensional F R]

omit [IsUltrametricDist F] [IsUltrametricDist R] [ProperSpace R] in
include F in
private theorem exp_conjugation (a : Rˣ) (x : R) :
    NormedSpace.exp (conjugationHomeomorph a x) =
      conjugationHomeomorph a (NormedSpace.exp x) := by
  let e : R ≃ₐ[F] R :=
    { toRingEquiv := MulSemiringAction.toRingEquiv _ R (ConjAct.toConjAct a)
      commutes' := fun c => by
        change (a : R) * algebraMap F R c * ↑a⁻¹ = algebraMap F R c
        rw [← Algebra.commutes c (a : R), mul_assoc, Units.mul_inv, mul_one] }
  have h (y : R) : e y = conjugationHomeomorph a y := by
    rw [conjugationHomeomorph_eq_smul]
    rfl
  have he := map_exp_sub_one (F := F) e x
  rw [map_sub, map_one, h, h, sub_left_inj] at he
  exact he.symm

/-- The exponential product change of variables turns locally constant sums
of additive characters invariant under the larger congruence group into
characters of actual smooth finite-dimensional representations. -/
def CompactExponentialCharacterStatement (F : Type u) (R : Type v)
    [NontriviallyNormedField F] [CompleteSpace F] [CharZero F] [IsUltrametricDist F]
    [NormedRing R] [NormedAlgebra F R] [IsUltrametricDist R] [ProperSpace R]
    [FiniteDimensional F R] : Prop :=
  ExponentialProductStraighteningStatement F R →
  ∃ c : ℝ, 1 ≤ c ∧ ∃ ε > (0 : ℝ), max 1 ‖(1 : R)‖ * (c * ε) < 1 ∧
    ∀ (r : ℝ) (hr : 0 < r) (hr₁ : r < 1), r ≤ ε →
      ∀ S : Finset (AddChar B(R, hr) ℂ),
        (∀ χ ∈ S, IsLocallyConstant (χ : B(R, hr) → ℂ)) →
        (∀ a : Rˣ, ‖(a : R) - 1‖ ≤ c * r → ∀ x y : B(R, hr),
          (y : R) = conjugationHomeomorph a (x : R) → ∑ χ ∈ S, χ y = ∑ χ ∈ S, χ x) →
        ∃ (W : Type v) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W)
          (ρ : Representation ℂ K(R, hr, hr₁) W), IsSmooth ρ ∧
          ∀ (x : B(R, hr)) (k : K(R, hr, hr₁)),
            (k.val : R) = NormedSpace.exp (x : R) → ρ.character k = ∑ χ ∈ S, χ x

theorem compactExponentialCharacter : CompactExponentialCharacterStatement F R := by
  classical
  intro hStraighten
  obtain ⟨c, hc, ε₁, hε₁, _, hΦ⟩ := hStraighten
  obtain ⟨ε₂, hε₂, hQ⟩ := exponentialCongruenceQuotient (F := F) (R := R)
  let m := max 1 ‖(1 : R)‖
  have hm : 1 ≤ m := le_max_left _ _
  have hmc : 0 < m * c := mul_pos (zero_lt_one.trans_le hm) (zero_lt_one.trans_le hc)
  let ε := min (min ε₁ ε₂) (1 / (2 * (m * c)))
  have hε : 0 < ε := lt_min (lt_min hε₁ hε₂) (one_div_pos.mpr (mul_pos (by norm_num) hmc))
  have hsmall : m * (c * ε) < 1 := by
    calc
      _ = (m * c) * ε := by rw [mul_assoc]
      _ ≤ (m * c) * (1 / (2 * (m * c))) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hmc.le
      _ = 1 / 2 := by field_simp
      _ < 1 := by norm_num
  refine ⟨c, hc, ε, hε, hsmall, fun r hr hr₁ hrε S hLC hInv => ?_⟩
  have hcR : r ≤ c * r := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hc hr.le
  have hrsmall : m * r < 1 := calc
    _ ≤ m * (c * ε) :=
      mul_le_mul_of_nonneg_left (hcR.trans (mul_le_mul_of_nonneg_left hrε (zero_le_one.trans hc)))
        (zero_le_one.trans hm)
    _ < _ := hsmall
  have hsmall₁ := hrε.trans ((min_le_left _ _).trans (min_le_left ε₁ ε₂))
  have hsmall₂ := hrε.trans ((min_le_left _ _).trans (min_le_right ε₁ ε₂))
  obtain ⟨Φ, hΦ⟩ := hΦ r hr hsmall₁
  let Ψ : (B(R, hr) × B(R, hr)) ≃ᵢ (B(R, hr) × B(R, hr)) := Φ
  have hΨ (x : B(R, hr) × B(R, hr)) :
      NormedSpace.exp (((Ψ x).1 : R) + ((Ψ x).2 : R)) =
        NormedSpace.exp (x.1 : R) * NormedSpace.exp (x.2 : R) ∧
      ∃ a b : Rˣ, ‖(a : R) - 1‖ ≤ c * r ∧ ‖(b : R) - 1‖ ≤ c * r ∧
        ((Ψ x).1 : R) = conjugationHomeomorph a (x.1 : R) ∧
        ((Ψ x).2 : R) = conjugationHomeomorph b (x.2 : R) := hΦ x
  have hOne : ∀ᶠ x : B(R, hr) in 𝓝 0, ∀ χ ∈ S, χ x = 1 :=
    (eventually_all_finset S).2 fun χ hχ => by simpa only [AddChar.map_zero_eq_one] using
      ((hLC χ hχ).eventually_eq (0 : B(R, hr)))
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hOne
  let s := min (δ / 2) (1 / 2)
  have hs : 0 < s := lt_min (half_pos hδ) (by norm_num)
  have hs₁ : s < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hsδ : s < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  let K := K(R, hr, hr₁)
  let B := B(R, hr)
  let M := unitCongruenceLevel (R := R) hr hr₁ hs hs₁
  let N := additiveCongruenceLevel (R := R) hr hs
  let : M.Normal := unitCongruenceLevel_normal hr hr₁ hrsmall hs hs₁
  let P := K ⧸ M
  let Q := B ⧸ N
  let p := QuotientGroup.mk' M
  let q := QuotientAddGroup.mk' N
  have hp : Surjective p := QuotientGroup.mk'_surjective M
  have hq : Surjective q := QuotientAddGroup.mk'_surjective N
  obtain ⟨hfin, E, hE⟩ := hQ r hr hr₁ hsmall₂ hrsmall s hs hs₁
  let : Finite P := hfin
  let : Fintype P := Fintype.ofFinite P
  let : Finite Q := Finite.of_injective E E.injective
  let : Fintype Q := Fintype.ofFinite Q
  obtain ⟨Ψ', hΨ'⟩ := additiveCongruencePairEquiv hr hs Ψ
  have hψ (χ : S) : N ≤ χ.val.toAddMonoidHom.ker := by
    intro x hx
    have hx' : dist x (0 : B) ≤ s := hx
    exact hδsub (mem_ball.mpr (hx'.trans_lt hsδ)) χ.val χ.property
  let ψ (χ : S) : AddChar Q ℂ :=
    AddChar.toAddMonoidHomEquiv.symm (QuotientAddGroup.lift N χ.val.toAddMonoidHom (hψ χ))
  have hψq (χ : S) (x : B) : ψ χ (q x) = χ.val x := rfl
  have hInj : Injective ψ := by
    intro χ η h
    exact Subtype.ext (AddChar.ext _ _ fun x => by
      rw [← hψq χ x, ← hψq η x, h])
  let I := S.attach.map ⟨ψ, hInj⟩
  let f (x : Q) : ℂ := ∑ χ ∈ I, χ x
  have hf (x : B) : f (q x) = ∑ χ ∈ S, χ x := by
    rw [show f (q x) = ∑ χ ∈ S.attach.map ⟨ψ, hInj⟩, χ (q x) from rfl, Finset.sum_map]
    simp only [Function.Embedding.coeFn_mk, hψq]
    exact Finset.sum_attach S (fun χ : AddChar B ℂ => χ x)
  have hMul (z : Q × Q) : E ((Ψ' z).1 + (Ψ' z).2) = E z.1 * E z.2 := by
    obtain ⟨x, hx⟩ := hq z.1
    obtain ⟨y, hy⟩ := hq z.2
    have hz : z = (q x, q y) := Prod.ext hx.symm hy.symm
    obtain ⟨a, ha, ha'⟩ := hE x
    obtain ⟨b, hb, hb'⟩ := hE y
    obtain ⟨d, hd, hd'⟩ := hE ((Ψ (x,y)).1 + (Ψ (x,y)).2)
    have hdab : d = a * b := by
      apply Subtype.ext
      apply Units.ext
      exact hd.trans (((hΨ (x,y)).1).trans (congrArg₂ (· * ·) ha.symm hb.symm))
    rw [hz, show Ψ' (q x, q y) = (q (Ψ (x,y)).1, q (Ψ (x,y)).2) from hΨ' (x,y)]
    change E (q (Ψ (x,y)).1 + q (Ψ (x,y)).2) = E (q x) * E (q y)
    rw [← map_add, show E (q _) = p d from hd', show E (q x) = p a from ha',
      show E (q y) = p b from hb', hdab, map_mul]
  have hPres (z : Q × Q) : f (Ψ' z).1 = f z.1 ∧ f (Ψ' z).2 = f z.2 := by
    obtain ⟨x, hx⟩ := hq z.1
    obtain ⟨y, hy⟩ := hq z.2
    have hz : z = (q x, q y) := Prod.ext hx.symm hy.symm
    obtain ⟨a, b, ha, hb, hx', hy'⟩ := (hΨ (x,y)).2
    rw [hz, show Ψ' (q x, q y) = (q (Ψ (x,y)).1, q (Ψ (x,y)).2) from hΨ' (x,y)]
    change f (q (Ψ (x,y)).1) = f (q x) ∧ f (q (Ψ (x,y)).2) = f (q y)
    rw [hf, hf, hf, hf]
    exact ⟨hInv a ha x _ hx', hInv b hb y _ hy'⟩
  have hConj (a b : P) : f (E.symm (a * b * a⁻¹)) = f (E.symm b) := by
    obtain ⟨k, rfl⟩ := hp a
    obtain ⟨x, hx⟩ := hq (E.symm b)
    obtain ⟨j, hj, hj'⟩ := hE x
    have hb : b = p j := by
      rw [← (E.apply_symm_apply b), ← hx]
      exact hj'
    have hk : ‖(k.val : R) - 1‖ ≤ c * r := (show ‖(k.val : R) - 1‖ ≤ r from k.property).trans hcR
    let y : B := ⟨conjugationHomeomorph k.val x, by
      change dist (conjugationHomeomorph k.val x) 0 ≤ r
      rw [dist_zero_right, norm_conjugation_eq_of_mem_normUnitCongruence hr.le hr₁ hrsmall k.property]
      exact (dist_zero_right (x : R)) ▸ x.property⟩
    obtain ⟨l, hl, hl'⟩ := hE y
    have hlkj : l = k * j * k⁻¹ := by
      apply Subtype.ext
      apply Units.ext
      change (l.val : R) = conjugationHomeomorph k.val (j.val : R)
      rw [hl, hj]
      exact exp_conjugation (F := F) k.val x
    have hEq : E.symm (p k * b * (p k)⁻¹) = q y := by
      apply E.injective
      rw [E.apply_symm_apply, show E (q y) = p l from hl', hb, hlkj, map_mul, map_mul, map_inv]
    rw [hEq, ← hx, hf, hf]
    exact hInv k.val hk x y rfl
  obtain ⟨W, _, _, _, ρ, hρ⟩ := finiteOrbitCharacter E Ψ' I hConj hMul hPres
  refine ⟨W, inferInstance, inferInstance, inferInstance, ρ.comp p, ?_, ?_⟩
  · intro w
    have hM : IsOpen (M : Set K) := (isOpen_normUnitCongruence hs hs₁).preimage continuous_subtype_val
    refine ⟨⟨M, hM⟩, fun j => ?_⟩
    change ρ (p j.val) w = w
    rw [show p j.val = 1 from (QuotientGroup.eq_one_iff j.val).mpr j.property, map_one]
    rfl
  intro x k hk
  obtain ⟨j, hj, hE'⟩ := hE x
  have hkj : k = j := Subtype.ext (Units.ext (hk.trans hj.symm))
  rw [hkj]
  change ρ.character (p j) = _
  rw [← (show E (q x) = p j from hE'), hρ]
  exact hf x

end Langlands.HarmonicAnalysis.UnitConjugation
