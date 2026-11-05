import Langlands.Geometry.Building.HalfWallRootFactorization
import Langlands.GroupScheme.Rational.RootFactorizationFromExistence

/-! # Ordinary roots representing extended affine roots -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.KPApartmentData

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
    {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- Without a doubled derivative root, every jump is an ordinary affine root. -/
theorem mem_affineRoots_of_not_double_root
    {a : relativeRoots i} (h2a : 2 • (a : characterLattice S) ∉ relativeRoots i)
    {ψ : D.Apartment →ᵃ[ℝ] ℝ} (hlin : ψ.linear = rootForm i a)
    (hjump : D.affineRootGroupPlus a ψ ≠ D.affineRootGroup a ψ) :
    ψ ∈ D.affineRoots := by
  refine ⟨a, hlin, ?_⟩
  intro hsub
  apply hjump
  apply le_antisymm (D.affineRootGroupPlus_le a ψ)
  intro g hg
  obtain ⟨v, hv, w, hw, hvw⟩ := hsub hg
  have hw1 : w = 1 := by
    change w ∈ doubleRootGroupPoints i (a : characterLattice S) at hw
    rw [doubleRootGroupPoints, ite_eq_right h2a] at hw
    exact Subgroup.mem_bot.mp hw
  change v * w = g at hvw
  rw [hw1, mul_one] at hvw
  exact hvw ▸ hv

/-- V4 gives the strict doubled-root inclusion at every affine depth. -/
theorem affineRootGroupPlus_double_le
    {a : relativeRoots i} (h2a : 2 • (a : characterLattice S) ∈ relativeRoots i)
    {ψ : D.Apartment →ᵃ[ℝ] ℝ} (hlin : ψ.linear = rootForm i a) :
    D.affineRootGroupPlus (2 • (a : characterLattice S)) ((2 : ℝ) • ψ) ≤
      D.affineRootGroupPlus a ψ := by
  have hlin2 : ((2 : ℝ) • ψ).linear =
      rootForm i ⟨2 • (a : characterLattice S), h2a⟩ := by
    rw [AffineMap.smul_linear, hlin, rootForm_nsmul a.property 2 h2a]
    norm_num
  obtain ⟨x⟩ := (inferInstance : Nonempty D.Apartment)
  intro g hg
  rw [mem_affineRootGroupPlus_iff hlin2 x] at hg
  apply (mem_affineRootGroupPlus_iff hlin x).2
  refine ⟨RelativeRoot.double_subgroup_le i a (Over.mk (𝟙 _)) hg.1, ?_⟩
  have hd := hg.2
  rw [x.isValuation.double a a.property h2a g hg.1, two_nsmul] at hd
  change ((2 * ψ x : ℝ) : WithTop ℝ) < x.val a g + x.val a g at hd
  induction hv : x.val a g using WithTop.recTopCoe with
  | top => exact WithTop.coe_lt_top _
  | coe t =>
    rw [hv, ← WithTop.coe_add, WithTop.coe_lt_coe] at hd
    rw [WithTop.coe_lt_coe]
    linarith

/-- A nonordinary jump yields a strict filtration jump in the doubled direction. -/
theorem affineRootGroupPlus_double_ne_of_not_mem_affineRoots
    {a : relativeRoots i} (h2a : 2 • (a : characterLattice S) ∈ relativeRoots i)
    {ψ : D.Apartment →ᵃ[ℝ] ℝ} (hlin : ψ.linear = rootForm i a)
    (hjump : D.affineRootGroupPlus a ψ ≠ D.affineRootGroup a ψ)
    (hnot : ψ ∉ D.affineRoots) :
    D.affineRootGroupPlus (2 • (a : characterLattice S)) ((2 : ℝ) • ψ) ≠
      D.affineRootGroup (2 • (a : characterLattice S)) ((2 : ℝ) • ψ) := by
  intro heq
  apply hjump
  apply le_antisymm (D.affineRootGroupPlus_le a ψ)
  intro g hg
  obtain ⟨v, hv, w, hw, hvw⟩ :=
    D.affineRootGroup_subset_mul_double_of_not_mem_affineRoots h2a hlin hnot hg
  have hwplus : w ∈ D.affineRootGroupPlus (2 • (a : characterLattice S))
      ((2 : ℝ) • ψ) := by rwa [heq]
  rw [← hvw]
  exact (D.affineRootGroupPlus a ψ).mul_mem hv
    (D.affineRootGroupPlus_double_le h2a hlin hwplus)

variable (hNo4 : ∀ a ∈ relativeRoots i, (4 : ℕ) • a ∉ relativeRoots i)

include hNo4

/-- V4 and absence of quadruple derivative roots imply AS4. -/
theorem mem_or_two_smul_mem_affineRoots_of_no_quadruple
    {ψ : D.Apartment →ᵃ[ℝ] ℝ} (hψ : ψ ∈ D.extendedAffineRoots) :
    ψ ∈ D.affineRoots ∨ (2 : ℝ) • ψ ∈ D.affineRoots := by
  classical
  by_cases h : ψ ∈ D.affineRoots
  · exact Or.inl h
  right
  obtain ⟨a, hlin, hjump⟩ := hψ
  have h2a : 2 • (a : characterLattice S) ∈ relativeRoots i := by
    by_contra hn
    exact h (D.mem_affineRoots_of_not_double_root (a := a) hn hlin hjump)
  have h4a : 2 • (2 • (a : characterLattice S)) ∉ relativeRoots i := by
    simpa only [smul_smul, show (2 : ℕ) * 2 = 4 from rfl] using hNo4 a a.property
  have hlin2 : ((2 : ℝ) • ψ).linear =
      rootForm i ⟨2 • (a : characterLattice S), h2a⟩ := by
    rw [AffineMap.smul_linear, hlin, rootForm_nsmul a.property 2 h2a]
    norm_num
  have hjump2 := D.affineRootGroupPlus_double_ne_of_not_mem_affineRoots
    (a := a) h2a hlin hjump h
  exact D.mem_affineRoots_of_not_double_root
    (a := ⟨2 • (a : characterLattice S), h2a⟩) h4a hlin2 hjump2

open Classical in
/-- Choose the ordinary affine root `ψ`, when available, and `2ψ` otherwise. -/
def ordinaryAffineRootForExtended
    (ψ : D.Apartment →ᵃ[ℝ] ℝ) (hψ : ψ ∈ D.extendedAffineRoots) : D.affineRoots :=
  if h : ψ ∈ D.affineRoots then ⟨ψ, h⟩ else
    ⟨(2 : ℝ) • ψ,
      (D.mem_or_two_smul_mem_affineRoots_of_no_quadruple hNo4 hψ).resolve_left h⟩

theorem ordinaryAffineRootForExtended_eq_or_eq_two_smul
    (ψ : D.Apartment →ᵃ[ℝ] ℝ) (hψ : ψ ∈ D.extendedAffineRoots) :
    (D.ordinaryAffineRootForExtended hNo4 ψ hψ : D.Apartment →ᵃ[ℝ] ℝ) = ψ ∨
      (D.ordinaryAffineRootForExtended hNo4 ψ hψ : D.Apartment →ᵃ[ℝ] ℝ) =
        (2 : ℝ) • ψ := by
  classical
  unfold ordinaryAffineRootForExtended
  split_ifs <;> simp

theorem ordinaryAffineRootForExtended_sign
    (ψ : D.Apartment →ᵃ[ℝ] ℝ) (hψ : ψ ∈ D.extendedAffineRoots)
    (x : D.Apartment) :
    SignType.sign ((D.ordinaryAffineRootForExtended hNo4 ψ hψ :
      D.Apartment →ᵃ[ℝ] ℝ) x) =
      SignType.sign (ψ x) := by
  rcases D.ordinaryAffineRootForExtended_eq_or_eq_two_smul hNo4 ψ hψ with h | h
  · rw [h]
  · rw [h]
    change SignType.sign ((2 : ℝ) * ψ x) = SignType.sign (ψ x)
    simp only [sign_mul, sign_pos (by norm_num : (0 : ℝ) < 2), one_mul]

theorem ordinaryAffineRootForExtended_hyperplane
    (ψ : D.Apartment →ᵃ[ℝ] ℝ) (hψ : ψ ∈ D.extendedAffineRoots) :
    AffineRootSystem.hyperplane (D.ordinaryAffineRootForExtended hNo4 ψ hψ) =
      AffineRootSystem.hyperplane ψ := by
  rcases D.ordinaryAffineRootForExtended_eq_or_eq_two_smul hNo4 ψ hψ with h | h
  · rw [h]
  · rw [h]
    ext x
    change (2 : ℝ) * ψ x = 0 ↔ ψ x = 0
    exact mul_eq_zero.trans (or_iff_right (by norm_num : (2 : ℝ) ≠ 0))

omit hNo4 in
/-- Actual opposite-pair existence excludes quadruple character roots by integrality. -/
theorem no_quadruple_root_of_oppositePairs [Smooth G.X.hom]
    (hS : IsSplitTorus S.toGrp) (hF : RelativeRoot.HasOppositeFactorPairs i) :
    ∀ a ∈ relativeRoots i, (4 : ℕ) • a ∉ relativeRoots i := by
  intro a _ ha4
  have h := hF.eq_one_or_two_of_nsmul_mem i hS ha4
  omega

omit hNo4 in
/-- V4 and actual opposite-pair existence imply AS4 without an apartment-axiom package. -/
theorem mem_or_two_smul_mem_affineRoots_of_oppositePairs [Smooth G.X.hom]
    (hS : IsSplitTorus S.toGrp) (hF : RelativeRoot.HasOppositeFactorPairs i)
    {ψ : D.Apartment →ᵃ[ℝ] ℝ} (hψ : ψ ∈ D.extendedAffineRoots) :
    ψ ∈ D.affineRoots ∨ (2 : ℝ) • ψ ∈ D.affineRoots :=
  D.mem_or_two_smul_mem_affineRoots_of_no_quadruple
    (no_quadruple_root_of_oppositePairs hS hF) hψ

end Langlands.Geometry.Building.KPApartmentData
