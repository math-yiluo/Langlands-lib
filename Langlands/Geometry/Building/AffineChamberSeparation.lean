import Langlands.Geometry.Building.AffineChamberTransitivityStatement
import Langlands.Geometry.Building.IwahoriWeylChamberLemmas

/-! # Finite separation and transport for affine chambers -/

noncomputable section

universe uV uA

namespace Langlands.Geometry.Building.AffineRootSystem

variable {V : Type uV} {A : Type uA} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
variable {Ψ : Set (A →ᵃ[ℝ] ℝ)}

/-- Roots whose zero hyperplane meets the closed segment with endpoints `x`, `y`.
The endpoint sign criterion also includes roots vanishing at an endpoint. -/
def segmentRoots (Ψ : Set (A →ᵃ[ℝ] ℝ)) (x y : A) : Set (A →ᵃ[ℝ] ℝ) :=
  {ψ | ψ ∈ Ψ ∧ ψ x * ψ y ≤ 0}

/-- Corrected AR4 and finitely many derivatives give finitely many roots with
bounded value at a point, allowing a bound that depends on the derivative. -/
theorem IsAffineRootSystemWithRankZero.finite_bounded_at
    (hΨ : IsAffineRootSystemWithRankZero Ψ) (x : A)
    (bound : Module.Dual ℝ V → ℝ) :
    {ψ | ψ ∈ Ψ ∧ |ψ x| ≤ bound ψ.linear}.Finite := by
  have hfib : ∀ a ∈ derivativeRoots Ψ,
      {ψ | ψ ∈ Ψ ∧ ψ.linear = a ∧ |ψ x| ≤ bound a}.Finite := by
    intro a ha
    obtain ⟨η, hη, hηa⟩ := ha
    change η.linear = a at hηa
    refine (hΨ.finite_bounded η hη (bound a + |η x|)).subset ?_
    rintro ψ ⟨hψ, hψa, hbound⟩
    refine ⟨hψ, hψa.trans hηa.symm, fun z => ?_⟩
    have hlin : (ψ - η).linear = 0 := by
      change ψ.linear - η.linear = 0
      rw [hψa, hηa, sub_self]
    change |(ψ - η) z| ≤ bound a + |η x|
    rw [apply_eq_apply_of_linear_eq_zero hlin z x]
    exact (abs_sub _ _).trans (by linarith)
  refine (hΨ.finite_derivativeRoots.biUnion hfib).subset ?_
  intro ψ hψ
  exact Set.mem_iUnion.2 ⟨ψ.linear, Set.mem_iUnion.2
    ⟨linear_mem_derivativeRoots hψ.1, hψ.1, rfl, hψ.2⟩⟩

/-- Only finitely many affine roots can vanish on the closed segment between two
points; the algebraic endpoint condition includes roots vanishing at an endpoint. -/
theorem IsAffineRootSystemWithRankZero.finite_segment_roots
    (hΨ : IsAffineRootSystemWithRankZero Ψ) (x y : A) :
    (segmentRoots Ψ x y).Finite := by
  refine (hΨ.finite_bounded_at x (fun a => |a (y -ᵥ x)|)).subset ?_
  rintro ψ ⟨hψ, hsep⟩
  refine ⟨hψ, ?_⟩
  rw [AffineMap.linearMap_vsub, vsub_eq_sub]
  apply sq_le_sq.mp
  nlinarith [sq_nonneg (ψ y)]

/-- In particular this is the actual affine Weyl group action on chamber subsets. -/
theorem IsChamber.image_affineWeylGroup {C : Set A} (hC : IsChamber Ψ C)
    (w : affineWeylGroup Ψ) : IsChamber Ψ ((w : A ≃ᵃ[ℝ] A) '' C) :=
  hC.image (affineWeylGroup_le_rootStabilizer Ψ w.property)

/-- Rank zero: no roots generate only the identity affine automorphism. -/
@[simp] theorem affineWeylGroup_empty :
    affineWeylGroup (∅ : Set (A →ᵃ[ℝ] ℝ)) = ⊥ := by
  simp [affineWeylGroup]

/-- For the empty arrangement every chamber is the whole torsor. -/
theorem IsChamber.eq_univ_of_empty {C : Set A}
    (hC : IsChamber (∅ : Set (A →ᵃ[ℝ] ℝ)) C) : C = Set.univ := by
  obtain ⟨x, _, rfl⟩ := hC
  simp [facet, facetRel]

/-- Empty arrangements already satisfy the exact simple-transitivity conclusion. -/
theorem existsUnique_chamber_transport_empty (C D : Set A)
    (hC : IsChamber (∅ : Set (A →ᵃ[ℝ] ℝ)) C)
    (hD : IsChamber (∅ : Set (A →ᵃ[ℝ] ℝ)) D) :
    ∃! w : affineWeylGroup (∅ : Set (A →ᵃ[ℝ] ℝ)),
      (w : A ≃ᵃ[ℝ] A) '' C = D := by
  refine ⟨1, ?_, fun w _ => ?_⟩
  · rw [hC.eq_univ_of_empty, hD.eq_univ_of_empty]
    exact Set.image_id _
  · apply Subtype.ext
    have hw := w.property
    simpa only [affineWeylGroup_empty, Subgroup.mem_bot, OneMemClass.coe_one] using hw

end Langlands.Geometry.Building.AffineRootSystem
