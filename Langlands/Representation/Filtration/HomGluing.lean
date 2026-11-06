import Langlands.Representation.Filtration.HomBounds
import Langlands.Representation.Filtration.SingleSurvivingGrade

/-! Hom length and off-distinguished maps for naturally glued representations. -/

noncomputable section

open CategoryTheory

namespace Langlands.HomSpace

universe uK uG uV uW uC vC uH uA

variable {k : Type uK} [Field k] {G : Type uG} [Monoid G]
variable {W : Type uW} [AddCommGroup W] [Module k W]
variable {C : Type uC} [Category.{vC} C]

/-- Source transport along an isomorphism of actual representation objects. -/
def equivLeftOfIso {A B : Rep.{uV} k G} (σ : Representation k G W)
    (e : A ≅ B) : A.ρ.IntertwiningMap σ ≃ₗ[k] B.ρ.IntertwiningMap σ :=
  equivLeft σ (Representation.equivOfIso e)

/-- Natural gluing bounds Hom length by the sum over the supplied pieces,
regardless of the order in which they occur in the filtration. -/
theorem length_le_sum_of_isGluedFrom
    {F : C ⥤ Rep.{uV} k G} {n : ℕ}
    {pieces : Fin n → C ⥤ Rep.{uV} k G}
    (h : IsGluedFrom F pieces) (X : C) (σ : Representation k G W) :
    length (F.obj X).ρ σ ≤ ∑ i : Fin n, length ((pieces i).obj X).ρ σ := by
  classical
  obtain ⟨e, s, hs⟩ := h
  calc
    length (F.obj X).ρ σ ≤
        ∑ i : Fin n, length ((s.atObject X).gradedRepresentation i).ρ σ :=
      length_le_sum (s.atObject X) σ
    _ = ∑ i : Fin n, length ((pieces (e i)).obj X).ρ σ := by
      apply Finset.sum_congr rfl
      intro i _
      exact (equivLeftOfIso σ ((Classical.choice (hs i)).app X)).length_eq
    _ = ∑ i : Fin n, length ((pieces i).obj X).ρ σ :=
      Equiv.sum_comp e (fun i => length ((pieces i).obj X).ρ σ)

/-- If only one supplied piece contributes, it bounds the glued Hom space. -/
theorem length_le_of_single_piece_of_isGluedFrom
    {F : C ⥤ Rep.{uV} k G} {n : ℕ}
    {pieces : Fin n → C ⥤ Rep.{uV} k G}
    (h : IsGluedFrom F pieces) (X : C) (σ : Representation k G W)
    (i₀ : Fin n)
    (hzero : ∀ i, i ≠ i₀ → length ((pieces i).obj X).ρ σ = 0) :
    length (F.obj X).ρ σ ≤ length ((pieces i₀).obj X).ρ σ := by
  classical
  have hsum : ∑ i : Fin n, length ((pieces i).obj X).ρ σ =
      length ((pieces i₀).obj X).ρ σ :=
    Finset.sum_eq_single i₀ (fun i _ hi => hzero i hi)
      (fun h => (h (Finset.mem_univ i₀)).elim)
  exact hsum ▸ length_le_sum_of_isGluedFrom h X σ

/-- Every endomorphism is scalar if the endomorphism space has length at most
one. This also includes representations with zero carrier. -/
theorem exists_scalar_of_length_end_le_one
    {H : Type uH} [Monoid H] {A : Type uA} [AddCommGroup A] [Module k A]
    (η : Representation k H A) (h : length η η ≤ 1)
    (f : η.IntertwiningMap η) :
    ∃ a : k, f = a • Representation.IntertwiningMap.id η := by
  classical
  by_cases hid : Representation.IntertwiningMap.id η = 0
  · refine ⟨0, ?_⟩
    have hf : f = 0 := by
      ext x
      have hx := congrArg (fun t : η.IntertwiningMap η => t x) hid
      change x = 0 at hx
      simp only [hx, map_zero]
    simpa only [zero_smul] using hf
  · exact exists_smul_eq_of_length_le_one η η h _ f hid

/-- Under a supplied endomorphism-to-Hom equivalence, a distinguished piece
of Hom length at most one forces scalarity or an actual nonzero map from
another supplied piece. -/
theorem scalar_or_exists_off_piece_of_isGluedFrom
    {H : Type uH} [Monoid H] {A : Type uA} [AddCommGroup A] [Module k A]
    (η : Representation k H A)
    {F : C ⥤ Rep.{uV} k G} {n : ℕ}
    {pieces : Fin n → C ⥤ Rep.{uV} k G}
    (h : IsGluedFrom F pieces) (X : C) (σ : Representation k G W)
    (e : η.IntertwiningMap η ≃ₗ[k] (F.obj X).ρ.IntertwiningMap σ)
    (i₀ : Fin n) (hone : length ((pieces i₀).obj X).ρ σ ≤ 1)
    (f : η.IntertwiningMap η) :
    (∃ a : k, f = a • Representation.IntertwiningMap.id η) ∨
      ∃ i : Fin n, i ≠ i₀ ∧
        ∃ g : ((pieces i).obj X).ρ.IntertwiningMap σ, g ≠ 0 := by
  classical
  by_cases hoff : ∃ i : Fin n, i ≠ i₀ ∧
      ∃ g : ((pieces i).obj X).ρ.IntertwiningMap σ, g ≠ 0
  · exact Or.inr hoff
  · have hzero : ∀ i, i ≠ i₀ → length ((pieces i).obj X).ρ σ = 0 := by
      intro i hi
      have hz : ∀ g : ((pieces i).obj X).ρ.IntertwiningMap σ, g = 0 := by
        intro g
        by_contra hg
        exact hoff ⟨i, hi, g, hg⟩
      apply Module.length_eq_zero_iff.mpr
      exact ⟨fun g g' => (hz g).trans (hz g').symm⟩
    have hlen : length η η ≤ 1 := calc
      length η η = length (F.obj X).ρ σ := e.length_eq
      _ ≤ length ((pieces i₀).obj X).ρ σ :=
        length_le_of_single_piece_of_isGluedFrom h X σ i₀ hzero
      _ ≤ 1 := hone
    exact Or.inl (exists_scalar_of_length_end_le_one η hlen f)

end Langlands.HomSpace
