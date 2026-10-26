import Langlands.Representation.CuspidalSupport.RefinedCuspidalInductionLengthStatement
import Langlands.Representation.Parabolic.RefinedInductionAdmissibility
import Langlands.Representation.Filtration.LengthCriterionProof

/-! The rank-zero case of actual refined cuspidal induction. -/

noncomputable section

namespace Langlands

universe uK uG uV

section Subsingleton

variable {k : Type uK} [Field k] {G : Type uG} [Group G] [TopologicalSpace G]
  [Subsingleton G] {V : Type uV} [AddCommGroup V] [Module k V]

/-- Over a trivial group, an admissible representation has a finite-dimensional
carrier: the whole group is an open subgroup fixing every vector. -/
theorem finite_of_isAdmissible_of_subsingleton {ρ : Representation k G V}
    (h : IsAdmissible ρ) : Module.Finite k V := by
  have hK := h.2 ⊤
  have htop : fixedVectors ρ (⊤ : OpenSubgroup G).toSubgroup = ⊤ := by
    refine eq_top_iff.mpr fun v _ => ?_
    change v ∈ Representation.invariants _
    rw [Representation.mem_invariants]
    intro g
    rw [MonoidHom.comp_apply, Subsingleton.elim ((Subgroup.subtype _) g) 1, map_one]
    rfl
  rw [htop] at hK
  exact Module.Finite.equiv (Submodule.topEquiv)

/-- Over a trivial group, an admissible representation has finite length over
the group algebra. -/
theorem isFiniteLength_of_isAdmissible_of_subsingleton {ρ : Representation k G V}
    (h : IsAdmissible ρ) : IsFiniteLength (MonoidAlgebra k G) ρ.asModule := by
  have := finite_of_isAdmissible_of_subsingleton h
  have : IsNoetherian (MonoidAlgebra k G) ρ.asModule := isNoetherian_of_tower k inferInstance
  have : IsArtinian (MonoidAlgebra k G) ρ.asModule := isArtinian_of_tower k inferInstance
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩

end Subsingleton

section Series

variable {k : Type uK} [Field k] {G : Type uG} [Group G]

/-- A representation of finite length over the group algebra has an actual
composition series. -/
theorem exists_hasCompositionSeriesLength_of_isFiniteLength (A : Rep.{uV} k G)
    (h : IsFiniteLength (MonoidAlgebra k G) A.ρ.asModule) :
    ∃ m : ℕ, HasCompositionSeriesLength A m := by
  obtain ⟨s, h₀, h₁⟩ := isFiniteLength_iff_exists_compositionSeries.mp h
  exact ⟨s.length, LengthCriterionProof.hasCompositionSeriesLength_of_compositionSeries s h₀ h₁⟩

end Series

end Langlands

namespace Langlands.CuspidalSupport

open GeneralLinear Geometric

universe uF uV

/-- The conclusion of the refined cuspidal induction target in total rank zero. -/
theorem refinedCuspidalInductionFiniteLength_rankZero {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (B : BlockShape 0)
    (S : BlockRefinement B) (ω : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier)) :
    letI := T.topology
    IsLeviCuspidal (B.flatten S) ω.ρ →
      letI := T.leviTopologicalGroup B
      let σ := ω.ρ.comp (flattenedLeviEquiv F.Carrier B S).symm.toMonoidHom
      let I : Rep.{max uF uV} ℂ (B.Levi F.Carrier) :=
        Rep.of (T.normalizedRefinedInduced B S σ)
      IsAdmissible I.ρ ∧
        IsFiniteLength (MonoidAlgebra ℂ (B.Levi F.Carrier)) I.ρ.asModule ∧
        ∃ m : ℕ, HasCompositionSeriesLength I m := by
  let := T.topology
  intro hω
  let := T.leviTopologicalGroup B
  let : IsEmpty (Fin B.length) := ⟨fun i =>
    Fin.elim0 (B.indexEquiv ⟨i, ⟨0, B.positive i⟩⟩)⟩
  let : Subsingleton (B.Levi F.Carrier) := inferInstance
  have hI := Parabolic.refinedCuspidalInduction_isAdmissible F T B S ω hω
  exact ⟨hI, isFiniteLength_of_isAdmissible_of_subsingleton hI,
    exists_hasCompositionSeriesLength_of_isFiniteLength _
      (isFiniteLength_of_isAdmissible_of_subsingleton hI)⟩

/-- The target proposition restricted to total rank zero, without the
irreducibility hypothesis. -/
def RefinedCuspidalInductionRankZeroClause : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (B : BlockShape 0) (S : BlockRefinement B)
      (ω : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier)),
      IsLeviCuspidal (B.flatten S) ω.ρ →
        letI := T.leviTopologicalGroup B
        let σ := ω.ρ.comp (flattenedLeviEquiv F.Carrier B S).symm.toMonoidHom
        let I : Rep.{max uF uV} ℂ (B.Levi F.Carrier) :=
          Rep.of (T.normalizedRefinedInduced B S σ)
        IsAdmissible I.ρ ∧
          IsFiniteLength (MonoidAlgebra ℂ (B.Levi F.Carrier)) I.ρ.asModule ∧
          ∃ m : ℕ, HasCompositionSeriesLength I m

theorem refinedCuspidalInductionRankZeroClause_holds :
    RefinedCuspidalInductionRankZeroClause.{uF, uV} :=
  fun _ _ F T B S ω => refinedCuspidalInductionFiniteLength_rankZero F T B S ω

end Langlands.CuspidalSupport
