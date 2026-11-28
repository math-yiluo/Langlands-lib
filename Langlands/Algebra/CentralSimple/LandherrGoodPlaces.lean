import Langlands.Algebra.CentralSimple.LandherrMainLemmas

/-! # Finiteness of the places where given coordinates fail to be integral -/

noncomputable section

namespace Langlands.CentralSimple.Landherr

open IsDedekindDomain NumberField

universe u v w

variable {F : Type u} [Field F] [NumberField F] {A : Type v} [Ring A] [Algebra F A]
  {ι : Type w} [Finite ι] (β : Module.Basis ι F A)

/-- An element has integral coordinates at all but finitely many finite places. -/
theorem finite_setOf_not_intAt (a : A) :
    {v : HeightOneSpectrum (𝓞 F) | ¬ IntAt β v a}.Finite := by
  refine (Set.finite_iUnion fun i => HeightOneSpectrum.Support.finite (𝓞 F) (β.repr a i)).subset ?_
  intro v hv
  simp only [Set.mem_ofPred_eq, IntAt, not_forall, not_le] at hv
  obtain ⟨i, hi⟩ := hv
  exact Set.mem_iUnion.mpr ⟨i, hi⟩

/-- Finitely many elements have integral coordinates at all but finitely many finite places. -/
theorem finite_setOf_not_forall_intAt {κ : Type*} [Finite κ] (a : κ → A) :
    {v : HeightOneSpectrum (𝓞 F) | ¬ ∀ j, IntAt β v (a j)}.Finite := by
  refine (Set.finite_iUnion fun j => finite_setOf_not_intAt β (a j)).subset ?_
  intro v hv
  simp only [Set.mem_ofPred_eq, not_forall] at hv
  obtain ⟨j, hj⟩ := hv
  exact Set.mem_iUnion.mpr ⟨j, hj⟩

/-- The structure constants of a finite basis and the coordinates of `1` are integral at
all but finitely many finite places. -/
theorem finite_setOf_not_basisIntAt :
    {v : HeightOneSpectrum (𝓞 F) | ¬ BasisIntAt β v}.Finite := by
  refine ((finite_setOf_not_forall_intAt β fun ij : ι × ι => β ij.1 * β ij.2).union
    (finite_setOf_not_intAt β 1)).subset ?_
  intro v hv
  simp only [Set.mem_ofPred_eq, BasisIntAt, not_and_or] at hv
  rcases hv with hv | hv
  · left
    intro h
    exact hv fun i j k => h (i, j) k
  · right
    exact hv

end Langlands.CentralSimple.Landherr
