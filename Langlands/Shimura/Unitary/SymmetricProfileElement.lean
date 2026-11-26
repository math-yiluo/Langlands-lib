import Langlands.Shimura.Unitary.AuxiliarySplitPlace
import Langlands.Shimura.Unitary.SplitSpectrumCondition
import Langlands.Shimura.Unitary.SymmetricRootField
import Langlands.Shimura.Unitary.SymmetricWeakApproximation

/-! # A symmetric element with a prescribed set of split spectra -/

noncomputable section

namespace Langlands.Shimura.FiniteUnitary

open NumberField _root_.Algebra _root_.Polynomial Langlands.CentralSimple
open Langlands.Global (FiniteCompletion)
open Langlands.Global.AdelicFunctoriality

universe u v

variable {E : Type u} {K A : Type v}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K] [Algebra E K] [IsQuadraticExtension E K]
  [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
  [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)

omit [NumberField E] [IsTotallyReal E] in
private theorem exists_place_of_realEmbedding (τ : E →+* ℝ) :
    ∃ w : InfinitePlace E, ∃ hw : w.IsReal, InfinitePlace.embedding_of_isReal hw = τ := by
  let c := Complex.ofRealHom.comp τ
  have hc : ComplexEmbedding.IsReal c := ComplexEmbedding.isReal_iff.mpr (by
    ext x
    simp [c, ComplexEmbedding.conjugate_coe_eq])
  refine ⟨InfinitePlace.mk c, InfinitePlace.isReal_mk_iff.mpr hc, RingHom.ext fun x => ?_⟩
  apply Complex.ofReal_injective
  rw [InfinitePlace.embedding_of_isReal_apply]
  exact congrArg (fun g : E →+* ℂ => g x) (InfinitePlace.embedding_mk_eq_of_isReal hc)

variable (s S : Finset (Langlands.Global.FinitePlace E))
  (hS : ∀ p ∈ S, ¬ IsSplitPlace E K p)
  (hz : ∀ p ∉ s, ∀ q : FinitePlacesAbove K p, HasCompletedBrauerInvariant K A q.val 0)
  (hdisj : Disjoint S s)

set_option maxRecDepth 4096 in
include hS hz hdisj in
private theorem exists_symmetricProfileElement :
    ∃ a : A, ∃ ha : D.involution a = a,
      Irreducible (reducedCharpoly K A a) ∧
      (∀ p ∈ S, ((symmetricReducedCharpoly D ha).val.map (algebraMap E (FiniteCompletion E p))).Splits) ∧
      (∀ τ : E →+* ℝ, ((symmetricReducedCharpoly D ha).val.map τ).Splits) := by
  classical
  let : FiniteDimensional E A := Module.Finite.trans K A
  let B := Module.finBasis E A
  let p₀ := splitPlaceOutside (K := K) s
  have h₀ : p₀.val ∉ S := fun h => hS p₀.val h p₀.property.2
  let J := insert p₀.val S
  let goal (p : J) (a : A) : Prop :=
    if p.val = p₀.val then Irreducible (reducedCharpoly K A a)
    else ∀ ha : D.involution a = a,
      ((symmetricReducedCharpoly D ha).val.map (algebraMap E (FiniteCompletion E p.val))).Splits
  let U (p : J) : SymmetricCoordinateCondition D.involution B (FiniteCompletion E p.val) (goal p) := by
    by_cases hp : p.val = p₀.val
    · have hps : p.val ∉ s := by rw [hp]; exact p₀.property.1
      have hs : IsSplitPlace E K p.val := by rw [hp]; exact p₀.property.2
      simpa only [goal, ite_eq_left hp] using
        splitIrreducibleCoordinateCondition D B p.val (Classical.choice hs)
          (hz p.val hps (placeAbove K p.val))
    · have hmem := Finset.mem_insert.mp p.property
      have hmem : p.val ∈ S := hmem.resolve_left hp
      have hps : p.val ∉ s := fun h => (Finset.disjoint_left.mp hdisj) hmem h
      simpa only [goal, ite_eq_right hp] using
        nonsplitSplitSpectrumCondition D B p.val (hS p.val hmem) (hz p.val hps)
  let V (w : InfinitePlace E) := infiniteSplitSpectrumCondition D B w (IsTotallyReal.isReal w)
  let a := symmetricWeakApproximation D.involution B J (fun p => (U p).carrier)
    (fun w => (V w).carrier) (fun p => (U p).isOpen_carrier) (fun w => (V w).isOpen_carrier)
    (fun p => (U p).fixedPoint) (fun w => (V w).fixedPoint)
  have ha := a.property.1
  refine ⟨a.val, ha, ?_, ?_, ?_⟩
  · let p : J := ⟨p₀.val, Finset.mem_insert_self _ _⟩
    have h := (U p).implies a.val ha (a.property.2.1 p)
    change goal p _ at h
    simpa only [goal, ite_eq_left (show p.val = p₀.val from rfl)] using h
  · intro p hp
    let q : J := ⟨p, Finset.mem_insert_of_mem hp⟩
    have h := (U q).implies a.val ha (a.property.2.1 q)
    change goal q _ at h
    have hq : q.val ≠ p₀.val := fun he => h₀ (he ▸ hp)
    have h' : ∀ ha : D.involution a.val = a.val,
        ((symmetricReducedCharpoly D ha).val.map (algebraMap E (FiniteCompletion E q.val))).Splits := by
      simpa only [goal, ite_eq_right hq] using h
    exact h' ha
  · intro τ
    obtain ⟨w, hw, hτ⟩ := exists_place_of_realEmbedding τ
    rw [← hτ]
    exact (V w).implies a.val ha (a.property.2.2 w) ha

/-- A symmetric element with irreducible reduced polynomial and split descended
polynomial at the prescribed nonsplit finite places and every real embedding. -/
def symmetricProfileElement :
    {a : A // ∃ ha : D.involution a = a,
      Irreducible (reducedCharpoly K A a) ∧
      (∀ p ∈ S, ((symmetricReducedCharpoly D ha).val.map (algebraMap E (FiniteCompletion E p))).Splits) ∧
      (∀ τ : E →+* ℝ, ((symmetricReducedCharpoly D ha).val.map τ).Splits)} :=
  ⟨(exists_symmetricProfileElement D s S hS hz hdisj).choose,
    (exists_symmetricProfileElement D s S hS hz hdisj).choose_spec⟩

end Langlands.Shimura.FiniteUnitary
