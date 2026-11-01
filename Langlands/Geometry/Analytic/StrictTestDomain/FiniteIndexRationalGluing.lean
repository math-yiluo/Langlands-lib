import Langlands.Geometry.Analytic.StrictTestDomain.WholeSpectrumRationalGluingProof
import Mathlib.Data.Fintype.EquivFin

/-! # Strict scalar rational descent with an independent finite index universe -/

noncomputable section

universe u v

namespace Langlands.Analytic.StrictTestDomain

open RationalData

/-- Reindex the published strict theorem through a finite ordinal, retaining an
arbitrary independent universe for the original finite chart family. -/
theorem wholeSpectrumRationalGluing_finiteIndex
    (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (P : PresentedStrictAffinoidAlgebra K)
    (I : Type v) [Finite I] (D : I → RationalData K P)
    (hcover : ∀ x : BanachSpectrum P, ∃ i, x ∈ (D i).locus)
    (s : ∀ i, (D i).algebra)
    (hcompat : ∀ i j, (interLeft (D i) (D j)).restriction (s i) =
      (interRight (D i) (D j)).restriction (s j)) :
    ∃! a : P, ∀ i, (D i).baseMap a = s i := by
  let := Fintype.ofFinite I
  let e : ULift.{u} (Fin (Fintype.card I)) ≃ I :=
    Equiv.ulift.trans (Fintype.equivFin I).symm
  have hc : ∀ x : BanachSpectrum P, ∃ j, x ∈ (D (e j)).locus := by
    intro x
    obtain ⟨i, hi⟩ := hcover x
    exact ⟨e.symm i, by simpa using hi⟩
  obtain ⟨a, ha, hu⟩ := wholeSpectrumRationalGluing K P
    (ULift.{u} (Fin (Fintype.card I))) (fun j => D (e j)) hc
    (fun j => s (e j)) (fun i j => hcompat (e i) (e j))
  refine ⟨a, ?_, ?_⟩
  · intro i
    obtain ⟨j, rfl⟩ := e.surjective i
    exact ha j
  · intro b hb
    exact hu b (fun j => hb (e j))

end Langlands.Analytic.StrictTestDomain
