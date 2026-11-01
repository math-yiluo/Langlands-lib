import Langlands.Representation.Aubert.LengthOrderedSupports
import Langlands.Representation.Aubert.BundledJacquetQuotientDiagram
import Langlands.Representation.Aubert.JacquetCutExactness

/-! Finite lifting from upper singleton grades to the actual Jacquet complex. -/

noncomputable section

namespace Langlands.Aubert.ActualCutComplex

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ}
  (A : letI := T.topology
    SmoothRep.{0,uF,uV} ℂ (GeneralLinear n F.Carrier))
  (C : BlockShape n)

/-- Injectivity on every upper singleton support grade implies injectivity on
the actual Jacquet complex. The finite support chain is constructed here. -/
theorem degreeDifferential_injective_of_upperSingletonGraded (k : ℕ)
    (hinj : ∀ (θ : Set (Equiv.Perm (Fin n))) (w : Equiv.Perm (Fin n)),
      (∀ v ∈ θ, ∀ z, Support.inversionLength v < Support.inversionLength z → z ∈ θ) →
      (∀ v ∈ θ \ {w}, ∀ z,
        Support.inversionLength v < Support.inversionLength z → z ∈ θ \ {w}) →
      w ∈ θ → Function.Injective
        ((bundledSupportQuotientDiagram T A C (θ \ {w}) θ).degreeDifferential k)) :
    Function.Injective ((jacquetDiagram T C A.obj.ρ).degreeDifferential k) := by
  apply degreeDifferential_injective_of_bundledGraded T A C
    (Support.lengthOrderedSupport n) (Support.lengthOrderedSupport_zero n)
    (Support.lengthOrderedWeylList n).length (Support.lengthOrderedSupport_top n) k
  intro i hi
  have hstep := Support.lengthOrderedSupport_step i hi
  rw [hstep]
  apply hinj (Support.lengthOrderedSupport n (i + 1))
    (Support.lengthOrderedWeylEquiv n ⟨i, hi⟩)
    (Support.lengthOrderedSupport_upper (i + 1))
  · rw [← hstep]
    exact Support.lengthOrderedSupport_upper i
  · exact Support.lengthOrderedWeylEquiv_mem_succ i hi

/-- Middle exactness on every upper singleton support grade lifts through the
actual finite increasing support filtration, with unchanged differentials. -/
theorem degreeDifferential_exact_of_upperSingletonGraded (k : ℕ)
    (hex : ∀ (θ : Set (Equiv.Perm (Fin n))) (w : Equiv.Perm (Fin n)),
      (∀ v ∈ θ, ∀ z, Support.inversionLength v < Support.inversionLength z → z ∈ θ) →
      (∀ v ∈ θ \ {w}, ∀ z,
        Support.inversionLength v < Support.inversionLength z → z ∈ θ \ {w}) →
      w ∈ θ →
      LinearMap.range
          ((bundledSupportQuotientDiagram T A C (θ \ {w}) θ).degreeDifferential k) =
        LinearMap.ker
          ((bundledSupportQuotientDiagram T A C (θ \ {w}) θ).degreeDifferential (k + 1))) :
    LinearMap.range ((jacquetDiagram T C A.obj.ρ).degreeDifferential k) =
      LinearMap.ker ((jacquetDiagram T C A.obj.ρ).degreeDifferential (k + 1)) := by
  apply degreeDifferential_exact_of_bundledGraded T A C
    (Support.lengthOrderedSupport n) (Support.lengthOrderedSupport_monotone n)
    (Support.lengthOrderedSupport_zero n) (Support.lengthOrderedWeylList n).length
    (Support.lengthOrderedSupport_top n) k
  intro i hi
  have hstep := Support.lengthOrderedSupport_step i hi
  rw [hstep]
  apply hex (Support.lengthOrderedSupport n (i + 1))
    (Support.lengthOrderedWeylEquiv n ⟨i, hi⟩)
    (Support.lengthOrderedSupport_upper (i + 1))
  · rw [← hstep]
    exact Support.lengthOrderedSupport_upper i
  · exact Support.lengthOrderedWeylEquiv_mem_succ i hi

/-- Explicit lower concentration of all genuine upper singleton support grades.
The terminal degree is omitted from the exactness requirements. -/
def UpperSingletonGradedConcentrationBelow (m : ℕ) : Prop :=
  ∀ (θ : Set (Equiv.Perm (Fin n))) (w : Equiv.Perm (Fin n)),
    (∀ v ∈ θ, ∀ z, Support.inversionLength v < Support.inversionLength z → z ∈ θ) →
    (∀ v ∈ θ \ {w}, ∀ z,
      Support.inversionLength v < Support.inversionLength z → z ∈ θ \ {w}) →
    w ∈ θ →
    (0 < m → Function.Injective
      ((bundledSupportQuotientDiagram T A C (θ \ {w}) θ).degreeDifferential 0)) ∧
    (∀ k, k + 1 < m →
      LinearMap.range
          ((bundledSupportQuotientDiagram T A C (θ \ {w}) θ).degreeDifferential k) =
        LinearMap.ker
          ((bundledSupportQuotientDiagram T A C (θ \ {w}) θ).degreeDifferential (k + 1)))

/-- Upper singleton grade concentration and actual upper-degree vanishing
suffice for the existing actual Jacquet concentration condition. -/
theorem jacquetConcentratedAt_of_upperSingletonGraded
    (P : BlockShape n → Prop)
    (A : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier)) (m : ℕ)
    (hgraded : ∀ C, P C → UpperSingletonGradedConcentrationBelow T A C m)
    (hzero : ∀ k, m < k → ∀ C, P C →
      Subsingleton ((jacquetDiagram T C A.obj.ρ).Degree k)) :
    JacquetConcentratedAt F T P A m := by
  apply (jacquetConcentratedAt_iff_diagram T P A m).mpr
  refine ⟨fun hm C hC => ?_, fun k hk C hC => ?_, hzero⟩
  · apply degreeDifferential_injective_of_upperSingletonGraded T A C 0
    intro θ w hθ hLower hw
    exact (hgraded C hC θ w hθ hLower hw).1 hm
  · apply degreeDifferential_exact_of_upperSingletonGraded T A C k
    intro θ w hθ hLower hw
    exact (hgraded C hC θ w hθ hLower hw).2 k hk

end Langlands.Aubert.ActualCutComplex
