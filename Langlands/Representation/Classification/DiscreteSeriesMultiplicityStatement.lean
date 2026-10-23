import Langlands.Representation.Classification.CuspidalJacquetMultiplicityStatement
import Langlands.Representation.Classification.TemperedInductionStatement
import Langlands.Representation.Exponents.UnitaryPart

/-!
# Discrete-series Jacquet multiplicities on the unitary central part

The discrete-series alternative of Silberger 1979, Theorem 5.4.1.1,
concerns the tempered part, not the full Jacquet module. These are
proposition definitions, with actual subspaces and composition factors.
-/

namespace Langlands

universe uG uF uV uW

namespace DiscreteSeriesJacquetMultiplicity

section Generic

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [MeasurableSpace (G ⧸ Subgroup.center G)]

/-- Finite length with analytically tempered irreducible factors. The whole
representation need not have a single scalar central character. -/
def HasTemperedCompositionSeries (A : Rep.{uV} ℂ G)
    (μ : MeasureTheory.Measure (G ⧸ Subgroup.center G))
    [MeasureTheory.Measure.IsHaarMeasure μ] : Prop :=
  ∃ (k : ℕ) (s : ObjectRepFiltration A k),
    s.HasSimpleFactors ∧ ∀ i, IsTemperedModCenter (s.gradedRepresentation i).ρ μ

/-- The concrete unitary central part contains exactly the invariant subspaces
that admit a finite composition series with tempered irreducible factors. -/
def UnitaryPartIsMaximalTempered (A : Rep.{uV} ℂ G)
    (μ : MeasureTheory.Measure (G ⧸ Subgroup.center G))
    [MeasureTheory.Measure.IsHaarMeasure μ] : Prop :=
  ∀ S : Subrepresentation A.ρ,
    HasTemperedCompositionSeries (Rep.of S.toRepresentation) μ ↔
      S ≤ unitaryCentralPart A.ρ

end Generic

/-- Bundle the actual invariant unitary central part with its inherited action
and linear structure. No decomposition or analytic property is supplied. -/
noncomputable def unitaryPart {G : Type uG} [Group G] (A : Rep.{uV} ℂ G) :
    Rep.{uV} ℂ G :=
  Rep.of (unitaryCentralPart A.ρ).toRepresentation

end DiscreteSeriesJacquetMultiplicity

open CuspidalSupport DiscreteSeriesJacquetMultiplicity

/-- For associated standard GL Levis and irreducible discrete-series inducing
data, the unitary central parts of both normalized Jacquet modules are maximal
among submodules with tempered composition factors and have the Weyl-count
lengths and multiplicities. Nothing here bounds the full Jacquet length. -/
def GLDiscreteSeriesJacquetMultiplicityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B C : GeneralLinear.BlockShape n),
      letI := T.leviTopologicalGroup B
      letI := T.leviTopologicalGroup C
      let QB := B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier)
      let QC := C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)
      ∀ [MeasurableSpace QB] [BorelSpace QB]
        [MeasurableSpace QC] [BorelSpace QC]
        (μB : MeasureTheory.Measure QB) [MeasureTheory.Measure.IsHaarMeasure μB]
        (μC : MeasureTheory.Measure QC) [MeasureTheory.Measure.IsHaarMeasure μC]
        (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (ρ : Representation ℂ (B.Levi F.Carrier) V),
        Representation.IsIrreducible ρ → IsSquareIntegrableModCenter ρ μB →
        LevisAssociated (F := F.Carrier) B C →
          let I := CuspidalJacquetMultiplicity.induced T B (Rep.of ρ)
          let Ju := CuspidalJacquetMultiplicity.upperJacquet T C I
          let Jo := CuspidalJacquetMultiplicity.oppositeJacquet T C I
          let Uu := unitaryPart Ju
          let Uo := unitaryPart Jo
          let length := Nat.card (MinimalConjugatingPermutations (F := F.Carrier) B C)
          UnitaryPartIsMaximalTempered Ju μC ∧
          UnitaryPartIsMaximalTempered Jo μC ∧
          IsAdmissible Uu.ρ ∧ IsAdmissible Uo.ρ ∧
          HasCompositionSeriesLength Uu length ∧
          HasCompositionSeriesLength Uo length ∧
          ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W]
            (τ : Representation ℂ (C.Levi F.Carrier) W),
            Representation.IsIrreducible τ →
              ∀ m : ℕ,
                (HasJordanHolderMultiplicity Uu (Rep.of τ) m ↔
                  m = Nat.card (AssociatingPermutations B C ρ τ)) ∧
                (HasJordanHolderMultiplicity Uo (Rep.of τ) m ↔
                  m = Nat.card (AssociatingPermutations B C ρ τ))

end Langlands
