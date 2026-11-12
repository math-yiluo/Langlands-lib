import Langlands.HarmonicAnalysis.HomogeneousFunctions
import Langlands.Representation.Induction.Definitions
import Langlands.Sheaf.Renard.ProjectorSheafFunctor

/-! # Renard II.3.9: invariant functionals and homogeneous-space comparisons -/

noncomputable section

open MeasureTheory
open Langlands.Algebra
open Langlands.Sheaf.Renard

namespace Langlands.HarmonicAnalysis.HomogeneousFunctions.Renard

universe uG

/-- Existence, strict positivity and uniqueness in the full complex algebraic
dual of the actual relative-modular function space. -/
def InvariantFunctionalStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)),
    let V := renardSpace H hH
    let R := rightAction H (relativeModular H hH)
    let Positive : Module.Dual ℂ V → Prop := fun ν =>
      ∀ f : V, f ≠ 0 → (∀ x : G, (f.val x).im = 0 ∧ 0 ≤ (f.val x).re) →
        (ν f).im = 0 ∧ 0 < (ν f).re
    ∃ ν : Module.Dual ℂ V,
      Positive ν ∧ (∀ (g : G) (f : V), ν (R g f) = ν f) ∧
      (∀ S : Module.Dual ℂ V, (∀ (g : G) (f : V), S (R g f) = S f) →
        ∃! c : ℂ, S = c • ν) ∧
      ∀ S : Module.Dual ℂ V, Positive S →
        (∀ (g : G) (f : V), S (R g f) = S f) →
        ∃! c : ℝ, 0 < c ∧ S = (c : ℂ) • ν

/-- The proof's averaging map is specified by the actual subgroup integral,
with integrability, surjectivity, right equivariance and Haar factorization. -/
def AveragingStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] (μG : Measure G) [μG.IsHaarMeasure]
    (H : Subgroup G) (hH : IsClosed (H : Set G)),
    letI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
    letI : MeasurableSpace H := borel H
    letI : BorelSpace H := ⟨rfl⟩
    ∀ (μH : Measure H) [μH.IsHaarMeasure],
    ∃ p : SchwartzBruhat G →ₗ[ℂ] renardSpace H hH,
      (∀ (f : SchwartzBruhat G) (g : G),
        Integrable (fun h : H => f (h.val * g) *
          (((Distribution.renardModular h.val : ℝ)⁻¹) : ℂ)) μH) ∧
      (∀ (f : SchwartzBruhat G) (g : G),
        (p f).val g = ∫ h : H, f (h.val * g) *
          (((Distribution.renardModular h.val : ℝ)⁻¹) : ℂ) ∂μH) ∧
      Function.Surjective p ∧
      (∀ (g : G) (f : SchwartzBruhat G),
        p (GroupAction.rightTests g f) = rightAction H (relativeModular H hH) g (p f)) ∧
      ∃ ν : Module.Dual ℂ (renardSpace H hH),
        ν.comp p = Distribution.ofMeasure μG.inv ∧
        ∀ (g : G) (f : renardSpace H hH),
          ν (rightAction H (relativeModular H hH) g f) = ν f

/-- When the relative character is trivial, the comparison is exactly
pullback along the original projection to H\G. -/
def QuotientTestStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)),
    (∀ h : H, relativeModular H hH h = 1) →
    ∃ E : SchwartzBruhat (Langlands.Induction.LeftQuotient H) ≃ₗ[ℂ] renardSpace H hH,
      ∀ (f : SchwartzBruhat (Langlands.Induction.LeftQuotient H)) (g : G),
        (E f).val g = f (Langlands.Induction.quotientMap H g)

/-- An identity-on-values comparison with the existing compact-induction
carrier, with its genuine uniform stabilizer and compact quotient support. -/
def CompactInductionStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)),
    ∃ χ : Langlands.Induction.SmoothCharacter ℂ H,
      (∀ h : H, (χ.toMonoidHom h : ℂ) = ((relativeModular H hH h : ℝ) : ℂ)) ∧
      ∃ E : renardSpace H hH ≃ₗ[ℂ]
          Langlands.Induction.CompactFunctions H
            (Langlands.characterRepresentation χ.toMonoidHom),
        (∀ (f : renardSpace H hH) (g : G),
          Langlands.Induction.eval H (Langlands.characterRepresentation χ.toMonoidHom)
            (E f).val g = f.val g) ∧
        ∀ (g : G) (f : renardSpace H hH),
          E (rightAction H (relativeModular H hH) g f) =
            Langlands.Induction.compactInduced H
              (Langlands.characterRepresentation χ.toMonoidHom) g (E f)

/-- The actual pointwise test-algebra action is nondegenerate. Its published
projector sheaf has exactly the expected support and restriction formulas. -/
def PointwiseModuleSheafStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)),
    ∃ hQ : Langlands.Topology.IsLocallyProfinite (Langlands.Induction.LeftQuotient H),
    ∃ m : NonUnitalModule (PointwiseTestAlgebra.Carrier
        (Langlands.Induction.LeftQuotient H)) (renardSpace H hH),
    letI := m
    let V := renardSpace H hH
    let F := ProjectorBasisSheaf.basisSheaf hQ V
    IsNondegenerate (PointwiseTestAlgebra.Carrier
      (Langlands.Induction.LeftQuotient H)) V ∧
    (∀ (a : PointwiseTestAlgebra.Carrier (Langlands.Induction.LeftQuotient H))
      (f : V) (g : G), (a • f).val g = a (Langlands.Induction.quotientMap H g) * f.val g) ∧
    (∀ (U : ProjectorBasisSheaf.CompactOpen hQ) (f : V),
      ProjectorBasisSheaf.action hQ V U f = f ↔
        Function.support f.val ⊆ Langlands.Induction.quotientMap H ⁻¹' (U.obj : Set _)) ∧
    ∀ (U W : ProjectorBasisSheaf.CompactOpen hQ) (h : U.obj ≤ W.obj)
      (s : Sections F.obj.obj W) (g : G),
      (restriction F.obj.obj h s).val.val g =
        (U.obj : Set _).indicator (fun _ => (1 : ℂ))
          (Langlands.Induction.quotientMap H g) * s.val.val g

def Statements : Prop :=
  InvariantFunctionalStatement.{uG} ∧ AveragingStatement.{uG} ∧
    QuotientTestStatement.{uG} ∧ CompactInductionStatement.{uG} ∧
    PointwiseModuleSheafStatement.{uG}

end Langlands.HarmonicAnalysis.HomogeneousFunctions.Renard
