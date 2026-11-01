import Langlands.Representation.GodementJacquet.AnalyticData
import Langlands.Representation.Induction.BlockFactors
import Langlands.Representation.Classification.ConstituentCompatibility

/-! # Existence of normalized matrix data on a finite normalized product -/

noncomputable section

namespace Langlands.GodementJacquet

open MeasureTheory HarmonicAnalysis

universe uF uV

namespace Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance finiteProductTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance finiteProductValuation : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance finiteProductLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance finiteProductMeasurable : MeasurableSpace F.Carrier := borel _
local instance finiteProductBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance finiteProductGLMeasurable (r : ℕ) : MeasurableSpace (Langlands.GeneralLinear r F.Carrier) := borel _
local instance finiteProductGLBorel (r : ℕ) : BorelSpace (Langlands.GeneralLinear r F.Carrier) := ⟨rfl⟩

/-- Existence of the unchanged normalized data, indexed by the actual rank.
Rank zero is excluded; at rank `n+1` the four normalization parameters are
existentially quantified on the supplied actual representation. -/
def HasNormalizedMatrixFunctionalEquationData
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear r F.Carrier) V) : Prop :=
  match r, σ with
  | 0, _ => False
  | _n + 1, σ => ∃ (P PDual : Polynomial ℂ) (c : ℂˣ) (a : ℤ),
      NormalizedMatrixFunctionalEquationData F ψ ν σ P PDual c a

end Padic

/-- A finite actual normalized product has normalized matrix data whenever its
smooth admissible block factors have those data and scalar central
quasicharacters. This is a conditional closure assertion, not an analytic base. -/
def FiniteProductMatrixFunctionalEquationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI : MeasurableSpace F.Carrier := borel _
    haveI : BorelSpace F.Carrier := ⟨rfl⟩
    haveI : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
    haveI : TotallyDisconnectedSpace F.Carrier := by
      let : NonarchimedeanRing F.Carrier := by
        convert! ValuativeRel.nonarchimedeanRing F.Carrier
        exact Valuation.toTopologicalSpace_eq _
      infer_instance
    ∀ (r : ℕ), 0 < r →
    ∀ (B : GeneralLinear.BlockShape r)
      (A : ∀ i, SmoothRep.{0,uF,uV} ℂ
        (Langlands.GeneralLinear (B.size i) F.Carrier)),
      (∀ i, IsAdmissible (A i).representation) →
      ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier),
      IsSelfDual ψ ν →
      ∀ (ω : Fin B.length → Quasicharacter F.Carrier),
      (∀ i, Classification.HasGLCentralCharacter F.Carrier (B.size i)
        (A i).representation (ω i).toMonoidHom) →
      (∀ i, Padic.HasNormalizedMatrixFunctionalEquationData F ψ ν
        (A i).representation) →
      Padic.HasNormalizedMatrixFunctionalEquationData F ψ ν
        (F.canonicalNormalizedProductInduced B (fun i => (A i).representation))

end Langlands.GodementJacquet
