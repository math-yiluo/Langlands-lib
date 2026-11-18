import Langlands.BaseChange.UnramifiedHecke
import Langlands.BaseChange.OrbitalIntegral

/-!
# The fundamental lemma for the unit element

Henniart–Lemaire (2011), Chapter I, §I.3.1, Proposition (printed p. 25), after Kottwitz
(1980), Lemma 8.8. Statement only; see the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory Correspondence Langlands.Unramified

universe u v

local instance unitFundamentalLemmaFieldTopology {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) :
    TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance unitFundamentalLemmaFieldValuativeRel {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance unitFundamentalLemmaFieldLocalField {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) :
    IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance unitFundamentalLemmaGeneralLinearTopology {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (n : ℕ) : TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n
local instance unitFundamentalLemmaGeneralLinearTopologicalGroup {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (n : ℕ) : IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopologicalGroup n
local instance unitFundamentalLemmaGeneralLinearT2 {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    (n : ℕ) : T2Space (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearT2Space n
local instance unitFundamentalLemmaGeneralLinearMeasurable {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (n : ℕ) : MeasurableSpace (GeneralLinear n F.Carrier) :=
  borel _
local instance unitFundamentalLemmaGeneralLinearBorel {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (n : ℕ) : BorelSpace (GeneralLinear n F.Carrier) :=
  ⟨rfl⟩

/-- The fundamental lemma for the unit elements (HL I.3.1, Proposition, printed p. 25). -/
def UnitFundamentalLemmaStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    (σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier) (l r : ℕ),
    IsCyclicAlgebra σ l →
    E.canonicalTopologicalData.ramificationIndex =
      F.canonicalTopologicalData.ramificationIndex →
    AreConcordant σ l (sphericalHaar F r) (sphericalHaar E r)
      ⇑(1 : SphericalHeckeAlgebra E r) ⇑(1 : SphericalHeckeAlgebra F r)

end Langlands.BaseChange
