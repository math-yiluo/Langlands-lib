import Langlands.BaseChange.UnramifiedHecke
import Langlands.BaseChange.OrbitalIntegral

/-!
# The fundamental lemma for unramified base change

Henniart–Lemaire (2011), Chapter I, §I.6.6, Théorème (printed p. 47); Arthur–Clozel (1989),
Chapter 1, Theorem 4.5. Statement only; see the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory Correspondence Langlands.Unramified

universe u v

local instance fundamentalLemmaFieldTopology {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) :
    TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance fundamentalLemmaFieldValuativeRel {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance fundamentalLemmaFieldLocalField {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) :
    IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance fundamentalLemmaGeneralLinearTopology {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (n : ℕ) : TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n
local instance fundamentalLemmaGeneralLinearTopologicalGroup {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (n : ℕ) : IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopologicalGroup n
local instance fundamentalLemmaGeneralLinearT2 {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    (n : ℕ) : T2Space (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearT2Space n
local instance fundamentalLemmaGeneralLinearMeasurable {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (n : ℕ) : MeasurableSpace (GeneralLinear n F.Carrier) :=
  borel _
local instance fundamentalLemmaGeneralLinearBorel {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (n : ℕ) : BorelSpace (GeneralLinear n F.Carrier) :=
  ⟨rfl⟩

/-- The fundamental lemma for unramified base change (HL I.6.6, Théorème, printed p. 47). -/
def FundamentalLemmaStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    (σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier) (l r : ℕ),
    IsCyclicAlgebra σ l →
    E.canonicalTopologicalData.ramificationIndex =
      F.canonicalTopologicalData.ramificationIndex →
    ∀ b : SphericalHeckeAlgebra E r →ₐ[ℂ] SphericalHeckeAlgebra F r,
      IsUnramifiedBaseChangeHom F E l r b →
      ∀ φ : SphericalHeckeAlgebra E r,
        AreConcordant σ l (sphericalHaar F r) (sphericalHaar E r) ⇑φ ⇑(b φ)

end Langlands.BaseChange
