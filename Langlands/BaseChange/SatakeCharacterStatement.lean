import Langlands.BaseChange.UnramifiedHecke

/-!
# The Satake parametrization of spherical characters

Henniart–Lemaire (2011), §I.3.1 (printed pp. 24–25), citing Laumon (1996), 4.1; Gross
(1998), Proposition 3.6. Statement only; see the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange

open Correspondence Langlands.Unramified

universe u

local instance satakeStatementFieldTopology {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) :
    TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance satakeStatementFieldValuativeRel {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance satakeStatementFieldLocalField {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) :
    IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance satakeStatementGeneralLinearTopology {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (n : ℕ) : TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n
local instance satakeStatementGeneralLinearTopologicalGroup {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (n : ℕ) : IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopologicalGroup n
local instance satakeStatementGeneralLinearT2 {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    (n : ℕ) : T2Space (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearT2Space n
local instance satakeStatementGeneralLinearMeasurable {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (n : ℕ) : MeasurableSpace (GeneralLinear n F.Carrier) :=
  borel _
local instance satakeStatementGeneralLinearBorel {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (n : ℕ) : BorelSpace (GeneralLinear n F.Carrier) :=
  ⟨rfl⟩

/-- The Satake isomorphism for `GL_{r+1}` over a `p`-adic field, in terms of characters:
(a) every parameter `s` has a Satake character, and (b) the Satake characters separate the
elements of the spherical Hecke algebra (HL I.3.1, printed pp. 24–25). -/
def SatakeCharacterStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (r : ℕ),
    (∀ s : Eigenvalues (r + 1), ∃ ω : SphericalHeckeAlgebra F r →ₐ[ℂ] ℂ,
        IsSatakeCharacter F r s ω) ∧
      ∀ f : SphericalHeckeAlgebra F r,
        (∀ (s : Eigenvalues (r + 1)) (ω : SphericalHeckeAlgebra F r →ₐ[ℂ] ℂ),
            IsSatakeCharacter F r s ω → ω f = 0) → f = 0

end Langlands.BaseChange
