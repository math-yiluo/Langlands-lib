import Langlands.BaseChange.UnramifiedHecke

/-!
# Existence and uniqueness of the unramified base-change homomorphism

Henniart–Lemaire (2011), §I.1.3 (printed p. 6) and §I.3.1 (printed p. 25). Statement only;
see the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange

open Correspondence Langlands.Unramified

universe u v

local instance baseChangeHomStatementFieldTopology {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) :
    TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance baseChangeHomStatementFieldValuativeRel {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance baseChangeHomStatementFieldLocalField {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) :
    IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance baseChangeHomStatementGeneralLinearTopology {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (n : ℕ) : TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n
local instance baseChangeHomStatementGeneralLinearTopologicalGroup {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (n : ℕ) : IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopologicalGroup n
local instance baseChangeHomStatementGeneralLinearT2 {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    (n : ℕ) : T2Space (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearT2Space n
local instance baseChangeHomStatementGeneralLinearMeasurable {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (n : ℕ) : MeasurableSpace (GeneralLinear n F.Carrier) :=
  borel _
local instance baseChangeHomStatementGeneralLinearBorel {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (n : ℕ) : BorelSpace (GeneralLinear n F.Carrier) :=
  ⟨rfl⟩

/-- For all `p`-adic fields `F`, `E` over the same prime and all `l r : ℕ`, there is exactly
one algebra homomorphism `b : H_E → H_F` of spherical Hecke algebras of `GL_{r+1}` with
`S_F(b φ)(s) = S_E(φ)(s^l)` for every Satake parameter `s` (HL I.1.3, printed p. 6;
I.3.1, printed p. 25). -/
def UnramifiedBaseChangeHomStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p) (l r : ℕ),
    ∃! b : SphericalHeckeAlgebra E r →ₐ[ℂ] SphericalHeckeAlgebra F r,
      IsUnramifiedBaseChangeHom F E l r b

end Langlands.BaseChange
