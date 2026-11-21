import Langlands.LocalField.LaurentSeries
import Langlands.VirtualRepresentation.Weil.Ramification
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Close-fields comparison of ramification quotients

The Galois and Weil forms of E1a compare a p-adic field with the Laurent-series
field over its residue field, up to the absolute ramification index.
-/

namespace Langlands.Ramification.Local

open Weil.Local (localDegree localProjection localResidueField localWeilGroup)
open VirtualRepresentation.LocalWeil.Ramification (upperGroup)

universe u uΩ

attribute [local instance] LocalField.Laurent.valuativeRel

local instance padicWeilUpperGroup_normal {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (v : ℝ) : (upperGroup F v).Normal :=
  Subgroup.Normal.comap (Padic.absoluteUpperRamificationGroup_normal F v)
    (localProjection F).toMonoidHom

local instance sepClosedWeilUpperGroup_normal
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (Ω : Type uΩ) [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] (v : ℝ) :
    (VirtualRepresentation.LocalWeil.SepClosed.Ramification.upperGroup K Ω v).Normal := by
  let : IsSepClosed Ω := IsSepClosure.sep_closed K
  exact Subgroup.Normal.comap (localAbsoluteUpperRamificationGroup_normal K Ω v)
    (Weil.Local.SepClosed.localProjection K Ω).toMonoidHom

/-- The absolute Galois quotients are topologically isomorphic with their upper filtrations. -/
def CloseFieldsGaloisQuotientStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p),
    let X := LaurentSeries (localResidueField F)
    let Ω := SeparableClosure X
    let e : ℝ := F.canonicalTopologicalData.ramificationIndex
    let upperK := Padic.absoluteUpperRamificationGroup F
    let upperX := localAbsoluteUpperRamificationGroup X Ω
    ∃ φ : (Field.absoluteGaloisGroup F.Carrier ⧸ upperK e) ≃ₜ*
        ((Ω ≃ₐ[X] Ω) ⧸ upperX e),
      ∀ v : ℝ, 0 ≤ v → v ≤ e →
        ((upperK v).map (QuotientGroup.mk' (upperK e))).map φ.toMulEquiv.toMonoidHom =
          (upperX v).map (QuotientGroup.mk' (upperX e))

/-- The Weil quotients are topologically isomorphic with their upper filtrations and degrees. -/
def CloseFieldsWeilQuotientStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p),
    let X := LaurentSeries (localResidueField F)
    let Ω := SeparableClosure X
    let e : ℝ := F.canonicalTopologicalData.ramificationIndex
    let W_K := localWeilGroup F
    let W_X := Weil.Local.SepClosed.localWeilGroup X Ω
    let upperK := upperGroup F
    let upperX := VirtualRepresentation.LocalWeil.SepClosed.Ramification.upperGroup X Ω
    ∃ ψ : (W_K ⧸ upperK e) ≃ₜ* (W_X ⧸ upperX e),
      (∀ v : ℝ, 0 ≤ v → v ≤ e →
        ((upperK v).map (QuotientGroup.mk' (upperK e))).map ψ.toMulEquiv.toMonoidHom =
          (upperX v).map (QuotientGroup.mk' (upperX e))) ∧
      ∀ (w : W_K) (w' : W_X),
        ψ (QuotientGroup.mk' (upperK e) w) = QuotientGroup.mk' (upperX e) w' →
          localDegree F w = Weil.Local.SepClosed.localDegree X Ω w'

end Langlands.Ramification.Local
