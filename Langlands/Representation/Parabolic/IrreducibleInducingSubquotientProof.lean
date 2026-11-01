import Langlands.Representation.Parabolic.IrreducibleInducingSubquotientStatement
import Langlands.Representation.Parabolic.NaturalFirstAdjointness
import Langlands.Representation.Filtration.NonzeroImageIrreducibleQuotient

/-! First adjointness and a simple quotient of its actual image. -/

noncomputable section

namespace Langlands.Parabolic

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

theorem irreducibleInducingSubquotient :
    IrreducibleInducingSubquotientStatement.{uF, uV} F T := by
  let := T.topology
  intro n B π σ hπ hfin ⟨f, hf⟩
  let := T.generalLinearTopologicalGroup n
  let e := FirstAdjointness.equiv T B π.isSmooth (σ := σ.representation)
  have hq0 : e f ≠ 0 := (LinearEquiv.map_ne_zero_iff _).mpr hf
  obtain ⟨ρ, hρ, ⟨q, hq⟩, hρσ⟩ :=
    SmoothRep.exists_irreducible_quotient_subquotient_of_nonzero hfin
      (SmoothRep.ofHom (e f)) hq0
  let := hρ
  let : Nontrivial ρ :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (B.Levi F.Carrier))
      ρ.representation.asModule
  have hq0' : SmoothRep.hom q ≠ 0 := by
    intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : ρ)
    obtain ⟨w, hw⟩ := hq v
    exact hv (hw.symm.trans (congrArg (fun g => g w) h))
  let e' := FirstAdjointness.equiv T B π.isSmooth (σ := ρ.representation)
  let j := e'.symm (SmoothRep.hom q)
  have hj0 : j ≠ 0 := (LinearEquiv.map_ne_zero_iff _).mpr hq0'
  let := hπ
  have hj : Function.Injective j :=
    (Representation.IsIrreducible.injective_or_eq_zero j).resolve_right hj0
  exact ⟨ρ, hρ, ⟨q, hq⟩, hρσ, ⟨SmoothRep.ofHom j, hj⟩⟩

end Langlands.Parabolic
