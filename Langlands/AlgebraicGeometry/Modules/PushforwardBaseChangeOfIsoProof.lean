import Langlands.AlgebraicGeometry.Modules.PushforwardBaseChangeOfIsoStatement

/-!
# Proof: invertibility of the base-change comparison of a map over spectra
-/

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- Over spectra, quasi-coherent direct images and an invertible scalar sections comparison
make the sheaf comparison `pushforwardBaseChangeOf` invertible. -/
theorem pushforwardBaseChangeOfIso : PushforwardBaseChangeOfIsoStatement.{u} := by
  intro X X' R T φ f f' g w P N a hP hN ha
  let P' := (Scheme.Modules.pushforward f).obj P
  let Q := (Scheme.Modules.pushforward f').obj N
  let : IsIso P'.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent P'
  let : IsIso Q.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent Q
  let : IsIso (tilde.map (scalarSectionsBaseChangeMapOf φ f f' g w a)) :=
    inferInstanceAs
      (IsIso ((tilde.functor T).map (scalarSectionsBaseChangeMapOf φ f f' g w a)))
  have h : IsIso ((Scheme.Modules.pullback (Spec.map φ)).map P'.fromTildeΓ ≫
      pushforwardBaseChangeOf f (Spec.map φ) f' g w a) := by
    rw [pullback_fromTildeΓ_comp_pushforwardBaseChangeOf]
    unfold affineDirectImageTildeMapOf
    infer_instance
  exact IsIso.of_isIso_comp_left ((Scheme.Modules.pullback (Spec.map φ)).map P'.fromTildeΓ) _

end Langlands.AlgebraicGeometry.Modules.DerivedSections
