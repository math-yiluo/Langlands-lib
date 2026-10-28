import Langlands.AlgebraicGeometry.Picard.AmpleIsoStatement
import Langlands.AlgebraicGeometry.Modules.TensorSections
import Langlands.AlgebraicGeometry.Modules.TensorPowerIsomorphisms

/-! # Ampleness under an actual module-sheaf isomorphism -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.SchemeModule

variable {X : Scheme.{u}}

/-- A section and its image under an isomorphism trivialize on the same opens. -/
theorem trivializesOn_mapIso_iff {P Q : X.Modules} (e : P ≅ Q) (s : GlobalSections P)
    (U : X.Opens) : TrivializesOn Q (e.hom.app ⊤ s) U ↔ TrivializesOn P s U := by
  unfold TrivializesOn
  rw [sectionHom_naturality, Functor.map_comp]
  exact isIso_comp_right_iff _ _

/-- An isomorphism of module sheaves preserves the whole trivialization open of a section. -/
theorem trivializationOpen_mapIso {P Q : X.Modules} (e : P ≅ Q) (s : GlobalSections P) :
    trivializationOpen Q (e.hom.app ⊤ s) = trivializationOpen P s := by
  unfold trivializationOpen
  congr 1
  ext U
  exact trivializesOn_mapIso_iff e s U

end Langlands.SchemeModule

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.SchemeModule Langlands.Scheme.Modules

namespace LineBundle

variable {X : Scheme.{u}} {L M : LineBundle X}

/-- Ampleness is transported along an isomorphism of the underlying module sheaves. -/
theorem IsAmple.of_iso (hL : L.IsAmple) (e : L.obj ≅ M.obj) : M.IsAmple := by
  refine ⟨hL.1, fun x ↦ ?_⟩
  obtain ⟨n, hn, s, hx, ha⟩ := hL.2 x
  have h : M.sectionOpen ((tensorPowIso e n).hom.app ⊤ s) = L.sectionOpen s :=
    trivializationOpen_mapIso (tensorPowIso e n) s
  exact ⟨n, hn, (tensorPowIso e n).hom.app ⊤ s, h ▸ hx, h ▸ ha⟩

end LineBundle

/-- An actual module-sheaf isomorphism transports ampleness between line bundles. -/
theorem ampleIso : AmpleIsoStatement.{u} :=
  fun _ _ _ ⟨e⟩ hL ↦ hL.of_iso e

end Langlands.AlgebraicGeometry.Picard
