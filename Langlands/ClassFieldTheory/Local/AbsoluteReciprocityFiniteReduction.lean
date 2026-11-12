import Langlands.ClassFieldTheory.Local.AbsoluteReciprocityImagesProof
import Langlands.ClassFieldTheory.Local.AbsoluteReciprocityConductorProof
import Langlands.LocalFactor.Ramification.Herbrand.AbsoluteProof
import Langlands.LocalFactor.Ramification.Herbrand.InertiaProof
import Langlands.LocalFactor.Ramification.Herbrand.TransportProof

/-! # The finite real-image input for absolute upper reciprocity -/

noncomputable section

namespace Langlands.LocalClassField

universe u

/-- The finite real unit-image theorem suffices for all five absolute targets.
The absolute finite-image and inertia inputs are discharged by published proofs. -/
theorem absoluteUpperReciprocityTheorems_of_finiteRealImages
    (hfinite : FiniteReciprocityRealUnitImages.{u}) :
    AbsoluteUpperReciprocityTheorems.{u} := by
  obtain ⟨hinertia, hhigher, hreal⟩ := absoluteReciprocityImages_of_finite hfinite
    (fun _ _ F => Ramification.HerbrandBridge.absoluteUpperFiniteImage F)
    (fun _ _ F T => Ramification.HerbrandBridge.absoluteUpperInertia F T)
  obtain ⟨hlevels, hbreak⟩ :=
    absoluteReciprocityConductorConsequences_of_realImages hreal
  exact ⟨hinertia, hhigher, hreal, hlevels, hbreak⟩

/-- Absolute real images recover finite real images for every supplied
extension realization by restriction and realization independence. -/
theorem finiteReciprocityRealUnitImages_of_absolute
    (habsolute : AbsoluteUpperReciprocityTheorems.{u}) :
    FiniteReciprocityRealUnitImages.{u} := by
  intro p _ F T
  let := T.topology
  intro r hr L S
  let : Algebra F.Carrier (L.asPadicField (p := p)).Carrier :=
    inferInstanceAs (Algebra F.Carrier L.field)
  let : IsScalarTower (Padic p) F.Carrier (L.asPadicField (p := p)).Carrier :=
    inferInstanceAs (IsScalarTower (Padic p) F.Carrier L.field)
  intro v hv
  change (T.unitFiltration ⌈v⌉₊).map
    (L.abelianRestriction.toMonoidHom.comp r.toMonoidHom) = _
  rw [← Subgroup.map_map, habsolute.2.2.1 p F T r hr v hv,
    localAbelianUpperRamificationGroup_map_restriction F
      (Ramification.HerbrandBridge.absoluteUpperFiniteImage F) L v (by linarith)]
  exact Ramification.HerbrandBridge.upperRamificationGroup_eq_of_realization
    (L.asPadicField (p := p)).canonicalTopologicalData S F.Carrier v

/-- An equivalence of proof types identifies the exact remaining finite
arithmetic input for the full absolute upper reciprocity target. -/
def absoluteUpperReciprocityFiniteRealEquiv :
    AbsoluteUpperReciprocityTheorems.{u} ≃ FiniteReciprocityRealUnitImages.{u} where
  toFun := finiteReciprocityRealUnitImages_of_absolute
  invFun := absoluteUpperReciprocityTheorems_of_finiteRealImages
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

end Langlands.LocalClassField
