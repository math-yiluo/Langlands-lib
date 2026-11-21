import Langlands.Geometry.FormalGroup.LocalQuasiIsogeny

/-! # Formal maps over the global sections of an affine spectrum -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory Opposite TopologicalSpace _root_.AlgebraicGeometry

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}

private abbrev GlobalCoefficients (R : Type v) [CommRing R] :=
  (coefficientStructurePresheaf R).obj (op (⊤ : Opens (PrimeSpectrum R)))

/-- The underlying affine ring equals the actual section algebra on the full spectrum. -/
def globalCoefficientEquiv (O : Type u) (R : Type v) [CommRing O] [CommRing R] [Algebra O R] :
    R ≃ₐ[O] GlobalCoefficients R :=
  AlgEquiv.ofBijective (IsScalarTower.toAlgHom O R (GlobalCoefficients R))
    (StructureSheaf.algebraMap_obj_top_bijective (R := R))

private def compareBack (M : ModuleLaw O R σ) :
    Iso ((M.map (globalCoefficientEquiv O R).toAlgHom).map (globalCoefficientEquiv O R).symm.toAlgHom) M :=
  Iso.ofIdenticalCoordinates
    (by
      change (M.groupLaw.addition.map (globalCoefficientEquiv O R).toRingHom).map
        (globalCoefficientEquiv O R).symm.toRingHom = _
      rw [CoordinateMap.map_ringHom_comp, show (globalCoefficientEquiv O R).symm.toRingHom.comp
          (globalCoefficientEquiv O R).toRingHom = RingHom.id R from
            RingHom.ext (globalCoefficientEquiv O R).symm_apply_apply, CoordinateMap.map_ringHom_id])
    (fun a => by
      change ((M.action a).toCoordinateMap.map (globalCoefficientEquiv O R).toRingHom).map
        (globalCoefficientEquiv O R).symm.toRingHom = _
      rw [CoordinateMap.map_ringHom_comp, show (globalCoefficientEquiv O R).symm.toRingHom.comp
          (globalCoefficientEquiv O R).toRingHom = RingHom.id R from
            RingHom.ext (globalCoefficientEquiv O R).symm_apply_apply, CoordinateMap.map_ringHom_id])

/-- A map over the full structure-section ring gives a map over the original affine base. -/
def Hom.ofGlobalCoefficients (f : OpenIntegralHom M N ⊤) : Hom M N :=
  (compareBack N).hom.comp ((f.map (globalCoefficientEquiv O R).symm.toAlgHom).comp (compareBack M).inv)

/-- Extending the recovered global map to structure sections restores the original coefficients. -/
theorem Hom.map_ofGlobalCoefficients (f : OpenIntegralHom M N ⊤) :
    f.ofGlobalCoefficients.map (globalCoefficientEquiv O R).toAlgHom = f := by
  apply Hom.ext
  apply CommLaw.Hom.ext
  change (CoordinateMap.id.comp
      ((f.toHom.toCoordinateMap.map (globalCoefficientEquiv O R).symm.toRingHom).comp
        CoordinateMap.id)).map (globalCoefficientEquiv O R).toRingHom = _
  rw [CoordinateMap.id_comp, CoordinateMap.comp_id, CoordinateMap.map_ringHom_comp,
    show (globalCoefficientEquiv O R).toRingHom.comp (globalCoefficientEquiv O R).symm.toRingHom =
      RingHom.id (GlobalCoefficients R) from RingHom.ext (globalCoefficientEquiv O R).apply_symm_apply,
    CoordinateMap.map_ringHom_id]

/-- Extending an integral map to full structure sections is faithful. -/
theorem Hom.map_globalCoefficients_injective :
    Function.Injective (fun f : Hom M N => f.map (globalCoefficientEquiv O R).toAlgHom) := by
  intro f g h
  apply Hom.ext
  apply CommLaw.Hom.ext
  apply CoordinateMap.ext
  funext j
  ext μ
  apply (globalCoefficientEquiv O R).injective
  have hc := congrArg (fun f : OpenIntegralHom M N ⊤ =>
    MvPowerSeries.coeff μ (f.toHom.toCoordinateMap.series j)) h
  change MvPowerSeries.coeff μ ((f.toHom.toCoordinateMap.series j).map
    (globalCoefficientEquiv O R).toRingHom) =
    MvPowerSeries.coeff μ ((g.toHom.toCoordinateMap.series j).map
      (globalCoefficientEquiv O R).toRingHom) at hc
  rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map] at hc
  exact hc

end Langlands.FormalGroup.ModuleLaw
