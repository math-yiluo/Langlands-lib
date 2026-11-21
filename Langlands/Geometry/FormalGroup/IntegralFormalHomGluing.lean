import Langlands.Geometry.FormalGroup.LocalQuasiIsogeny
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Gluing integral formal Hom by its structure coefficients -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory Opposite TopologicalSpace _root_.AlgebraicGeometry

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {ι : Type*} {U : Opens (PrimeSpectrum R)}

namespace IntegralFormalHomGluing

private abbrev Sections (U : Opens (PrimeSpectrum R)) :=
  (coefficientStructurePresheaf R).obj (op U)

private abbrev restrictCoeff {U V : Opens (PrimeSpectrum R)} (i : V ⟶ U) :
    Sections U →+* Sections V :=
  ((coefficientStructurePresheaf R).map i.op).hom.toRingHom

variable (V : ι → Opens (PrimeSpectrum R)) (i : ∀ b, V b ⟶ U) (hcover : U ≤ iSup V)

omit [Finite σ] in
private theorem seriesCoefficients_compatible (s : ∀ b, MvPowerSeries σ (Sections (V b)))
    (h : ∀ b c, (s b).map (restrictCoeff (homOfLE inf_le_left : V b ⊓ V c ⟶ V b)) =
      (s c).map (restrictCoeff (homOfLE inf_le_right : V b ⊓ V c ⟶ V c)))
    (μ : σ →₀ ℕ) :
    TopCat.Presheaf.IsCompatible (Spec.structureSheaf R).obj V (fun b => MvPowerSeries.coeff μ (s b)) := by
  intro b c
  change restrictCoeff (homOfLE inf_le_left : V b ⊓ V c ⟶ V b) (MvPowerSeries.coeff μ (s b)) =
    restrictCoeff (homOfLE inf_le_right : V b ⊓ V c ⟶ V c) (MvPowerSeries.coeff μ (s c))
  simpa only [MvPowerSeries.coeff_map] using congrArg (MvPowerSeries.coeff μ) (h b c)

private def glueSeries (s : ∀ b, MvPowerSeries σ (Sections (V b)))
    (h : ∀ b c, (s b).map (restrictCoeff (homOfLE inf_le_left : V b ⊓ V c ⟶ V b)) =
      (s c).map (restrictCoeff (homOfLE inf_le_right : V b ⊓ V c ⟶ V c))) :
    MvPowerSeries σ (Sections U) := fun μ =>
  ((Spec.structureSheaf R).existsUnique_gluing' V U i hcover
    (fun b => MvPowerSeries.coeff μ (s b)) (seriesCoefficients_compatible V s h μ)).exists.choose

omit [Finite σ] in
private theorem restrict_glueSeries (s : ∀ b, MvPowerSeries σ (Sections (V b)))
    (h : ∀ b c, (s b).map (restrictCoeff (homOfLE inf_le_left : V b ⊓ V c ⟶ V b)) =
      (s c).map (restrictCoeff (homOfLE inf_le_right : V b ⊓ V c ⟶ V c))) (b : ι) :
    (glueSeries V i hcover s h).map (restrictCoeff (i b)) = s b := by
  ext μ
  rw [MvPowerSeries.coeff_map]
  exact ((Spec.structureSheaf R).existsUnique_gluing' V U i hcover
    (fun c => MvPowerSeries.coeff μ (s c)) (seriesCoefficients_compatible V s h μ)).exists.choose_spec b

omit [Finite σ] [Finite τ] in
private theorem coordinateSeries_compatible (f : ∀ b, CoordinateMap (Sections (V b)) σ τ)
    (h : ∀ b c, (f b).map (restrictCoeff (homOfLE inf_le_left : V b ⊓ V c ⟶ V b)) =
      (f c).map (restrictCoeff (homOfLE inf_le_right : V b ⊓ V c ⟶ V c))) (j : τ) (b c : ι) :
    ((f b).series j).map (restrictCoeff (homOfLE inf_le_left : V b ⊓ V c ⟶ V b)) =
      ((f c).series j).map (restrictCoeff (homOfLE inf_le_right : V b ⊓ V c ⟶ V c)) :=
  congrArg (fun g : CoordinateMap (Sections (V b ⊓ V c)) σ τ => g.series j) (h b c)

private def glueCoordinates (f : ∀ b, CoordinateMap (Sections (V b)) σ τ)
    (h : ∀ b c, (f b).map (restrictCoeff (homOfLE inf_le_left : V b ⊓ V c ⟶ V b)) =
      (f c).map (restrictCoeff (homOfLE inf_le_right : V b ⊓ V c ⟶ V c))) :
    CoordinateMap (Sections U) σ τ where
  series j := glueSeries V i hcover (fun b => (f b).series j) (coordinateSeries_compatible V f h j)
  constantCoeff_eq_zero j := by
    apply (Spec.structureSheaf R).eq_of_locally_eq' V U i hcover
    intro b
    have hg := restrict_glueSeries V i hcover (fun b => (f b).series j) (coordinateSeries_compatible V f h j) b
    change restrictCoeff (i b) (MvPowerSeries.constantCoeff _) = restrictCoeff (i b) 0
    simpa only [MvPowerSeries.constantCoeff_map, (f b).constantCoeff_eq_zero, map_zero] using
      congrArg MvPowerSeries.constantCoeff hg

omit [Finite σ] [Finite τ] in
private theorem restrict_glueCoordinates (f : ∀ b, CoordinateMap (Sections (V b)) σ τ)
    (h : ∀ b c, (f b).map (restrictCoeff (homOfLE inf_le_left : V b ⊓ V c ⟶ V b)) =
      (f c).map (restrictCoeff (homOfLE inf_le_right : V b ⊓ V c ⟶ V c))) (b : ι) :
    (glueCoordinates V i hcover f h).map (restrictCoeff (i b)) = f b := by
  apply CoordinateMap.ext
  funext j
  exact restrict_glueSeries V i hcover _ (coordinateSeries_compatible V f h j) b

include hcover in
private theorem coordinate_eq_of_restrictions {α β : Type} {f g : CoordinateMap (Sections U) α β}
    (h : ∀ b, f.map (restrictCoeff (i b)) = g.map (restrictCoeff (i b))) : f = g := by
  apply CoordinateMap.ext
  funext j
  ext μ
  apply (Spec.structureSheaf R).eq_of_locally_eq' V U i hcover
  intro b
  change restrictCoeff (i b) (MvPowerSeries.coeff μ (f.series j)) =
    restrictCoeff (i b) (MvPowerSeries.coeff μ (g.series j))
  have hc := congrArg (fun x : CoordinateMap (Sections (V b)) α β =>
    MvPowerSeries.coeff μ (x.series j)) (h b)
  simpa only [CoordinateMap.map_series, MvPowerSeries.coeff_map] using hc

private theorem restrictCoeff_structural (b : ι) :
    (restrictCoeff (i b)).comp (algebraMap R (Sections U)) = algebraMap R (Sections (V b)) :=
  RingHom.ext ((coefficientStructurePresheaf R).map (i b).op).hom.commutes

variable (f : ∀ b, OpenIntegralHom M N (V b))
variable (h : ∀ b c,
  Hom.algebraMapLinear ((coefficientStructurePresheaf R).map
    (homOfLE inf_le_left : V b ⊓ V c ⟶ V b).op) (f b) =
  Hom.algebraMapLinear ((coefficientStructurePresheaf R).map
    (homOfLE inf_le_right : V b ⊓ V c ⟶ V c).op) (f c))

include h in
private theorem coordinates_compatible (b c : ι) :
    ((f b).toHom.toCoordinateMap).map (restrictCoeff (homOfLE inf_le_left : V b ⊓ V c ⟶ V b)) =
      ((f c).toHom.toCoordinateMap).map (restrictCoeff (homOfLE inf_le_right : V b ⊓ V c ⟶ V c)) := by
  have hc := congrArg (fun g : OpenIntegralHom M N (V b ⊓ V c) => g.toHom.toCoordinateMap) (h b c)
  simpa only [Hom.algebraMapLinear_coordinates] using hc

include h hcover in
/-- Glue the pointed coordinates of a compatible family, and check the addition and
scalar equations on the original open cover. -/
def glue : OpenIntegralHom M N U := by
  let q := glueCoordinates V i hcover (fun b => (f b).toHom.toCoordinateMap)
    (coordinates_compatible V f h)
  have hq (b : ι) : q.map (restrictCoeff (i b)) = (f b).toHom.toCoordinateMap :=
    restrict_glueCoordinates V i hcover _ _ b
  refine ⟨⟨q, ?_⟩, ?_⟩
  · apply coordinate_eq_of_restrictions V i hcover
    intro b
    simp only [CoordinateMap.map_comp, CoordinateMap.map_pair, CoordinateMap.map_fst,
      CoordinateMap.map_snd, hq]
    change (f b).toHom.toCoordinateMap.comp ((M.groupLaw.addition.map (algebraMap R (Sections U))).map
      (restrictCoeff (i b))) =
      ((N.groupLaw.addition.map (algebraMap R (Sections U))).map (restrictCoeff (i b))).comp _
    rw [CoordinateMap.map_ringHom_comp, CoordinateMap.map_ringHom_comp, restrictCoeff_structural V i b]
    exact (f b).toHom.map_add
  · intro a
    apply CommLaw.Hom.ext
    apply coordinate_eq_of_restrictions V i hcover
    intro b
    simp only [CommLaw.Hom.comp_toCoordinateMap, CoordinateMap.map_comp, hq]
    change (f b).toHom.toCoordinateMap.comp (((M.action a).toCoordinateMap.map
      (algebraMap R (Sections U))).map (restrictCoeff (i b))) =
      (((N.action a).toCoordinateMap.map (algebraMap R (Sections U))).map
        (restrictCoeff (i b))).comp (f b).toHom.toCoordinateMap
    rw [CoordinateMap.map_ringHom_comp, CoordinateMap.map_ringHom_comp, restrictCoeff_structural V i b]
    exact congrArg CommLaw.Hom.toCoordinateMap ((f b).commutes a)

/-- Restricting the glued integral map recovers the given map on its presenting open. -/
theorem restrict_glue (b : ι) :
    Hom.algebraMapLinear ((coefficientStructurePresheaf R).map (i b).op)
      (glue V i hcover f h) = f b := by
  apply Hom.ext
  apply CommLaw.Hom.ext
  rw [Hom.algebraMapLinear_coordinates]
  exact restrict_glueCoordinates V i hcover _ (coordinates_compatible V f h) b

end IntegralFormalHomGluing

end Langlands.FormalGroup.ModuleLaw
