import Langlands.Geometry.FormalGroup.CoefficientSquareHom
import Langlands.Geometry.FormalGroup.RationalSectionGlobal
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.Topology.Sheaves.Functors

/-! # Coefficient pullback of arbitrary rational formal Hom sections -/

noncomputable section
universe u v
namespace Langlands.FormalGroup.ModuleLaw
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R S : Type v} [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
variable {F : Type v} [Field F] [Algebra O F]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}

/-- The actual continuous map of spectra induced by coefficient extension. -/
def coefficientSpectrumMap (φ : R →ₐ[O] S) : PrimeSpectrum.Top S ⟶ PrimeSpectrum.Top R :=
  Spec.topMap (CommRingCat.ofHom φ.toRingHom)

/-- Inverse image of actual open subsets under the coefficient spectrum map. -/
abbrev coefficientOpenMap (φ : R →ₐ[O] S) :=
  Opens.map (coefficientSpectrumMap φ)

/-- The actual structure-sheaf map, retaining its O-algebra structure. -/
def coefficientSectionMap (φ : R →ₐ[O] S) (U : Opens (PrimeSpectrum R)) :
    (coefficientStructurePresheaf R).obj (op U) →ₐ[O]
      (coefficientStructurePresheaf S).obj (op ((coefficientOpenMap φ).obj U)) where
  __ := ((Spec.sheafedSpaceMap (CommRingCat.ofHom φ.toRingHom)).hom.c.app (op U)).hom
  commutes' a := by
    have h := congrArg (fun k => k.hom (algebraMap O R a))
      (StructureSheaf.toOpen_comp_comap φ.toRingHom U)
    change StructureSheaf.comap φ.toRingHom U _ _ (algebraMap R _ (algebraMap O R a)) =
      algebraMap S _ (algebraMap O S a)
    change StructureSheaf.comap φ.toRingHom U _ _ (algebraMap R _ (algebraMap O R a)) =
      algebraMap S _ (φ (algebraMap O R a)) at h
    rw [φ.commutes] at h
    exact h

/-- The structure-sheaf pullback commutes with the actual structural coefficients. -/
theorem coefficientSectionMap_structural (φ : R →ₐ[O] S)
    (U : Opens (PrimeSpectrum R)) :
    (coefficientSectionMap φ U).comp (IsScalarTower.toAlgHom O R _) =
      (IsScalarTower.toAlgHom O S _).comp φ := by
  ext r
  exact congrArg (fun k => k.hom r) (StructureSheaf.toOpen_comp_comap φ.toRingHom U)

/-- The coefficient square commutes with actual restriction of sections. -/
theorem coefficientSectionMap_naturality (φ : R →ₐ[O] S)
    {U V : Opens (PrimeSpectrum R)} (i : V ⟶ U) :
    (coefficientSectionMap φ V).comp
        (coefficientAlgHom ((coefficientStructurePresheaf R).map i.op)) =
      (coefficientAlgHom ((coefficientStructurePresheaf S).map
        ((coefficientOpenMap φ).map i).op)).comp (coefficientSectionMap φ U) := by
  ext s
  exact congrArg (fun k => k.hom s)
    ((Spec.sheafedSpaceMap (CommRingCat.ofHom φ.toRingHom)).hom.c.naturality i.op)

namespace Hom

/-- Extend an actual formal map on an open through its genuine coefficient square. -/
def openBaseChange (φ : R →ₐ[O] S) (U : Opens (PrimeSpectrum R)) :
    OpenIntegralHom M N U →ₗ[O]
      OpenIntegralHom (M.map φ) (N.map φ) ((coefficientOpenMap φ).obj U) :=
  mapSquareLinear _ (coefficientSectionMap φ U) φ _ (coefficientSectionMap_structural φ U)

@[simp]
theorem openBaseChange_coordinates (φ : R →ₐ[O] S) (U : Opens (PrimeSpectrum R))
    (f : OpenIntegralHom M N U) :
    (openBaseChange φ U f).toHom.toCoordinateMap =
      f.toHom.toCoordinateMap.map (coefficientSectionMap φ U).toRingHom :=
  mapSquareLinear_coordinates _ _ _ _ _ _

/-- Actual integral coefficient pullback commutes with open restriction. -/
theorem openBaseChange_naturality (φ : R →ₐ[O] S)
    {U V : Opens (PrimeSpectrum R)} (i : V ⟶ U) (f : OpenIntegralHom M N U) :
    openBaseChange φ V
        (algebraMapLinear ((coefficientStructurePresheaf R).map i.op) f) =
      algebraMapLinear ((coefficientStructurePresheaf S).map
        ((coefficientOpenMap φ).map i).op) (openBaseChange φ U f) := by
  apply Hom.ext
  apply CommLaw.Hom.ext
  rw [openBaseChange_coordinates, algebraMapLinear_coordinates,
    algebraMapLinear_coordinates, openBaseChange_coordinates]
  rw [CoordinateMap.map_ringHom_comp, CoordinateMap.map_ringHom_comp]
  exact congrArg (fun k => f.toHom.toCoordinateMap.map k.toRingHom)
    (coefficientSectionMap_naturality φ i)

end Hom

namespace RationalHom

/-- Actual coefficient pullback of rational tensors on the rings of open sections. -/
def openBaseChange (φ : R →ₐ[O] S) (U : Opens (PrimeSpectrum R)) :
    (rationalHomPresheaf F M N).obj (op U) →ₗ[F]
      (rationalHomPresheaf F (M.map φ) (N.map φ)).obj
        (op ((coefficientOpenMap φ).obj U)) :=
  mapSquareLinear _ (coefficientSectionMap φ U) φ _ (coefficientSectionMap_structural φ U)

@[simp]
theorem openBaseChange_tmul (φ : R →ₐ[O] S) (U : Opens (PrimeSpectrum R))
    (a : F) (f : OpenIntegralHom M N U) :
    openBaseChange φ U (a ⊗ₜ[O] f) = a ⊗ₜ[O] Hom.openBaseChange φ U f :=
  mapSquareLinear_tmul _ _ _ _ _ _ _

/-- Rational tensor coefficient pullback commutes with actual restriction. -/
theorem openBaseChange_naturality (φ : R →ₐ[O] S)
    {U V : Opens (PrimeSpectrum R)} (i : V ⟶ U)
    (z : (rationalHomPresheaf F M N).obj (op U)) :
    openBaseChange φ V ((rationalHomPresheaf F M N).map i.op z) =
      (rationalHomPresheaf F (M.map φ) (N.map φ)).map
        ((coefficientOpenMap φ).map i).op (openBaseChange φ U z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a f =>
    change openBaseChange φ V (algebraMapLinear _ (a ⊗ₜ[O] f)) =
      algebraMapLinear _ (openBaseChange φ U (a ⊗ₜ[O] f))
    simp only [algebraMapLinear_tmul, openBaseChange_tmul]
    exact congrArg (fun k => a ⊗ₜ[O] k) (Hom.openBaseChange_naturality φ i f)
  | add z w hz hw =>
    change openBaseChange φ V (algebraMapLinear _ (z + w)) =
      algebraMapLinear _ (openBaseChange φ U (z + w))
    erw [LinearMap.map_add, LinearMap.map_add, LinearMap.map_add, LinearMap.map_add]
    exact congrArg₂ (fun a b => a + b) hz hw

end RationalHom

/-- Actual coefficient pullback is a morphism of rational Hom presheaves. -/
def rationalHomPresheafBaseChange (φ : R →ₐ[O] S) :
    rationalHomPresheaf F M N ⟶
      (coefficientOpenMap φ).op ⋙ rationalHomPresheaf F (M.map φ) (N.map φ) where
  app U := ModuleCat.ofHom (RationalHom.openBaseChange φ U.unop)
  naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact RationalHom.openBaseChange_naturality φ i.unop

/-- Pull tensors back and then apply the target sheafification unit. -/
def rationalHomPresheafBaseChangeUnit (φ : R →ₐ[O] S) :
    rationalHomPresheaf F M N ⟶
      ((TopCat.Sheaf.pushforward (ModuleCat.{v} F) (coefficientSpectrumMap φ)).obj
        (rationalHomSheaf F (M.map φ) (N.map φ))).obj :=
  rationalHomPresheafBaseChange φ ≫
    Functor.whiskerLeft (coefficientOpenMap φ).op
      (toSheafify (Opens.grothendieckTopology (PrimeSpectrum.Top S))
        (rationalHomPresheaf F (M.map φ) (N.map φ)))

/-- Extend actual coefficient pullback to arbitrary sheaf sections by the
universal property of genuine sheafification. -/
def rationalHomSheafBaseChange (φ : R →ₐ[O] S) :
    rationalHomSheaf F M N ⟶
      (TopCat.Sheaf.pushforward (ModuleCat.{v} F) (coefficientSpectrumMap φ)).obj
        (rationalHomSheaf F (M.map φ) (N.map φ)) :=
  ⟨sheafifyLift (Opens.grothendieckTopology (PrimeSpectrum.Top R))
    (rationalHomPresheafBaseChangeUnit φ)
    ((TopCat.Sheaf.pushforward (ModuleCat.{v} F) (coefficientSpectrumMap φ)).obj
      (rationalHomSheaf F (M.map φ) (N.map φ))).property⟩

namespace RationalSection

/-- Coefficient pullback of an arbitrary rational formal Hom sheaf section. -/
def baseChange (φ : R →ₐ[O] S) (U : Opens (PrimeSpectrum R)) :
    RationalSection F M N U →ₗ[F]
      RationalSection F (M.map φ) (N.map φ) ((coefficientOpenMap φ).obj U) :=
  ((rationalHomSheafBaseChange φ).hom.app (op U)).hom

@[simp]
theorem restrict_baseChange (φ : R →ₐ[O] S)
    {U V : Opens (PrimeSpectrum R)} (i : V ⟶ U) (z : RationalSection F M N U) :
    restrict ((coefficientOpenMap φ).map i) (baseChange φ U z) =
      baseChange φ V (restrict i z) := by
  exact (congrArg (fun k => k.hom z) ((rationalHomSheafBaseChange φ).hom.naturality i.op)).symm

@[simp]
theorem baseChange_ofRational (φ : R →ₐ[O] S) (U : Opens (PrimeSpectrum R))
    (z : (rationalHomPresheaf F M N).obj (op U)) :
    baseChange φ U (ofRational U z) =
      ofRational ((coefficientOpenMap φ).obj U) (RationalHom.openBaseChange φ U z) := by
  have h := toSheafify_sheafifyLift (Opens.grothendieckTopology (PrimeSpectrum.Top R))
    (rationalHomPresheafBaseChangeUnit (F := F) (M := M) (N := N) φ)
    ((TopCat.Sheaf.pushforward (ModuleCat.{v} F) (coefficientSpectrumMap φ)).obj
      (rationalHomSheaf F (M.map φ) (N.map φ))).property
  exact congrArg (fun η => (η.app (op U)).hom z) h

@[simp]
theorem baseChange_ofGlobalOn (φ : R →ₐ[O] S) (U : Opens (PrimeSpectrum R))
    (z : RationalHom F M N) :
    baseChange φ U (ofGlobalOn U z) =
      ofGlobalOn ((coefficientOpenMap φ).obj U) (RationalHom.map φ z) := by
  change baseChange φ U (ofRational U (RationalHom.map _ z)) = _
  erw [baseChange_ofRational]
  change ofRational _ (RationalHom.mapSquareLinear _ _ _ _ _ (RationalHom.map _ z)) = _
  rw [RationalHom.mapSquareLinear_map]
  rfl

@[simp]
theorem baseChange_ofHom (φ : R →ₐ[O] S) (U : Opens (PrimeSpectrum R)) (f : Hom M N) :
    baseChange φ U (ofHom (F := F) f U) =
      ofHom (f.map φ) ((coefficientOpenMap φ).obj U) := by
  rw [← ofGlobalOn_ofHom, baseChange_ofGlobalOn, RationalHom.map_ofHom, ofGlobalOn_ofHom]

end RationalSection
end Langlands.FormalGroup.ModuleLaw
