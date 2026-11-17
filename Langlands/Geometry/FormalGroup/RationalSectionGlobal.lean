import Langlands.Geometry.FormalGroup.RationalSectionCalculus
import Langlands.Geometry.FormalGroup.LocalQuasiIsogeny

/-! # Actual global tensors as sections on arbitrary opens -/

noncomputable section
universe u v
namespace Langlands.FormalGroup.ModuleLaw
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {F : Type v} [Field F] [Algebra O F]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {P : ModuleLaw O R υ}

namespace Hom

/-- Actual coherent coefficient restriction agrees on a map extended from the base. -/
theorem algebraMapLinear_mapStructural {A B : CommAlgCat.{v} R} (φ : A ⟶ B) (f : Hom M N) :
    algebraMapLinear φ (f.map (IsScalarTower.toAlgHom O R A)) =
      f.map (IsScalarTower.toAlgHom O R B) := by
  apply Hom.ext
  apply CommLaw.Hom.ext
  rw [algebraMapLinear_coordinates]
  change (f.toHom.toCoordinateMap.map (algebraMap R A)).map φ.hom.toRingHom =
    f.toHom.toCoordinateMap.map (algebraMap R B)
  rw [CoordinateMap.map_ringHom_comp]
  exact congrArg (fun ψ => f.toHom.toCoordinateMap.map ψ) (RingHom.ext φ.hom.commutes)

end Hom

namespace RationalHom

/-- The same structural compatibility for the actual rational tensor Hom. -/
theorem algebraMapLinear_mapStructural {A B : CommAlgCat.{v} R} (φ : A ⟶ B)
    (z : RationalHom F M N) :
    algebraMapLinear φ (map (IsScalarTower.toAlgHom O R A) z) =
      map (IsScalarTower.toAlgHom O R B) z := by
  induction z using TensorProduct.inductionOn with
  | tmul a f => simp only [map_tmul, algebraMapLinear_tmul, Hom.algebraMapLinear_mapStructural]
  | add z w hz hw => simp only [_root_.map_add, hz, hw]

end RationalHom

namespace RationalSection

/-- Extend a global tensor to the actual ring of sections and then sheafify. -/
def ofGlobalOn (U : Opens (PrimeSpectrum R)) :
    RationalHom F M N →ₗ[F] RationalSection F M N U :=
  (ofRational U).comp
    (RationalHom.map (IsScalarTower.toAlgHom O R ((coefficientStructurePresheaf R).obj (op U))))

@[simp]
theorem ofGlobalOn_top (z : RationalHom F M N) : ofGlobalOn ⊤ z = ofGlobal z := rfl

@[simp]
theorem restrict_ofGlobalOn {U V : Opens (PrimeSpectrum R)} (i : V ⟶ U)
    (z : RationalHom F M N) : restrict i (ofGlobalOn U z) = ofGlobalOn V z := by
  change restrict i (ofRational U (RationalHom.map _ z)) = _
  erw [restrict_ofRational]
  change ofRational V (RationalHom.algebraMapLinear ((coefficientStructurePresheaf R).map i.op)
    (RationalHom.map _ z)) = _
  rw [RationalHom.algebraMapLinear_mapStructural]
  rfl

@[simp]
theorem ofGlobalOn_comp (U : Opens (PrimeSpectrum R))
    (g : RationalHom F N P) (f : RationalHom F M N) :
    ofGlobalOn U (RationalHom.comp g f) = comp (ofGlobalOn U g) (ofGlobalOn U f) := by
  change ofRational U (RationalHom.map _ (RationalHom.comp g f)) =
    comp (ofRational U (RationalHom.map _ g)) (ofRational U (RationalHom.map _ f))
  erw [RationalHom.map_comp, comp_ofRational]

@[simp]
theorem ofGlobalOn_id (U : Opens (PrimeSpectrum R)) :
    ofGlobalOn U (RationalHom.id (F := F) M) = id M U := by
  change ofRational U (RationalHom.map _ (RationalHom.id M)) = _
  rw [RationalHom.map_id]
  rfl

/-- The actual image of a global integral formal homomorphism on any open. -/
def ofHom (f : Hom M N) (U : Opens (PrimeSpectrum R)) : RationalSection F M N U :=
  ofIntegral U (f.map (IsScalarTower.toAlgHom O R ((coefficientStructurePresheaf R).obj (op U))))

@[simp]
theorem ofGlobalOn_ofHom (U : Opens (PrimeSpectrum R)) (f : Hom M N) :
    ofGlobalOn U (RationalHom.ofHom (F := F) f) = ofHom f U := by
  change ofRational U (RationalHom.map _ (RationalHom.ofHom f)) = _
  rw [RationalHom.map_ofHom]
  rfl

@[simp]
theorem restrict_ofHom {U V : Opens (PrimeSpectrum R)} (i : V ⟶ U) (f : Hom M N) :
    restrict i (ofHom (F := F) f U) = ofHom f V := by
  rw [← ofGlobalOn_ofHom, restrict_ofGlobalOn, ofGlobalOn_ofHom]

@[simp]
theorem comp_ofIntegral {U : Opens (PrimeSpectrum R)}
    (g : OpenIntegralHom N P U) (f : OpenIntegralHom M N U) :
    comp (ofIntegral U g) (ofIntegral U f) = (ofIntegral U (g.comp f) : RationalSection F M P U) := by
  change comp (ofRational U (RationalHom.ofHom g))
    (ofRational U (RationalHom.ofHom f)) = _
  erw [comp_ofRational, ← RationalHom.ofHom_comp]
  rfl

@[simp]
theorem comp_ofHom (g : Hom N P) (f : Hom M N) (U : Opens (PrimeSpectrum R)) :
    comp (ofHom g U) (ofHom f U) = (ofHom (g.comp f) U : RationalSection F M P U) := by
  rw [← ofGlobalOn_ofHom, ← ofGlobalOn_ofHom, ← ofGlobalOn_comp, ← RationalHom.ofHom_comp,
    ofGlobalOn_ofHom]

@[simp]
theorem ofHom_id (U : Opens (PrimeSpectrum R)) :
    ofHom (F := F) (Hom.id M) U = id M U := by
  rw [← ofGlobalOn_ofHom, RationalHom.ofHom_id, ofGlobalOn_id]

/-- Integral global isogenies give local scalar-isogeny sections on every open. -/
theorem IsLocallyScalarIsogeny.ofHom {π : O} (f : Hom M N) (hf : f.IsIsogeny)
    (U : Opens (PrimeSpectrum R)) : IsLocallyScalarIsogeny π (ofHom (F := F) f U) :=
  IsLocallyScalarIsogeny.ofIntegral _ (hf.map _)

/-- Every identity section satisfies the local scalar-isogeny condition. -/
theorem IsLocallyScalarIsogeny.id (π : O) (M : ModuleLaw O R σ)
    (U : Opens (PrimeSpectrum R)) : IsLocallyScalarIsogeny π (id (F := F) M U) := by
  rw [← ofHom_id]
  exact IsLocallyScalarIsogeny.ofHom (Hom.id M) (Iso.refl M).isIsogeny U

end RationalSection
end Langlands.FormalGroup.ModuleLaw
