import Langlands.Geometry.FormalGroup.DrinfeldFramedClassBaseChange
import Langlands.Geometry.FormalGroup.AtlasOrderRationalBaseChangeSelf

/-! # Forced frame maps for identity and composition of framed base extension -/

noncomputable section

universe u v w s

namespace Langlands.FormalGroup.Nilp

open CategoryTheory

variable (O : Type u) [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R] {r : R}
variable {A B C : Nilp.{v, w} R r}

attribute [local instance] ModuleLaw.coefficientAlgebra ModuleLaw.coefficientScalarTower

/-- The actual induced quotient scalar map preserves the Nilp identity. -/
@[simp]
theorem reducedScalarMap_id (A : Nilp.{v, w} R r) :
    reducedScalarMap O (𝟙 A) = AlgHom.id O ((reductionFunctor R r).obj A).obj := by
  rw [reducedScalarMap, CategoryTheory.Functor.map_id]
  rfl

/-- The actual induced quotient scalar maps compose in the same order as the Nilp maps. -/
@[simp]
theorem reducedScalarMap_comp (f : A ⟶ B) (g : B ⟶ C) :
    reducedScalarMap O (f ≫ g) = (reducedScalarMap O g).comp (reducedScalarMap O f) := by
  rw [reducedScalarMap, CategoryTheory.Functor.map_comp]
  rfl

end Langlands.FormalGroup.Nilp

namespace Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] {π : 𝒪[K]}
variable {A B C : Nilp.{v, u} R (algebraMap 𝒪[K] R π)}
variable {Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι) (R := κ) π}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Identity Nilp extension preserves the actual stored residue map. -/
@[simp]
theorem baseChange_id_residueMap (X : DrinfeldFramedAtlas Φ A) :
    (X.baseChange (𝟙 A)).residueMap = X.residueMap := by
  change (Nilp.reducedScalarMap 𝒪[K] (𝟙 A)).comp X.residueMap = _
  rw [Nilp.reducedScalarMap_id, AlgHom.id_comp]

/-- Two Nilp extensions have the same actual residue map as their composite. -/
theorem baseChange_comp_residueMap (X : DrinfeldFramedAtlas Φ A) (f : A ⟶ B) (g : B ⟶ C) :
    ((X.baseChange f).baseChange g).residueMap = (X.baseChange (f ≫ g)).residueMap := by
  change (Nilp.reducedScalarMap 𝒪[K] g).comp
      ((Nilp.reducedScalarMap 𝒪[K] f).comp X.residueMap) =
    (Nilp.reducedScalarMap 𝒪[K] (f ≫ g)).comp X.residueMap
  rw [Nilp.reducedScalarMap_comp, AlgHom.comp_assoc]

/-- The actual identity-coordinate global-frame map forced by identity residue coherence. -/
def baseChangeIdentityFrameIso (X : DrinfeldFramedAtlas Φ A) :=
  globalFrameIso (X.baseChange_id_residueMap)

/-- The actual identity-coordinate global-frame map forced by composite residue coherence. -/
def baseChangeCompositionFrameIso (X : DrinfeldFramedAtlas Φ A) (f : A ⟶ B) (g : B ⟶ C) :=
  globalFrameIso (X.baseChange_comp_residueMap f g)

/-- The identity-extension fixed-frame comparison has complete identity formal series. -/
theorem baseChangeIdentityFrameIso_hom_coordinates (X : DrinfeldFramedAtlas Φ A) :
    (X.baseChangeIdentityFrameIso).hom.val.toHom.toCoordinateMap = CoordinateMap.id :=
  globalFrameIso_hom_coordinates X.baseChange_id_residueMap

/-- The inverse identity-extension frame comparison has complete identity series. -/
theorem baseChangeIdentityFrameIso_inv_coordinates (X : DrinfeldFramedAtlas Φ A) :
    (X.baseChangeIdentityFrameIso).inv.val.toHom.toCoordinateMap = CoordinateMap.id :=
  ModuleLaw.OrderAction.Iso.inv_coordinates_of_hom_id _ X.baseChangeIdentityFrameIso_hom_coordinates

/-- The composite-extension fixed-frame comparison has complete identity formal series. -/
theorem baseChangeCompositionFrameIso_hom_coordinates
    (X : DrinfeldFramedAtlas Φ A) (f : A ⟶ B) (g : B ⟶ C) :
    (X.baseChangeCompositionFrameIso f g).hom.val.toHom.toCoordinateMap = CoordinateMap.id :=
  globalFrameIso_hom_coordinates (X.baseChange_comp_residueMap f g)

/-- The inverse composite-extension frame comparison has complete identity series. -/
theorem baseChangeCompositionFrameIso_inv_coordinates
    (X : DrinfeldFramedAtlas Φ A) (f : A ⟶ B) (g : B ⟶ C) :
    (X.baseChangeCompositionFrameIso f g).inv.val.toHom.toCoordinateMap = CoordinateMap.id :=
  ModuleLaw.OrderAction.Iso.inv_coordinates_of_hom_id _ (X.baseChangeCompositionFrameIso_hom_coordinates f g)

end Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas
