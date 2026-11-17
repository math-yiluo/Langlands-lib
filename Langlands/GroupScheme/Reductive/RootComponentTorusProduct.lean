import Langlands.GroupScheme.Reductive.RootComponentCentralizerFactors
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleProductFactors

/-! # Actual torus products from integral Cartan-component coordinates -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace splitTorus

/-- An integral character equivalence between possibly different coordinate
index sets gives an actual torus isomorphism over every scheme. -/
def exponentIsoOfEquiv (S : Scheme.{u}) (I K : Type u) [Fintype I] [Fintype K]
    (e : (I → ℤ) ≃ₗ[ℤ] (K → ℤ)) : splitTorus S K ≅ splitTorus S I := by
  classical
  refine
    { hom := CommGroupScheme.groupHom (exponentHom S K I e.toLinearMap)
      inv := CommGroupScheme.groupHom (exponentHom S I K e.symm.toLinearMap)
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · change CommGroupScheme.groupHom
      (exponentHom S K I e.toLinearMap ≫ exponentHom S I K e.symm.toLinearMap) =
      CommGroupScheme.groupHom (𝟙 (commGroupScheme S K))
    apply congrArg CommGroupScheme.groupHom
    rw [exponentHom_comp]
    have he : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by
      ext x
      simp
    rw [he, exponentHom_id]
  · change CommGroupScheme.groupHom
      (exponentHom S I K e.symm.toLinearMap ≫ exponentHom S K I e.toLinearMap) =
      CommGroupScheme.groupHom (𝟙 (commGroupScheme S I))
    apply congrArg CommGroupScheme.groupHom
    rw [exponentHom_comp]
    have he : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
      ext x
      simp
    rw [he, exponentHom_id]

end splitTorus

namespace RootComponentCoordinates

open Langlands.LinearAlgebra.SimplyConnectedCartanComponents

variable {M : AffinePinnedModel.{u}} (D : RootComponentCoordinates M)

/-- Simple indices in the specified Cartan component. -/
abbrev OwnIndices (_D : RootComponentCoordinates M) (c : Component M.basis) :=
  {i : M.basis.support // component M.basis i = c}

/-- The split torus for one block of the full integral character coordinates. -/
abbrev factorTorus (S : Scheme.{u}) (c : Component M.basis) : GroupScheme S :=
  splitTorus S (D.OwnIndices c)

/-- Regrouping the individual multiplicative groups by their Cartan components
is an actual isomorphism of finite product group schemes. -/
def coordinateProductIso (S : Scheme.{u}) :
    pi (D.factorTorus S) ≅ splitTorus S M.basis.support := by
  classical
  let F := D.factorTorus S
  let U := fun _ : M.basis.support => (Gm S).toGrp
  refine
    { hom := Pi.lift (f := U) (fun i => Pi.π F (component M.basis i) ≫
        Pi.π (fun _ : D.OwnIndices (component M.basis i) => (Gm S).toGrp) ⟨i, rfl⟩)
      inv := Pi.lift (f := F) (fun c =>
        Pi.lift (f := fun _ : D.OwnIndices c => (Gm S).toGrp) (fun i => Pi.π U i.val))
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply Pi.hom_ext
    intro c
    apply Pi.hom_ext
    rintro ⟨i, hi⟩
    subst c
    dsimp only [F, U, factorTorus]
    simp only [Category.assoc, Pi.lift_comp_π, Category.id_comp]
  · apply Pi.hom_ext
    intro i
    dsimp only [F, U, factorTorus]
    simp only [Category.assoc, Pi.lift_comp_π, Category.id_comp]
    rw [← Category.assoc, Pi.lift_comp_π, Pi.lift_comp_π]

/-- The integral component-coordinate decomposition gives an actual product
presentation of the original coordinate maximal torus over every base scheme. -/
def torusProductIso (S : Scheme.{u}) :
    pi (D.factorTorus S) ≅ splitTorus S M.coordinates := by
  classical
  let : Fintype M.coordinates := M.fintypeCoordinates
  exact D.coordinateProductIso S ≪≫
    splitTorus.exponentIsoOfEquiv S M.coordinates M.basis.support D.characters

/-- The actual inclusion of a component block in the full coordinate torus. -/
def torusFactorInclusion (S : Scheme.{u}) (c : Component M.basis) :
    D.factorTorus S c ⟶ splitTorus S M.coordinates :=
  piFactorInclusionHom (D.factorTorus S) c ≫ (D.torusProductIso S).hom

/-- The actual projection from the full coordinate torus to a component block. -/
def torusFactorProjection (S : Scheme.{u}) (c : Component M.basis) :
    splitTorus S M.coordinates ⟶ D.factorTorus S c :=
  (D.torusProductIso S).inv ≫ Pi.π (D.factorTorus S) c

/-- The component inclusion has the supplied actual projection as retraction. -/
theorem torusFactorInclusion_projection (S : Scheme.{u}) (c : Component M.basis) :
    D.torusFactorInclusion S c ≫ D.torusFactorProjection S c = 𝟙 _ := by
  simp only [torusFactorInclusion, torusFactorProjection, Category.assoc,
    Iso.hom_inv_id_assoc]
  exact piFactorInclusionHom_π_self (D.factorTorus S) c

/-- Distinct integral component torus blocks have zero cross projection. -/
theorem torusFactorInclusion_projection_ne (S : Scheme.{u})
    (c d : Component M.basis) (h : c ≠ d) :
    D.torusFactorInclusion S c ≫ D.torusFactorProjection S d = 0 := by
  simp only [torusFactorInclusion, torusFactorProjection, Category.assoc,
    Iso.hom_inv_id_assoc]
  exact piFactorInclusionHom_π_ne (D.factorTorus S) c d h

end RootComponentCoordinates

end Langlands.GroupScheme
