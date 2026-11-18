import Langlands.Geometry.FormalGroup.OrderRationalEndAlgebra
import Langlands.Geometry.FormalGroup.DrinfeldFramedAtlas
import Langlands.Geometry.FormalGroup.GlobalAtlasOrderRationalMorphism
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.Group.Units.Equiv

/-! # Chosen matrix coordinates on an actual special formal frame -/

noncomputable section

universe u v s

namespace Langlands.FormalGroup.LocalDivision

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ]

namespace SpecialModule

/-- A chosen matrix algebra identification of the actual full-order rational endomorphisms of the frame. -/
abbrev MatrixCoordinates (Φ : SpecialModule K D ι κ) :=
  Matrix (Fin (CentralSimple.reducedDegree K D)) (Fin (CentralSimple.reducedDegree K D)) K ≃ₐ[K]
    ModuleLaw.OrderAction.RationalHom K Φ.order Φ.order

namespace MatrixCoordinates

variable {Φ : SpecialModule K D ι κ} (c : Φ.MatrixCoordinates)

/-- The actual chosen matrix algebra identification gives an equivalence of the actual unit groups. -/
def unitEquiv : GL (Fin (CentralSimple.reducedDegree K D)) K ≃*
    (ModuleLaw.OrderAction.RationalHom K Φ.order Φ.order)ˣ :=
  Units.mapEquiv c.toRingEquiv.toMulEquiv

/-- Invertible matrices give exactly the actual full-order rational self quasi-isogenies of the frame. -/
def quasiIsogenyEquiv : GL (Fin (CentralSimple.reducedDegree K D)) K ≃
    ModuleLaw.OrderAction.QuasiIsogeny K Φ.order Φ.order :=
  c.unitEquiv.toEquiv.trans ModuleLaw.OrderAction.QuasiIsogeny.unitEquiv

/-- Both actual rational inverse maps are those specified by the chosen matrix coordinates. -/
def quasiIsogeny (g : GL (Fin (CentralSimple.reducedDegree K D)) K) :
    ModuleLaw.OrderAction.QuasiIsogeny K Φ.order Φ.order := c.quasiIsogenyEquiv g

@[simp]
theorem quasiIsogeny_hom (g : GL (Fin (CentralSimple.reducedDegree K D)) K) :
    (c.quasiIsogeny g).hom = c (g : Matrix _ _ K) := rfl

@[simp]
theorem quasiIsogeny_inv (g : GL (Fin (CentralSimple.reducedDegree K D)) K) :
    (c.quasiIsogeny g).inv = c ((g⁻¹ : GL _ K) : Matrix _ _ K) := rfl

/-- Matrix multiplication is the actual functional composition of the resulting rational maps. -/
theorem quasiIsogeny_mul (g h : GL (Fin (CentralSimple.reducedDegree K D)) K) :
    c.quasiIsogeny (g * h) = (c.quasiIsogeny h).trans (c.quasiIsogeny g) := by
  apply ModuleLaw.OrderAction.QuasiIsogeny.ext
  exact c.map_mul (g : Matrix _ _ K) (h : Matrix _ _ K)

@[simp]
theorem quasiIsogeny_one : c.quasiIsogeny 1 = ModuleLaw.OrderAction.QuasiIsogeny.refl Φ.order := by
  apply ModuleLaw.OrderAction.QuasiIsogeny.ext
  exact c.map_one

@[simp]
theorem quasiIsogeny_inv_group (g : GL (Fin (CentralSimple.reducedDegree K D)) K) :
    c.quasiIsogeny g⁻¹ = (c.quasiIsogeny g).symm := by
  apply ModuleLaw.OrderAction.QuasiIsogeny.ext
  rfl

/-- Central scalar matrices correspond to the actual scalar rational endomorphisms of the frame. -/
theorem quasiIsogeny_scalar_hom (a : Kˣ) :
    (c.quasiIsogeny (Matrix.GeneralLinearGroup.scalar (Fin (CentralSimple.reducedDegree K D)) a)).hom =
      (a : K) • ModuleLaw.OrderAction.RationalHom.id Φ.order := by
  change c (Matrix.scalar _ (a : K)) = (a : K) • ModuleLaw.OrderAction.RationalHom.id Φ.order
  exact c.commutes (a : K)

end MatrixCoordinates
end SpecialModule

namespace DrinfeldFramedAtlas

variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R] {π : 𝒪[K]}
variable {A : Nilp.{v, u} R (algebraMap 𝒪[K] R π)}
variable {Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι) (R := κ) π}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Extend the actual matrix quasi-endomorphism along the residue map and restrict to the actual source cover. -/
def matrixSourceQuasiIsogeny (X : DrinfeldFramedAtlas Φ A) (c : Φ.val.MatrixCoordinates)
    (g : GL (Fin (CentralSimple.reducedDegree K D)) K) :
    BasicAtlas.OrderAction.QuasiIsogeny K X.source.order X.source.order rfl :=
  BasicAtlas.ofGlobalOrderQuasiIsogeny ((c.quasiIsogeny g).map X.residueMap)
    X.target.val.reduction.atlas.opens X.target.val.reduction.atlas.covers

/-- The identity matrix gives the actual whole source identity quasi-isogeny. -/
@[simp]
theorem matrixSourceQuasiIsogeny_one (X : DrinfeldFramedAtlas Φ A) (c : Φ.val.MatrixCoordinates) :
    X.matrixSourceQuasiIsogeny c 1 = BasicAtlas.OrderAction.QuasiIsogeny.refl X.source.order := by
  simp only [matrixSourceQuasiIsogeny, SpecialModule.MatrixCoordinates.quasiIsogeny_one,
    ModuleLaw.OrderAction.QuasiIsogeny.map_refl, BasicAtlas.ofGlobalOrderQuasiIsogeny_refl]
  rfl

/-- Matrix multiplication retains whole actual source composition under coefficient extension and restriction. -/
theorem matrixSourceQuasiIsogeny_mul (X : DrinfeldFramedAtlas Φ A) (c : Φ.val.MatrixCoordinates)
    (g h : GL (Fin (CentralSimple.reducedDegree K D)) K) :
    X.matrixSourceQuasiIsogeny c (g * h) =
      (X.matrixSourceQuasiIsogeny c h).trans (X.matrixSourceQuasiIsogeny c g) := by
  simp only [matrixSourceQuasiIsogeny, SpecialModule.MatrixCoordinates.quasiIsogeny_mul,
    ModuleLaw.OrderAction.QuasiIsogeny.map_trans, BasicAtlas.ofGlobalOrderQuasiIsogeny_trans]
  rfl

/-- The inverse matrix retains the specified whole actual source inverse map. -/
@[simp]
theorem matrixSourceQuasiIsogeny_inv (X : DrinfeldFramedAtlas Φ A) (c : Φ.val.MatrixCoordinates)
    (g : GL (Fin (CentralSimple.reducedDegree K D)) K) :
    X.matrixSourceQuasiIsogeny c g⁻¹ = (X.matrixSourceQuasiIsogeny c g).symm := by
  simp only [matrixSourceQuasiIsogeny, SpecialModule.MatrixCoordinates.quasiIsogeny_inv_group,
    ModuleLaw.OrderAction.QuasiIsogeny.map_symm, BasicAtlas.ofGlobalOrderQuasiIsogeny_symm]
  rfl

end DrinfeldFramedAtlas

end Langlands.FormalGroup.LocalDivision
