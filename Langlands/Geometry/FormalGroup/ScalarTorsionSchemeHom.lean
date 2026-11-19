import Langlands.Geometry.FormalGroup.ScalarTatePoints
import Langlands.Geometry.FormalGroup.ScalarTorsionSchemes

/-! # Integral formal maps on scalar-power kernel schemes -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw.Hom

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {L : ModuleLaw O R υ}
variable {π : O}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Integral formal maps act naturally on each actual affine point kernel. -/
def scalarTorsionPointNatTrans (f : Hom M N) (π : O) (n : ℕ) :
    M.torsionPointFunctor.{u, v, v} (π ^ n) ⟶ N.torsionPointFunctor (π ^ n) where
  app A := ModuleCat.ofHom (f.scalarTorsionPointsMap π n A)
  naturality {A B} φ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (f.onAlgebraPoints_natural φ.hom x.val).symm

variable (hM : M.IsPiDivisible π) (hN : N.IsPiDivisible π) (hL : L.IsPiDivisible π)

/-- The map of represented finite kernels induced by an actual integral formal map. -/
def scalarTorsionSchemeMap (f : Hom M N) (n : ℕ) :
    hM.torsionSchemeInclusions.obj n ⟶ hN.torsionSchemeInclusions.obj n :=
  (hM.torsionKernelModel n).commGroupSchemeMap (hN.torsionKernelModel n)
    (f.scalarTorsionPointNatTrans π n)

theorem scalarTorsionSchemeMap_affinePoints (f : Hom M N) (n : ℕ)
    {A : CommAlgCat.{v} R}
    (x : (algSpec (CommRingCat.of R)).obj (op A) ⟶ (hM.torsionKernelModel n).commGroupScheme.X) :
    (hN.torsionKernelModel n).affinePointsEquiv A
        (x ≫ (f.scalarTorsionSchemeMap hM hN n).toMul.hom.hom) =
      f.scalarTorsionPointsMap π n A ((hM.torsionKernelModel n).affinePointsEquiv A x) :=
  (hM.torsionKernelModel n).commGroupSchemeMap_affinePoints (hN.torsionKernelModel n)
    (f.scalarTorsionPointNatTrans π n) x

@[simp]
theorem scalarTorsionSchemeMap_id (n : ℕ) :
    (Hom.id M).scalarTorsionSchemeMap hM hM n = 𝟙 _ := by
  have e : (Hom.id M).scalarTorsionPointNatTrans π n = 𝟙 _ := by
    apply NatTrans.ext
    funext A
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact Hom.onAlgebraPoints_id x.val
  rw [scalarTorsionSchemeMap, e]
  exact (hM.torsionKernelModel n).commGroupSchemeMap_id

theorem scalarTorsionSchemeMap_comp (g : Hom N L) (f : Hom M N) (n : ℕ) :
    (g.comp f).scalarTorsionSchemeMap hM hL n =
      f.scalarTorsionSchemeMap hM hN n ≫ g.scalarTorsionSchemeMap hN hL n := by
  have e : (g.comp f).scalarTorsionPointNatTrans π n =
      f.scalarTorsionPointNatTrans π n ≫ g.scalarTorsionPointNatTrans π n := by
    apply NatTrans.ext
    funext A
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact Hom.onAlgebraPoints_comp g f x.val
  rw [scalarTorsionSchemeMap, e]
  exact (hM.torsionKernelModel n).commGroupSchemeMap_comp
    (hN.torsionKernelModel n) (hL.torsionKernelModel n)
    (f.scalarTorsionPointNatTrans π n) (g.scalarTorsionPointNatTrans π n)

/-- Integral formal maps commute with the inclusions of the represented torsion schemes. -/
theorem scalarTorsionSchemeMap_inclusion (f : Hom M N) {m n : ℕ} (i : m ⟶ n) :
    hM.torsionSchemeInclusions.map i ≫ f.scalarTorsionSchemeMap hM hN n =
      f.scalarTorsionSchemeMap hM hN m ≫ hN.torsionSchemeInclusions.map i := by
  change (hM.torsionKernelModel m).commGroupSchemeMap (hM.torsionKernelModel n)
      (M.torsionIncl π (leOfHom i)) ≫
    (hM.torsionKernelModel n).commGroupSchemeMap (hN.torsionKernelModel n)
      (f.scalarTorsionPointNatTrans π n) =
    (hM.torsionKernelModel m).commGroupSchemeMap (hN.torsionKernelModel m)
      (f.scalarTorsionPointNatTrans π m) ≫
    (hN.torsionKernelModel m).commGroupSchemeMap (hN.torsionKernelModel n)
      (N.torsionIncl π (leOfHom i))
  erw [← FiniteKernelModel.commGroupSchemeMap_comp, ← FiniteKernelModel.commGroupSchemeMap_comp]
  congr 1

/-- Integral formal maps commute with the scalar transitions on the represented kernels. -/
theorem scalarTorsionSchemeMap_transition (f : Hom M N) {m n : ℕ} (i : m ⟶ n) :
    hM.torsionSchemeTower.map i.op ≫ f.scalarTorsionSchemeMap hM hN m =
      f.scalarTorsionSchemeMap hM hN n ≫ hN.torsionSchemeTower.map i.op := by
  change (hM.torsionKernelModel n).commGroupSchemeMap (hM.torsionKernelModel m)
      (M.torsionTransition π (leOfHom i)) ≫
    (hM.torsionKernelModel m).commGroupSchemeMap (hN.torsionKernelModel m)
      (f.scalarTorsionPointNatTrans π m) =
    (hM.torsionKernelModel n).commGroupSchemeMap (hN.torsionKernelModel n)
      (f.scalarTorsionPointNatTrans π n) ≫
    (hN.torsionKernelModel n).commGroupSchemeMap (hN.torsionKernelModel m)
      (N.torsionTransition π (leOfHom i))
  erw [← FiniteKernelModel.commGroupSchemeMap_comp, ← FiniteKernelModel.commGroupSchemeMap_comp]
  congr 1
  apply NatTrans.ext
  funext A
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change f.onAlgebraPoints (((M.torsionTransition π (leOfHom i)).app A x).val) =
    ((N.torsionTransition π (leOfHom i)).app A (f.scalarTorsionPointsMap π n A x)).val
  erw [torsionTransition_app_val, torsionTransition_app_val]
  exact map_smul f.onAlgebraPoints _ _

/-- The induced maps are a transformation of the direct diagrams. -/
def scalarTorsionSchemeInclusionNatTrans (f : Hom M N) :
    hM.torsionSchemeInclusions ⟶ hN.torsionSchemeInclusions where
  app n := f.scalarTorsionSchemeMap hM hN n
  naturality _ _ i := f.scalarTorsionSchemeMap_inclusion hM hN i

/-- The same maps give a transformation of the inverse diagrams. -/
def scalarTorsionSchemeTowerNatTrans (f : Hom M N) :
    hM.torsionSchemeTower ⟶ hN.torsionSchemeTower where
  app n := f.scalarTorsionSchemeMap hM hN n.unop
  naturality _ _ i := f.scalarTorsionSchemeMap_transition hM hN i.unop

end Langlands.FormalGroup.ModuleLaw.Hom
