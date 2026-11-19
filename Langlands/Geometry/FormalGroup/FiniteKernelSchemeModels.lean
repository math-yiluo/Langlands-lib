import Langlands.Geometry.FormalGroup.ScalarTorsionSchemes
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-! # Canonical comparisons of represented finite kernel schemes -/

noncomputable section
universe u v

namespace Langlands.FormalGroup.ModuleLaw.Hom.FiniteKernelModel
open CategoryTheory Opposite _root_.AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ υ ω : Type} [Finite σ] [Finite τ] [Finite υ] [Finite ω]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {P : ModuleLaw O R υ} {Q : ModuleLaw O R ω}
variable {f : Hom M N} {g : Hom P Q}
variable (K K' : FiniteKernelModel f) (L L' : FiniteKernelModel g)

/-- The finite projective coordinate algebra gives a locally finitely presented kernel scheme. -/
theorem locallyOfFinitePresentation_commGroupScheme :
    LocallyOfFinitePresentation K.commGroupScheme.X.hom := by
  let : Module.FinitePresentation R K.coordinateAlgebra :=
    Module.finitePresentation_of_projective R K.coordinateAlgebra
  let : Algebra.FinitePresentation R K.coordinateAlgebra := inferInstance
  change LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R K.coordinateAlgebra)))
  exact (LocallyOfFinitePresentation.SpecMap_iff _).mpr
    (RingHom.finitePresentation_algebraMap.mpr inferInstance)

/-- Two models of one actual kernel are canonically isomorphic, by the identity
of the represented kernel-point functor. -/
def commGroupSchemeIso : K.commGroupScheme ≅ K'.commGroupScheme where
  hom := K.commGroupSchemeMap K' (𝟙 f.kernelPointFunctor.{u, v, v})
  inv := K'.commGroupSchemeMap K (𝟙 f.kernelPointFunctor.{u, v, v})
  hom_inv_id := by
    rw [← commGroupSchemeMap_comp, Category.id_comp, commGroupSchemeMap_id]
  inv_hom_id := by
    rw [← commGroupSchemeMap_comp, Category.id_comp, commGroupSchemeMap_id]

/-- The comparison acts as the identity on the actual affine kernel points. -/
@[simp]
theorem affinePointsEquiv_commGroupSchemeIso (A : CommAlgCat.{v} R)
    (x : (algSpec (CommRingCat.of R)).obj (op A) ⟶ K.commGroupScheme.X) :
    K'.affinePointsEquiv A (x ≫ (K.commGroupSchemeIso K').hom.toMul.hom.hom) =
      K.affinePointsEquiv A x := by
  rw [commGroupSchemeIso, commGroupSchemeMap_affinePoints]
  rfl

/-- Canonical model changes commute with the scheme map of any actual kernel-point map. -/
theorem commGroupSchemeIso_natural
    (a : f.kernelPointFunctor.{u, v, v} ⟶ g.kernelPointFunctor) :
    (K.commGroupSchemeIso K').hom ≫ K'.commGroupSchemeMap L' a =
      K.commGroupSchemeMap L a ≫ (L.commGroupSchemeIso L').hom := by
  change K.commGroupSchemeMap K' (𝟙 _) ≫ K'.commGroupSchemeMap L' a =
    K.commGroupSchemeMap L a ≫ L.commGroupSchemeMap L' (𝟙 _)
  rw [← commGroupSchemeMap_comp, ← commGroupSchemeMap_comp, Category.id_comp, Category.comp_id]

/-- Three choices of a kernel model agree under the iterated canonical comparison. -/
@[simp]
theorem commGroupSchemeIso_trans (K'' : FiniteKernelModel f) :
    (K.commGroupSchemeIso K').trans (K'.commGroupSchemeIso K'') = K.commGroupSchemeIso K'' := by
  apply Iso.ext
  change K.commGroupSchemeMap K' (𝟙 _) ≫ K'.commGroupSchemeMap K'' (𝟙 _) = _
  rw [← commGroupSchemeMap_comp, Category.id_comp]
  rfl

end Langlands.FormalGroup.ModuleLaw.Hom.FiniteKernelModel

namespace Langlands.FormalGroup.ModuleLaw.IsPiDivisible
open Opposite _root_.AlgebraicGeometry

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ : Type} [Finite σ] {M : ModuleLaw O R σ} {π : O}

/-- Each actual scalar torsion scheme is locally of finite presentation. -/
theorem torsionSchemeTower_locallyOfFinitePresentation (hM : M.IsPiDivisible π) (n : ℕ) :
    LocallyOfFinitePresentation (hM.torsionSchemeTower.obj (op n)).X.hom :=
  (hM.torsionKernelModel n).locallyOfFinitePresentation_commGroupScheme

end Langlands.FormalGroup.ModuleLaw.IsPiDivisible
