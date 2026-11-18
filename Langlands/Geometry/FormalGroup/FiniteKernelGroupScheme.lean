import Langlands.Geometry.FormalGroup.FiniteKernel
import Langlands.GroupScheme.CorepresentedPoints
import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # The affine group schemes of represented formal kernels -/

noncomputable section
universe u v

namespace Langlands.FormalGroup.ModuleLaw.Hom
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ υ ω : Type} [Finite σ] [Finite τ] [Finite υ] [Finite ω]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {P : ModuleLaw O R υ} {Q : ModuleLaw O R ω}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- The additive kernel module, regarded as a commutative point group. -/
def kernelCommGroupPointFunctor (f : Hom M N) : CommAlgCat.{v} R ⥤ CommGrpCat.{v} :=
  f.kernelPointFunctor ⋙ forget₂ (ModuleCat.{v} O) AddCommGrpCat.{v} ⋙ AddCommGrpCat.toCommGrp

namespace FiniteKernelModel

variable {f : Hom M N} {g : Hom P Q}
variable (K : FiniteKernelModel f) (L : FiniteKernelModel g)

/-- The original coordinate algebra corepresents the commutative point groups. -/
def commCorepresentation :
    (f.kernelCommGroupPointFunctor ⋙ forget CommGrpCat).CorepresentableBy K.coordinateAlgebra where
  homEquiv := K.represents.homEquiv
  homEquiv_comp φ ψ := K.represents.homEquiv_comp φ ψ

/-- The group law on the actual represented point kernel gives its affine group scheme. -/
def commGroupScheme : Langlands.CommGroupScheme (Spec (CommRingCat.of R)) :=
  GroupScheme.Corepresented.commGroupScheme f.kernelCommGroupPointFunctor K.commCorepresentation

theorem isFinite_commGroupScheme : IsFinite K.commGroupScheme.X.hom := by
  change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R K.coordinateAlgebra)))
  exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr K.finite)

theorem flat_commGroupScheme : Flat K.commGroupScheme.X.hom := by
  change Flat (Spec.map (CommRingCat.ofHom (algebraMap R K.coordinateAlgebra)))
  exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)

/-- The scheme points on an affine test recover the original formal kernel points. -/
def affinePointsEquiv (A : CommAlgCat.{v} R) :
    Additive ((algSpec (CommRingCat.of R)).obj (op A) ⟶ K.commGroupScheme.X) ≃+
      f.kernelPoints A :=
  (GroupScheme.Corepresented.affinePointsEquiv
    (R := CommRingCat.of R) (B := K.coordinateAlgebra)
    (f.kernelCommGroupPointFunctor ⋙ forget₂ CommGrpCat GrpCat)
    K.commCorepresentation A).toAdditive

theorem affinePointsEquiv_naturality {A B : CommAlgCat.{v} R} (φ : A ⟶ B)
    (x : (algSpec (CommRingCat.of R)).obj (op A) ⟶ K.commGroupScheme.X) :
    K.affinePointsEquiv B ((algSpec (CommRingCat.of R)).map φ.op ≫ x) =
      f.kernelMap φ (K.affinePointsEquiv A x) :=
  GroupScheme.Corepresented.affinePointsEquiv_naturality
    (R := CommRingCat.of R) (B := K.coordinateAlgebra)
    (f.kernelCommGroupPointFunctor ⋙ forget₂ CommGrpCat GrpCat) K.commCorepresentation φ x

/-- A transformation between actual point kernels induces a group-scheme homomorphism. -/
def commGroupSchemeMap
    (a : f.kernelPointFunctor.{u, v, v} ⟶ g.kernelPointFunctor) :
    K.commGroupScheme ⟶ L.commGroupScheme :=
  Additive.ofMul (GroupScheme.Corepresented.groupSchemeMap
    (R := CommRingCat.of R) (B := K.coordinateAlgebra) (C := L.coordinateAlgebra)
    (F := f.kernelCommGroupPointFunctor ⋙ forget₂ CommGrpCat GrpCat)
    (G := g.kernelCommGroupPointFunctor ⋙ forget₂ CommGrpCat GrpCat)
    K.commCorepresentation L.commCorepresentation
    (Functor.whiskerRight a
      (forget₂ (ModuleCat.{v} O) AddCommGrpCat.{v} ⋙ AddCommGrpCat.toCommGrp ⋙
        forget₂ CommGrpCat GrpCat)))

theorem commGroupSchemeMap_affinePoints
    (a : f.kernelPointFunctor.{u, v, v} ⟶ g.kernelPointFunctor)
    {A : CommAlgCat.{v} R}
    (x : (algSpec (CommRingCat.of R)).obj (op A) ⟶ K.commGroupScheme.X) :
    L.affinePointsEquiv A (x ≫ (K.commGroupSchemeMap L a).toMul.hom.hom) =
      a.app A (K.affinePointsEquiv A x) :=
  GroupScheme.Corepresented.groupSchemeMap_affinePoints
    (R := CommRingCat.of R) (B := K.coordinateAlgebra) (C := L.coordinateAlgebra)
    (F := f.kernelCommGroupPointFunctor ⋙ forget₂ CommGrpCat GrpCat)
    (G := g.kernelCommGroupPointFunctor ⋙ forget₂ CommGrpCat GrpCat)
    K.commCorepresentation L.commCorepresentation _ x

end FiniteKernelModel
end Langlands.FormalGroup.ModuleLaw.Hom
