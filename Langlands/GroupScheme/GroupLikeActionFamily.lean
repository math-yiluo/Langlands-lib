import Langlands.Algebra.ConvolutionBaseChange
import Langlands.Algebra.ConvolutionFamilyRigidity
import Langlands.GroupScheme.HopfSpecConvolution
import Langlands.GroupScheme.AutomorphicAction

/-! # Convolution families induced by actual automorphic actions -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry WithConv
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.AutomorphicAction

variable {k R : Type u} [Field k] [CommRing R] [Algebra k R]
    {C : CommHopfAlgCat.{u} (CommRingCat.of k)}
    {H : GroupScheme (Spec (CommRingCat.of k))}

local instance coefficientAlgebra (A : CommAlgCat.{u} (CommRingCat.of R)) :
    Algebra k A := Algebra.compHom A (algebraMap k R)

local instance coefficientTower (A : CommAlgCat.{u} (CommRingCat.of R)) :
    IsScalarTower k R A := IsScalarTower.of_algebraMap_eq' rfl

/-- The coefficient algebra of a parameter algebra, viewed over the field. -/
abbrev fieldCoefficients (A : CommAlgCat.{u} (CommRingCat.of R)) :
    CommAlgCat.{u} (CommRingCat.of k) := CommAlgCat.of k A

/-- The affine test map induced by the parameter-algebra structure. -/
def parameterSpecMap (A : CommAlgCat.{u} (CommRingCat.of R)) :
    (algSpec (CommRingCat.of k)).obj (op (fieldCoefficients A)) ⟶
      (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k R)) :=
  (algSpec (CommRingCat.of k)).map
    (CommAlgCat.ofHom (IsScalarTower.toAlgHom k R A)).op

/-- The affine test map induced by a coefficient-algebra map. -/
def coefficientSpecMap {A B : CommAlgCat.{u} (CommRingCat.of R)} (φ : A →ₐ[R] B) :
    (algSpec (CommRingCat.of k)).obj (op (fieldCoefficients B)) ⟶
      (algSpec (CommRingCat.of k)).obj (op (fieldCoefficients A)) :=
  (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom (φ.restrictScalars k)).op

theorem coefficientSpecMap_parameterSpecMap
    {A B : CommAlgCat.{u} (CommRingCat.of R)} (φ : A →ₐ[R] B) :
    coefficientSpecMap (k := k) φ ≫ parameterSpecMap (k := k) A =
      parameterSpecMap (k := k) B := by
  have h : (φ.restrictScalars k).comp (IsScalarTower.toAlgHom k R A) =
      IsScalarTower.toAlgHom k R B := by
    ext r
    exact φ.commutes r
  exact (((algSpec (CommRingCat.of k)).map_comp
    (CommAlgCat.ofHom (φ.restrictScalars k)).op
    (CommAlgCat.ofHom (IsScalarTower.toAlgHom k R A)).op).symm).trans
      (congrArg (fun f : R →ₐ[k] B =>
        (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom f).op) h)

variable (hspan : Submodule.span k {c : C | IsGroupLikeElem k c} = ⊤)

/-- Scalar-extended convolution points identify naturally with actual affine
points of the original Hopf spectrum. -/
def parameterPointsEquiv (A : CommAlgCat.{u} (CommRingCat.of R)) :
    WithConv (R ⊗[k] C →ₐ[R] A) ≃*
      ((algSpec (CommRingCat.of k)).obj (op (fieldCoefficients A)) ⟶
        ((hopfSpec (CommRingCat.of k)).obj (op C)).X) :=
  (Langlands.ConvolutionFamily.baseChangeMulEquiv hspan).trans
    (HopfSpecPoints.specPointMulEquiv
      (R := CommRingCat.of k) (C := C) (A := fieldCoefficients A))

theorem parameterPointsEquiv_naturality
    {A B : CommAlgCat.{u} (CommRingCat.of R)} (φ : A →ₐ[R] B)
    (x : WithConv (R ⊗[k] C →ₐ[R] A)) :
    coefficientSpecMap (k := k) φ ≫ parameterPointsEquiv hspan A x =
      parameterPointsEquiv hspan B (toConv (φ.comp x.ofConv)) := by
  exact HopfSpecPoints.specPoint_precomp
    (R := CommRingCat.of k) (C := C)
    (A := fieldCoefficients A) (B := fieldCoefficients B) (φ.restrictScalars k)
    (Langlands.ConvolutionFamily.baseChangeMulEquiv hspan x).ofConv

variable (a : AutomorphicAction H ((hopfSpec (CommRingCat.of k)).obj (op C)))
    (s : (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k R)) ⟶ H.X)

/-- The action of a parameter-valued point, transported to convolution points. -/
def convolutionPointAut (A : CommAlgCat.{u} (CommRingCat.of R)) :
    MulAut (WithConv (R ⊗[k] C →ₐ[R] A)) :=
  (parameterPointsEquiv hspan A).trans
    ((a.pointAut _ (parameterSpecMap A ≫ s)).trans (parameterPointsEquiv hspan A).symm)

@[simp]
theorem parameterPointsEquiv_convolutionPointAut
    (A : CommAlgCat.{u} (CommRingCat.of R)) (x : WithConv (R ⊗[k] C →ₐ[R] A)) :
    parameterPointsEquiv hspan A (convolutionPointAut hspan a s A x) =
      a.act (parameterSpecMap A ≫ s) (parameterPointsEquiv hspan A x) := by
  exact (parameterPointsEquiv hspan A).apply_symm_apply _

/-- An actual automorphic action gives a natural convolution-monoid family. -/
def convolutionFamily : Langlands.ConvolutionFamily.EndFamily R (R ⊗[k] C) where
  app A := (convolutionPointAut hspan a s A).toMonoidHom
  naturality {A B} φ x := by
    apply WithConv.toConv_injective
    apply (parameterPointsEquiv hspan B).injective
    change parameterPointsEquiv hspan B
        (convolutionPointAut hspan a s B (toConv (φ.comp x.ofConv))) =
      parameterPointsEquiv hspan B
        (toConv (φ.comp (convolutionPointAut hspan a s A x).ofConv))
    rw [parameterPointsEquiv_convolutionPointAut,
      ← parameterPointsEquiv_naturality hspan φ (convolutionPointAut hspan a s A x),
      parameterPointsEquiv_convolutionPointAut,
      a.naturality, ← Category.assoc, coefficientSpecMap_parameterSpecMap,
      parameterPointsEquiv_naturality]

end Langlands.GroupScheme.AutomorphicAction
