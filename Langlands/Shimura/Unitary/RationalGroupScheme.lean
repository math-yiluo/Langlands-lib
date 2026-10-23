import Langlands.GroupScheme.CorepresentedPoints
import Langlands.GroupScheme.Multiplicative
import Langlands.Shimura.Unitary.SimilitudeCoordinates
import Langlands.Shimura.Unitary.CMData
import Langlands.Shimura.Unitary.Adelic

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry Algebra
open scoped CategoryTheory.MonObj

namespace Langlands.Shimura.AlgebraInvolution.SchemeModel

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {κ : Type u} [Fintype κ] (b : Module.Basis κ R A) (σ : AlgebraInvolution R A)

/-- The finite-basis similitude functor as an actual affine group scheme over the base ring. -/
abbrev groupScheme : GroupScheme (Spec (CommRingCat.of R)) :=
  GroupScheme.Corepresented.groupScheme (R := CommRingCat.of R) σ.similitudeFunctor
    (σ.similitudeCorepresentableBy b)

/-- Its underlying scheme is the spectrum of the explicit coordinate algebra. -/
theorem groupScheme_scheme :
    (groupScheme b σ).X.left = Spec (CommRingCat.of (σ.similitudeCoordinateRing b)) := rfl

/-- Its structure morphism is induced by the coefficient-ring inclusion. -/
theorem groupScheme_structureMap : (groupScheme b σ).X.hom =
    Spec.map (CommRingCat.ofHom (algebraMap R (σ.similitudeCoordinateRing b))) := rfl

instance groupScheme_isAffine : IsAffine (groupScheme b σ).X.left := by
  change IsAffine (Spec (CommRingCat.of (σ.similitudeCoordinateRing b)))
  infer_instance

/-- Affine points recover scalar-extended similitudes with their original group law. -/
def affinePointsEquiv (S : CommAlgCat R) :
    ((algSpec (CommRingCat.of R)).obj (op S) ⟶ (groupScheme b σ).X) ≃*
      (σ.baseChange S).similitudes :=
  GroupScheme.Corepresented.affinePointsEquiv (R := CommRingCat.of R) σ.similitudeFunctor
    (σ.similitudeCorepresentableBy b) S

/-- Affine point restriction is the original coefficient-change homomorphism. -/
theorem affinePointsEquiv_naturality {S S' : CommAlgCat R} (a : S ⟶ S')
    (x : (algSpec (CommRingCat.of R)).obj (op S) ⟶ (groupScheme b σ).X) :
    affinePointsEquiv b σ S' ((algSpec (CommRingCat.of R)).map a.op ≫ x) =
      σ.baseChangeMap a (affinePointsEquiv b σ S x) :=
  GroupScheme.Corepresented.affinePointsEquiv_naturality (R := CommRingCat.of R)
    σ.similitudeFunctor (σ.similitudeCorepresentableBy b) a x

/-- Points on any test scheme use its relative global-sections algebra. -/
def pointsEquiv (T : Over (Spec (CommRingCat.of R))) :
    (T ⟶ (groupScheme b σ).X) ≃*
      (σ.baseChange ((algΓ (CommRingCat.of R)).obj T).unop).similitudes :=
  GroupScheme.Corepresented.pointsEquiv (R := CommRingCat.of R) σ.similitudeFunctor
    (σ.similitudeCorepresentableBy b) T

/-- The point comparison commutes with restriction to an arbitrary test scheme. -/
theorem pointsEquiv_naturality {T T' : Over (Spec (CommRingCat.of R))}
    (a : T' ⟶ T) (x : T ⟶ (groupScheme b σ).X) :
    pointsEquiv b σ T' (a ≫ x) =
      σ.baseChangeMap ((algΓ (CommRingCat.of R)).map a).unop (pointsEquiv b σ T x) :=
  GroupScheme.Corepresented.pointsEquiv_naturality (R := CommRingCat.of R)
    σ.similitudeFunctor (σ.similitudeCorepresentableBy b) a x

/-- The multiplier of a geometric point, valued in the actual global units. -/
def multiplierPoints (T : Over (Spec (CommRingCat.of R))) :
    (T ⟶ (groupScheme b σ).X) →* (Γ(T.left, ⊤))ˣ :=
  (σ.baseChange ((algΓ (CommRingCat.of R)).obj T).unop).multiplier.comp
    (pointsEquiv b σ T).toMonoidHom

/-- Multipliers restrict along the map on global sections. -/
theorem multiplierPoints_naturality {T T' : Over (Spec (CommRingCat.of R))}
    (a : T' ⟶ T) (x : T ⟶ (groupScheme b σ).X) :
    multiplierPoints b σ T' (a ≫ x) =
      Units.map a.left.appTop.hom.toMonoidHom (multiplierPoints b σ T x) := by
  change (σ.baseChange _).multiplier (pointsEquiv b σ T' (a ≫ x)) = _
  rw [pointsEquiv_naturality]
  rfl

private def multiplierAsPoint (T : Over (Spec (CommRingCat.of R))) :
    (T ⟶ (groupScheme b σ).X) →* (T ⟶ (GroupScheme.Gm (Spec (CommRingCat.of R))).X) :=
  (GroupScheme.Gm.pointsEquiv _ T).symm.toMonoidHom.comp (multiplierPoints b σ T)

private theorem multiplierAsPoint_naturality {T T' : Over (Spec (CommRingCat.of R))}
    (a : T' ⟶ T) (x : T ⟶ (groupScheme b σ).X) :
    multiplierAsPoint b σ T' (a ≫ x) = a ≫ multiplierAsPoint b σ T x := by
  apply (GroupScheme.Gm.pointsEquiv _ T').injective
  change GroupScheme.Gm.pointsEquiv _ T' ((GroupScheme.Gm.pointsEquiv _ T').symm _) = _
  rw [MulEquiv.apply_symm_apply, GroupScheme.Gm.pointsEquiv_naturality]
  change _ = Units.map _ (GroupScheme.Gm.pointsEquiv _ T
    ((GroupScheme.Gm.pointsEquiv _ T).symm _))
  rw [MulEquiv.apply_symm_apply, multiplierPoints_naturality]

/-- The multiplier as an actual homomorphism to the existing multiplicative group scheme. -/
def multiplier : groupScheme b σ ⟶ (GroupScheme.Gm (Spec (CommRingCat.of R))).toGrp :=
  GroupScheme.homOfPoints (multiplierAsPoint b σ) (multiplierAsPoint_naturality b σ)

/-- This scheme homomorphism induces the original multiplier on every test scheme. -/
theorem multiplier_points (T : Over (Spec (CommRingCat.of R)))
    (x : T ⟶ (groupScheme b σ).X) :
    GroupScheme.Gm.pointsEquiv _ T (x ≫ (multiplier b σ).hom.hom) =
      multiplierPoints b σ T x := by
  have h : x ≫ (multiplier b σ).hom.hom = _ :=
    GroupScheme.comp_homOfPoints _ (multiplierAsPoint_naturality b σ) T x
  rw [h]
  exact (GroupScheme.Gm.pointsEquiv _ T).apply_symm_apply _

end Langlands.Shimura.AlgebraInvolution.SchemeModel

namespace Langlands.Shimura.CentralSimpleUnitaryData

variable {E K A : Type} [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K] [Ring A] [Algebra K A] [Algebra E A]
  [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)

/-- A rational finite basis is obtained from the actual finite CM algebra. -/
def rationalBasis : Module.Basis (Fin (Module.finrank ℚ A)) ℚ A := by
  letI : FiniteDimensional K A := D.finite
  letI : FiniteDimensional ℚ A := FiniteDimensional.trans ℚ K A
  exact Module.finBasis ℚ A

/-- The rational group scheme of the given central simple CM algebra and involution. -/
abbrev rationalGroupScheme : GroupScheme (Spec (CommRingCat.of ℚ)) :=
  AlgebraInvolution.SchemeModel.groupScheme D.rationalBasis D.toSecondKindInvolution.rationalInvolution

/-- The multiplier remains a rational scalar, as a morphism to Gm over Spec Q. -/
def rationalMultiplier : D.rationalGroupScheme ⟶ (GroupScheme.Gm (Spec (CommRingCat.of ℚ))).toGrp :=
  AlgebraInvolution.SchemeModel.multiplier D.rationalBasis D.toSecondKindInvolution.rationalInvolution

/-- The rational scheme represents the previously defined rational similitude functor. -/
def rationalAffinePointsEquiv (S : CommAlgCat ℚ) :
    ((algSpec (CommRingCat.of ℚ)).obj (op S) ⟶ D.rationalGroupScheme.X) ≃*
      (D.toSecondKindInvolution.rationalInvolution.baseChange S).similitudes :=
  AlgebraInvolution.SchemeModel.affinePointsEquiv D.rationalBasis
    D.toSecondKindInvolution.rationalInvolution S

omit [IsScalarTower E K A] in
/-- Restriction of rational affine points is the original scalar-extension map. -/
theorem rationalAffinePointsEquiv_naturality {S S' : CommAlgCat ℚ} (a : S ⟶ S')
    (x : (algSpec (CommRingCat.of ℚ)).obj (op S) ⟶ D.rationalGroupScheme.X) :
    D.rationalAffinePointsEquiv S' ((algSpec (CommRingCat.of ℚ)).map a.op ≫ x) =
      D.toSecondKindInvolution.rationalInvolution.baseChangeMap a
        (D.rationalAffinePointsEquiv S x) :=
  AlgebraInvolution.SchemeModel.affinePointsEquiv_naturality D.rationalBasis
    D.toSecondKindInvolution.rationalInvolution a x

/-- Its points over the existing rational finite adeles are the existing adelic group. -/
def finiteAdelicPointsEquiv :
    ((algSpec (CommRingCat.of ℚ)).obj
      (op (CommAlgCat.of ℚ (Global.FiniteAdeles ℚ))) ⟶ D.rationalGroupScheme.X) ≃*
      D.toSecondKindInvolution.rationalInvolution.FiniteAdelicPoints :=
  D.rationalAffinePointsEquiv (CommAlgCat.of ℚ (Global.FiniteAdeles ℚ))

omit [IsScalarTower E K A] in
/-- Restriction along finite-place evaluation is evaluation of adelic similitudes. -/
theorem finiteAdelicPointsEquiv_evaluation (v : Global.FinitePlace ℚ)
    (x : (algSpec (CommRingCat.of ℚ)).obj
      (op (CommAlgCat.of ℚ (Global.FiniteAdeles ℚ))) ⟶ D.rationalGroupScheme.X) :
    D.rationalAffinePointsEquiv (CommAlgCat.of ℚ (Global.FiniteCompletion ℚ v))
      ((algSpec (CommRingCat.of ℚ)).map
        (CommAlgCat.ofHom (AlgebraInvolution.finiteEvaluation v)).op ≫ x) =
      D.toSecondKindInvolution.rationalInvolution.pointsMap
        (AlgebraInvolution.finiteEvaluation v) (D.finiteAdelicPointsEquiv x) :=
  D.rationalAffinePointsEquiv_naturality
    (CommAlgCat.ofHom (AlgebraInvolution.finiteEvaluation v)) x

end Langlands.Shimura.CentralSimpleUnitaryData
