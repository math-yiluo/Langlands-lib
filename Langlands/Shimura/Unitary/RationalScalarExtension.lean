import Langlands.Shimura.Coefficients.Algebraic
import Langlands.Shimura.Unitary.SchemeScalarExtension
import Langlands.Shimura.Unitary.DeligneGroupScheme

noncomputable section
universe u v
open CategoryTheory Opposite AlgebraicGeometry Algebra
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.Shimura.AlgebraInvolution

section Coefficients
variable {A : Type v} [Ring A] [Algebra ℚ A]
  (L S : Type u) [Field L] [Algebra ℚ L]
  [CommRing S] [Algebra ℚ S] [Algebra L S]

/-- The rational coefficient comparison is the general tensor-tower equivalence. -/
theorem baseChangeTowerEquiv_toAlgHom_eq_towerMap :
    (baseChangeTowerEquiv ℚ L S A).toAlgHom = towerMap (A := A) L S := by
  apply AlgHom.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul s a => simp
  | add x y hx hy => simp only [map_add, hx, hy]

variable (σ : AlgebraInvolution ℚ A)

/-- The existing rational point map is the underlying homomorphism of the tower equivalence. -/
theorem baseChangeTowerSimilitudes_toMonoidHom_eq_towerPoints :
    (baseChangeTowerSimilitudes L S σ).toMonoidHom = σ.towerPoints L S := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  apply Prod.ext
  · apply Units.ext
    exact DFunLike.congr_fun (baseChangeTowerEquiv_toAlgHom_eq_towerMap L S) (x.val.1 : S ⊗[ℚ] A)
  · exact Units.ext rfl

/-- In particular the existing rational point map is bijective. -/
theorem towerPoints_bijective : Function.Bijective (σ.towerPoints L S) := by
  rw [← baseChangeTowerSimilitudes_toMonoidHom_eq_towerPoints]
  exact (baseChangeTowerSimilitudes L S σ).bijective

variable {S} {T : Type u} [CommRing T] [Algebra ℚ T] [Algebra L T]

/-- Rational towerPoints commute with every change of the final coefficient algebra. -/
theorem towerPoints_naturality (f : S →ₐ[L] T) (g : σ.Points S) :
    σ.towerPoints L T (σ.pointsMap (f.restrictScalars ℚ) g) =
      (σ.baseChange L).pointsMap f (σ.towerPoints L S g) := by
  simp only [← baseChangeTowerSimilitudes_toMonoidHom_eq_towerPoints]
  exact baseChangeTowerSimilitudes_naturality σ f g

end Coefficients

namespace SchemeModel
variable {A : Type} [Ring A] [Algebra ℚ A]
  {κ : Type} [Fintype κ] (b : Module.Basis κ ℚ A) (σ : AlgebraInvolution ℚ A)

/-- The actual real pullback of the rational group is the existing Deligne target model. -/
def realScalarExtensionIso :
    baseChangedGroupScheme b σ (scalarBaseMap ℚ ℝ) ≅
      (σ.baseChange ℝ).similitudeGroupScheme (b.baseChange ℝ) :=
  scalarExtensionIso ℝ b σ

local instance realSectionsAlgebra (T : Over (Spec (CommRingCat.of ℝ))) :
    Algebra ℝ (restrictedSections ℚ ℝ T) :=
  inferInstanceAs (Algebra ℝ ((algΓ (CommRingCat.of ℝ)).obj T).unop)

/-- On arbitrary real test schemes the isomorphism is the existing rational towerPoints map. -/
theorem realScalarExtensionIso_points (T : Over (Spec (CommRingCat.of ℝ)))
    (x : T ⟶ (baseChangedGroupScheme b σ (scalarBaseMap ℚ ℝ)).X) :
    pointsEquiv (b.baseChange ℝ) (σ.baseChange ℝ) T
        (x ≫ (realScalarExtensionIso b σ).hom.hom.hom) =
      σ.towerPoints ℝ (restrictedSections ℚ ℝ T)
        (baseChangedPointsEquiv b σ (scalarBaseMap ℚ ℝ) T x) := by
  rw [realScalarExtensionIso, scalarExtensionIso_points]
  exact DFunLike.congr_fun
    (baseChangeTowerSimilitudes_toMonoidHom_eq_towerPoints ℝ (restrictedSections ℚ ℝ T) σ) _

/-- The real comparison preserves the actual multiplier morphism. -/
theorem realScalarExtensionIso_multiplier :
    (realScalarExtensionIso b σ).hom ≫ multiplier (b.baseChange ℝ) (σ.baseChange ℝ) =
      baseChangedMultiplier b σ (scalarBaseMap ℚ ℝ) :=
  scalarExtensionIso_multiplier ℝ b σ

variable (h : ComplexHom (σ.baseChange ℝ))

/-- A Deligne homomorphism with target the actual real pullback of the rational group. -/
def rationalDeligneGroupSchemeMap :
    Langlands.Shimura.DeligneTorus.groupScheme ⟶
      baseChangedGroupScheme b σ (scalarBaseMap ℚ ℝ) :=
  h.deligneGroupSchemeMap (b.baseChange ℝ) ≫ (realScalarExtensionIso b σ).inv

/-- The transported Deligne map recovers the existing real model map. -/
theorem rationalDeligneGroupSchemeMap_comparison :
    rationalDeligneGroupSchemeMap b σ h ≫ (realScalarExtensionIso b σ).hom =
      h.deligneGroupSchemeMap (b.baseChange ℝ) := by
  simp [rationalDeligneGroupSchemeMap]

/-- The inverse convention also has target the actual rational group's real pullback. -/
def rationalInverseDeligneGroupSchemeMap :
    Langlands.Shimura.DeligneTorus.groupScheme ⟶
      baseChangedGroupScheme b σ (scalarBaseMap ℚ ℝ) :=
  h.inverseDeligneGroupSchemeMap (b.baseChange ℝ) ≫ (realScalarExtensionIso b σ).inv

theorem rationalInverseDeligneGroupSchemeMap_comparison :
    rationalInverseDeligneGroupSchemeMap b σ h ≫ (realScalarExtensionIso b σ).hom =
      h.inverseDeligneGroupSchemeMap (b.baseChange ℝ) := by
  simp [rationalInverseDeligneGroupSchemeMap]

/-- Affine points of the transported direct map retain the original Deligne formula. -/
theorem rationalDeligneGroupSchemeMap_affinePoints {S : CommAlgCat ℝ}
    (f : (algSpec (CommRingCat.of ℝ)).obj (op S) ⟶
      Langlands.Shimura.DeligneTorus.groupScheme.X) :
    (σ.baseChange ℝ).similitudeAffinePointsEquiv (b.baseChange ℝ) S
      (f ≫ (rationalDeligneGroupSchemeMap b σ h ≫
        (realScalarExtensionIso b σ).hom).hom.hom) =
      h.delignePoints S (Langlands.Shimura.DeligneTorus.affinePointsEquiv S f) := by
  rw [rationalDeligneGroupSchemeMap_comparison]
  exact h.deligneGroupSchemeMap_affinePoints (b.baseChange ℝ) f

/-- Affine points retain inversion for the inverse-convention map. -/
theorem rationalInverseDeligneGroupSchemeMap_affinePoints {S : CommAlgCat ℝ}
    (f : (algSpec (CommRingCat.of ℝ)).obj (op S) ⟶
      Langlands.Shimura.DeligneTorus.groupScheme.X) :
    (σ.baseChange ℝ).similitudeAffinePointsEquiv (b.baseChange ℝ) S
      (f ≫ (rationalInverseDeligneGroupSchemeMap b σ h ≫
        (realScalarExtensionIso b σ).hom).hom.hom) =
      h.delignePoints S (Langlands.Shimura.DeligneTorus.affinePointsEquiv S f)⁻¹ := by
  rw [rationalInverseDeligneGroupSchemeMap_comparison]
  exact h.inverseDeligneGroupSchemeMap_affinePoints (b.baseChange ℝ) f

end SchemeModel
end Langlands.Shimura.AlgebraInvolution

namespace Langlands.Shimura.CentralSimpleUnitaryData

variable {E K A : Type} [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K] [Ring A] [Algebra K A] [Algebra E A]
  [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)

/-- Real scalar extension of the actual CM rational group has the existing Deligne target model. -/
def realGroupSchemeIso :
    D.rationalBaseChange (AlgebraInvolution.SchemeModel.scalarBaseMap ℚ ℝ) ≅
      (D.toSecondKindInvolution.rationalInvolution.baseChange ℝ).similitudeGroupScheme
        (D.rationalBasis.baseChange ℝ) :=
  AlgebraInvolution.SchemeModel.realScalarExtensionIso D.rationalBasis
    D.toSecondKindInvolution.rationalInvolution

end Langlands.Shimura.CentralSimpleUnitaryData
