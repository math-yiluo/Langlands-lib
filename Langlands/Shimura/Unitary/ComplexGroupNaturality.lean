import Langlands.Shimura.Unitary.ComplexGroupSplitting

noncomputable section
open Algebra Module CategoryTheory
open scoped TensorProduct Classical
attribute [local instance 1100] Algebra.toModule

namespace Langlands.Shimura.ComplexMatrix

universe u v

variable {S T U : Type*} [CommRing S] [CommRing T] [CommRing U]

/-- Coefficient change on a family of general linear points and its scalar multiplier. -/
def splitGroupMap (n : ℕ) (I : Type*) (f : S →+* T) :
    ((I → (Matrix (Fin n) (Fin n) S)ˣ) × Sˣ) →*
      ((I → (Matrix (Fin n) (Fin n) T)ˣ) × Tˣ) where
  toFun p := (fun τ => Units.map (f.mapMatrix : Matrix (Fin n) (Fin n) S →+* Matrix (Fin n) (Fin n) T).toMonoidHom (p.1 τ),
    Units.map f.toMonoidHom p.2)
  map_one' := by
    apply Prod.ext
    · funext τ
      exact map_one (Units.map (f.mapMatrix : Matrix (Fin n) (Fin n) S →+* Matrix (Fin n) (Fin n) T).toMonoidHom)
    · exact map_one (Units.map f.toMonoidHom)
  map_mul' p q := by
    apply Prod.ext
    · funext τ
      exact map_mul (Units.map (f.mapMatrix : Matrix (Fin n) (Fin n) S →+* Matrix (Fin n) (Fin n) T).toMonoidHom) _ _
    · exact map_mul (Units.map f.toMonoidHom) _ _

@[simp] theorem splitGroupMap_id (n : ℕ) (I : Type*)
    (p : (I → (Matrix (Fin n) (Fin n) S)ˣ) × Sˣ) :
    splitGroupMap n I (RingHom.id S) p = p := by
  apply Prod.ext
  · funext τ
    apply Units.ext
    rfl
  · exact Units.ext rfl

@[simp] theorem splitGroupMap_comp (n : ℕ) (I : Type*) (f : S →+* T) (g : T →+* U)
    (p : (I → (Matrix (Fin n) (Fin n) S)ˣ) × Sˣ) :
    splitGroupMap n I (g.comp f) p = splitGroupMap n I g (splitGroupMap n I f p) := by
  apply Prod.ext
  · funext τ
    apply Units.ext
    rfl
  · exact Units.ext rfl

/-- The product of general linear point groups and one multiplicative point group. -/
def splitGroupFunctor (n : ℕ) (I : Type v) : CommAlgCat.{u} ℂ ⥤ GrpCat.{max u v} where
  obj S := GrpCat.of ((I → (Matrix (Fin n) (Fin n) S)ˣ) × Sˣ)
  map f := GrpCat.ofHom (splitGroupMap n I f.hom.toRingHom)
  map_id S := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    exact splitGroupMap_id n I
  map_comp f g := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    exact splitGroupMap_comp n I f.hom.toRingHom g.hom.toRingHom

end Langlands.Shimura.ComplexMatrix

namespace Langlands.Shimura.HarrisSignatureCharts

universe u v w z s
open NumberField
variable {E : Type u} {K : Type v} {A : Type w}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K]
  [Ring A] [Algebra E A] [Algebra K A]
  [Algebra ℚ A] [IsScalarTower ℚ E A]
  {σ : SecondKindInvolution E K A} {n : ℕ}
  {Φ : (E →+* ℝ) → (K →+* ℂ)}
  (C : HarrisSignatureCharts σ n Φ)
  {ι : Type z} [Fintype ι] (b : Module.Basis ι E A)
  {S : Type s} [CommRing S] [Algebra ℂ S] [Algebra ℝ S] [IsScalarTower ℝ ℂ S]
  {T : Type s} [CommRing T] [Algebra ℂ T] [Algebra ℝ T] [IsScalarTower ℝ ℂ T]

/-- The actual iterated Harris matrix coordinates commute with complex coefficient change. -/
theorem iteratedScalarMatrixEquiv_natural (f : S →ₐ[ℂ] T)
    (x : S ⊗[ℝ] (ℝ ⊗[ℚ] A)) :
    C.iteratedScalarMatrixEquiv b T
      (AlgebraInvolution.changeCoefficients (f.restrictScalars ℝ) x) =
      fun τ => ((C.iteratedScalarMatrixEquiv b S x τ).1.map f,
        (C.iteratedScalarMatrixEquiv b S x τ).2.map f) := by
  induction x using TensorProduct.inductionOn with
  | tmul s x =>
    funext τ
    apply Prod.ext <;> ext i j <;>
      simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, AlgHom.commutes]
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    funext τ
    apply Prod.ext <;> ext i j <;> simp [Matrix.map_apply]

/-- The iterated group splitting is natural in its complex coefficient algebra. -/
theorem iteratedScalarGroupSplitting_natural (f : S →ₐ[ℂ] T)
    (g : ((σ.rationalInvolution.baseChange ℝ).baseChange S).similitudes) :
    C.iteratedScalarGroupSplitting b T
      ((σ.rationalInvolution.baseChange ℝ).baseChangeMap
        (CommAlgCat.ofHom (f.restrictScalars ℝ)) g) =
      ComplexMatrix.splitGroupMap n (E →+* ℝ) f.toRingHom
        (C.iteratedScalarGroupSplitting b S g) := by
  apply Prod.ext
  · funext τ
    apply Units.ext
    exact congrArg (fun p => (p τ).1) (C.iteratedScalarMatrixEquiv_natural b f g.val.1)
  · exact Units.ext rfl

variable [Algebra ℚ S] [IsScalarTower ℚ ℝ S] [Algebra ℚ T] [IsScalarTower ℚ ℝ T]

/-- Direct Harris matrix coordinates commute with complex coefficient change. -/
theorem scalarMatrixEquiv_natural (f : S →ₐ[ℂ] T) (x : S ⊗[ℚ] A) :
    C.scalarMatrixEquiv b T
      (AlgebraInvolution.changeCoefficients ((f.restrictScalars ℝ).restrictScalars ℚ) x) =
      fun τ => ((C.scalarMatrixEquiv b S x τ).1.map f,
        (C.scalarMatrixEquiv b S x τ).2.map f) := by
  simp only [scalarMatrixEquiv, AlgEquiv.trans_apply,
    AlgebraInvolution.baseChangeTowerEquiv_naturality, iteratedScalarMatrixEquiv_natural]

/-- The actual rational Harris group splitting commutes with complex coefficient change. -/
theorem scalarGroupSplitting_natural (f : S →ₐ[ℂ] T)
    (g : (σ.rationalInvolution.baseChange S).similitudes) :
    C.scalarGroupSplitting b T
      (σ.rationalInvolution.baseChangeMap
        (CommAlgCat.ofHom ((f.restrictScalars ℝ).restrictScalars ℚ)) g) =
      ComplexMatrix.splitGroupMap n (E →+* ℝ) f.toRingHom
        (C.scalarGroupSplitting b S g) := by
  apply Prod.ext
  · funext τ
    apply Units.ext
    exact congrArg (fun p => (p τ).1) (C.scalarMatrixEquiv_natural b f g.val.1)
  · exact Units.ext rfl

end Langlands.Shimura.HarrisSignatureCharts
