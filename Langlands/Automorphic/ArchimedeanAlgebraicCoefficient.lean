import Langlands.Automorphic.RegularAlgebraic
import Langlands.Automorphic.TensorLieAction
import Langlands.GroupScheme.MatrixRepresentationProductDifferentialModule

/-! # Algebraic coefficients on the actual archimedean group and Lie algebra -/

noncomputable section

universe uF

open scoped Classical TensorProduct Matrix

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Langlands.Global.ArchimedeanGL

attribute [local instance 100] LieRing.ofAssociativeRing

variable (F : Type uF) [Field F] (n : ℕ)
variable {I : Type} (e : I → EmbeddingIndex F)

/-- A small finite index can enumerate every embedding even when the field is in a higher universe. -/
def fullEmbeddingEnumeration [NumberField F] :
    Fin (Fintype.card (EmbeddingIndex F)) ≃ EmbeddingIndex F :=
  (Fintype.equivFin (EmbeddingIndex F)).symm

/-- All selected embedding coordinates, including either orientation of a complex place. -/
def embeddingMatrixHom :
    ArchimedeanMatrix F n →ₐ[ℝ] (I → Matrix (Fin n) (Fin n) ℂ) :=
  AlgHom.pi (fun i => (embeddingComponent F (e i)).mapMatrix)

@[simp]
theorem embeddingMatrixHom_apply (X : ArchimedeanMatrix F n) (i : I) (a b : Fin n) :
    embeddingMatrixHom F n e X i a b = embeddingComponent F (e i) (X a b) := rfl

/-- The full completion-based group maps to the genuine family of complex GL groups. -/
def embeddingGL : InfiniteAdelicGL F n →* (I → GL (Fin n) ℂ) :=
  MonoidHom.pi (fun i =>
    (Units.map ((embeddingComponent F (e i)).mapMatrix).toMonoidHom).comp
      (archimedeanGLCoordinates F n).toMonoidHom)

@[simp]
theorem embeddingGL_val (g : InfiniteAdelicGL F n) (i : I) :
    (embeddingGL F n e g i : Matrix (Fin n) (Fin n) ℂ) =
      embeddingMatrixHom F n e (archimedeanGLCoordinates F n g).val i := rfl

@[simp]
theorem embeddingGL_entry (g : InfiniteAdelicGL F n) (i : I) (a b : Fin n) :
    (embeddingGL F n e g i : Matrix (Fin n) (Fin n) ℂ) a b =
      embeddingComponent F (e i) ((archimedeanGLCoordinates F n g).val a b) := rfl

/-- The same embedding coordinates preserve the real matrix commutator. -/
def embeddingRealLieHom :
    RealLieAlgebra F n →ₗ⁅ℝ⁆ (I → Matrix (Fin n) (Fin n) ℂ) :=
  { (embeddingMatrixHom F n e).toLinearMap.comp
      (realLieAlgebraToMatrix F n).toLinearMap with
    map_lie' := by
      intro X Y
      change embeddingMatrixHom F n e
        (realLieAlgebraToMatrix F n ⁅X, Y⁆) = _
      rw [realLieAlgebraToMatrix_lie, map_sub, map_mul, map_mul]
      rfl }

/-- Complex-linear extension of every selected real embedding coordinate. -/
def embeddingComplexLieLinear :
    ComplexLieAlgebra F n →ₗ[ℂ] (I → Matrix (Fin n) (Fin n) ℂ) :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton ℂ _ (embeddingRealLieHom F n e).toLinearMap)

@[simp]
theorem embeddingComplexLieLinear_tmul (z : ℂ) (X : RealLieAlgebra F n) :
    embeddingComplexLieLinear F n e (z ⊗ₜ[ℝ] X) =
      z • embeddingRealLieHom F n e X := rfl

/-- Scalar extension retains the actual Lie bracket, with no supplied differential. -/
def embeddingComplexLieHom :
    ComplexLieAlgebra F n →ₗ⁅ℂ⁆ (I → Matrix (Fin n) (Fin n) ℂ) :=
  { embeddingComplexLieLinear F n e with
    map_lie' := by
      intro X Y
      change embeddingComplexLieLinear F n e ⁅X, Y⁆ =
        ⁅embeddingComplexLieLinear F n e X, embeddingComplexLieLinear F n e Y⁆
      induction X using TensorProduct.inductionOn with
      | tmul z X =>
          induction Y using TensorProduct.inductionOn with
          | tmul w Y =>
              simp only [complexLieAlgebra_lie_tmul, embeddingComplexLieLinear_tmul,
                (embeddingRealLieHom F n e).map_lie, smul_lie, lie_smul, smul_smul,
                mul_comm]
          | add Y Z hY hZ =>
              simp only [LieRing.lie_add, map_add, hY, hZ]
      | add X Z hX hZ =>
          simp only [add_lie, map_add, hX, hZ] }

@[simp]
theorem embeddingComplexLieHom_tmul (z : ℂ) (X : RealLieAlgebra F n) :
    embeddingComplexLieHom F n e (z ⊗ₜ[ℝ] X) =
      z • embeddingRealLieHom F n e X := rfl

@[simp]
theorem embeddingComplexLieHom_tmul_entry (z : ℂ) (X : RealLieAlgebra F n)
    (i : I) (a b : Fin n) :
    embeddingComplexLieHom F n e (z ⊗ₜ[ℝ] X) i a b =
      z * embeddingComponent F (e i) (realLieAlgebraToMatrix F n X a b) := rfl

theorem embeddingRealLieHom_conjugation (g : InfiniteAdelicGL F n)
    (X : RealLieAlgebra F n) :
    embeddingRealLieHom F n e (realLieConjugation F n g X) =
      fun i => (embeddingGL F n e g i : Matrix (Fin n) (Fin n) ℂ) *
        embeddingRealLieHom F n e X i *
        (((embeddingGL F n e g i)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := by
  change embeddingMatrixHom F n e
    (realLieAlgebraToMatrix F n (realLieConjugation F n g X)) = _
  rw [realLieAlgebraToMatrix_realLieConjugation, map_mul, map_mul]
  funext i
  change _ = _ * _ * ((embeddingGL F n e g)⁻¹ i : Matrix (Fin n) (Fin n) ℂ)
  rw [← map_inv]
  rfl

/-- The embedding complexification intertwines conjugation by the entire actual group. -/
theorem embeddingComplexLieHom_conjugation (g : InfiniteAdelicGL F n)
    (X : ComplexLieAlgebra F n) :
    embeddingComplexLieHom F n e (complexLieConjugation F n g X) =
      fun i => (embeddingGL F n e g i : Matrix (Fin n) (Fin n) ℂ) *
        embeddingComplexLieHom F n e X i *
        (((embeddingGL F n e g i)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := by
  induction X using TensorProduct.inductionOn with
  | tmul z X =>
      simp only [complexLieConjugation_tmul, embeddingComplexLieHom_tmul,
        embeddingRealLieHom_conjugation]
      funext i
      simp only [Pi.smul_apply, mul_smul_comm, smul_mul_assoc]
  | add X Y hX hY =>
      simp only [map_add, hX, hY, Pi.add_apply, mul_add, add_mul]
      rfl

end Langlands.Global.ArchimedeanGL

namespace Langlands.Automorphic.ArchimedeanAlgebraicCoefficient

open Langlands.Global Langlands.Global.ArchimedeanGL
open Langlands.GroupScheme

attribute [local instance 100] LieRing.ofAssociativeRing

variable {F : Type uF} [Field F] {n : ℕ}
variable {I : Type} [Finite I] (e : I → EmbeddingIndex F)
variable {m : Type} [Fintype m] [DecidableEq m]
variable (ρ : MatrixRepresentation
  (GeneralLinearProductDualNumber.groupScheme (fun _ : I => Fin n)
    (CommRingCat.of ℂ)) m)

/-- The full coefficient module, tagged by its actual embeddings and scheme representation. -/
@[nolint unusedArguments]
def Space (_e : I → EmbeddingIndex F) (_ρ : MatrixRepresentation
    (GeneralLinearProductDualNumber.groupScheme (fun _ : I => Fin n)
      (CommRingCat.of ℂ)) m) := m → ℂ

instance : AddCommGroup (Space e ρ) := inferInstanceAs (AddCommGroup (m → ℂ))
instance : Module ℂ (Space e ρ) := inferInstanceAs (Module ℂ (m → ℂ))
instance : Module.Free ℂ (Space e ρ) := inferInstanceAs (Module.Free ℂ (m → ℂ))
instance : Module.Finite ℂ (Space e ρ) := inferInstanceAs (Module.Finite ℂ (m → ℂ))

/-- Every coordinate vector is retained. -/
def coordinates : Space e ρ ≃ₗ[ℂ] (m → ℂ) := LinearEquiv.refl ℂ _

/-- Pull back the actual algebraic differential along all selected complexified embeddings. -/
def lieAction : ComplexLieAlgebra F n →ₗ⁅ℂ⁆ Module.End ℂ (Space e ρ) :=
  (ρ.productDifferentialLieAction ℂ).comp (embeddingComplexLieHom F n e)

instance : LieRingModule (ComplexLieAlgebra F n) (Space e ρ) :=
  LieRingModule.compLieHom (L₂ := Module.End ℂ (Space e ρ))
    (Space e ρ) (lieAction e ρ)

instance : LieModule ℂ (ComplexLieAlgebra F n) (Space e ρ) where
  smul_lie z X v := by
    change lieAction e ρ (z • X) v = z • lieAction e ρ X v
    rw [map_smul]
    rfl
  lie_smul z X v := by
    change lieAction e ρ X (z • v) = z • lieAction e ρ X v
    exact map_smul (lieAction e ρ X) z v

@[simp]
theorem coordinates_lie (X : ComplexLieAlgebra F n) (v : Space e ρ) :
    coordinates e ρ ⁅X, v⁆ =
      ρ.productDifferential ℂ (embeddingComplexLieHom F n e X) *ᵥ coordinates e ρ v := rfl

@[simp]
theorem coordinates_lie_tmul (z : ℂ) (X : RealLieAlgebra F n) (v : Space e ρ) :
    coordinates e ρ ⁅z ⊗ₜ[ℝ] X, v⁆ =
      z • (ρ.productDifferential ℂ (embeddingRealLieHom F n e X) *ᵥ coordinates e ρ v) := by
  rw [coordinates_lie, embeddingComplexLieHom_tmul, map_smul, Matrix.smul_mulVec]

/-- Restriction to the actual complement of the real split central directions. -/
def reducedLieAction : ReducedComplexLieAlgebra F n →ₗ⁅ℂ⁆ Module.End ℂ (Space e ρ) :=
  (lieAction e ρ).comp (reducedComplexInclusion F n)

/-- Restriction to the actual complexified compact Lie algebra. -/
def compactLieAction : CompactComplexLieAlgebra F n →ₗ⁅ℂ⁆ Module.End ℂ (Space e ρ) :=
  (lieAction e ρ).comp (compactComplexInclusion F n)

theorem reducedLieAction_compact (X : CompactComplexLieAlgebra F n) :
    reducedLieAction e ρ (compactToReducedComplex F n X) = compactLieAction e ρ X := by
  change lieAction e ρ (reducedComplexInclusion F n (compactToReducedComplex F n X)) = _
  rw [reducedComplexInclusion_compact]
  rfl

/-- Actual scheme points give the representation of the full archimedean group. -/
def representation : Representation ℂ (InfiniteAdelicGL F n) (Space e ρ) :=
  (ρ.productDifferentialModuleRepresentation ℂ).comp (embeddingGL F n e)

@[simp]
theorem coordinates_representation (g : InfiniteAdelicGL F n) (v : Space e ρ) :
    coordinates e ρ (representation e ρ g v) =
      (ρ.productMatrixPointsHom ℂ (embeddingGL F n e g) : Matrix m m ℂ) *ᵥ
        coordinates e ρ v := rfl

/-- Full-group covariance is derived from the original algebraic representation. -/
theorem representation_lie (g : InfiniteAdelicGL F n)
    (X : ComplexLieAlgebra F n) (v : Space e ρ) :
    representation e ρ g ⁅X, v⁆ =
      ⁅complexLieConjugation F n g X, representation e ρ g v⁆ := by
  apply (coordinates e ρ).injective
  simp only [coordinates_representation, coordinates_lie]
  rw [embeddingComplexLieHom_conjugation, ρ.productDifferential_conjugate]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

/-- Restrict the same genuine point representation to the full standard compact subgroup. -/
def compactRepresentation : Representation ℂ (standardInfiniteCompact F n) (Space e ρ) :=
  (representation e ρ).comp (standardInfiniteCompact F n).subtype

@[simp]
theorem compactRepresentation_apply (k : standardInfiniteCompact F n) (v : Space e ρ) :
    compactRepresentation e ρ k v = representation e ρ k.val v := rfl

theorem compactRepresentation_lie (k : standardInfiniteCompact F n)
    (X : ComplexLieAlgebra F n) (v : Space e ρ) :
    compactRepresentation e ρ k ⁅X, v⁆ =
      ⁅complexLieConjugation F n k.val X, compactRepresentation e ρ k v⁆ :=
  representation_lie e ρ k.val X v

section AutomorphicTensor

variable [NumberField F]

local instance coefficientRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance coefficientContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance coefficientSmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance coefficientFormsAddCommGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance coefficientStableAddCommGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance coefficientSpaceAddCommGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

/-- Actual automorphic tensors now have compact covariance without a supplied coefficient law. -/
theorem tensorCompactRepresentation_lie (S : OperatorRealization F n)
    (k : standardInfiniteCompact F n) (X : ComplexLieAlgebra F n)
    (t : S.Space ⊗[ℂ] Space e ρ) :
    S.tensorCompactRepresentation (compactRepresentation e ρ) k
        (S.tensorComplexLieAction (Space e ρ) X t) =
      S.tensorComplexLieAction (Space e ρ) (complexLieConjugation F n k.val X)
        (S.tensorCompactRepresentation (compactRepresentation e ρ) k t) :=
  S.tensorCompactRepresentation_complexLieAction (Space e ρ)
    (compactRepresentation e ρ) (compactRepresentation_lie e ρ) k X t

end AutomorphicTensor

end Langlands.Automorphic.ArchimedeanAlgebraicCoefficient
