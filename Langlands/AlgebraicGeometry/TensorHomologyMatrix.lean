import Langlands.AlgebraicGeometry.TensorSectionsHomology
import Langlands.AlgebraicGeometry.TensorLinearKernel
import Langlands.AlgebraicGeometry.FiniteLinearModels
import Mathlib.Algebra.Category.ModuleCat.Kernels

/-! # Finite matrix coordinates for connective tensor homology -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.TensorSections

variable {R : CommRingCat.{u}}

/-- The actual cycles identify with the linear kernel of the outgoing differential. -/
def cyclesLinearKernelIso (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    K.cycles 0 ≅ ModuleCat.of R (K.d 0 1).hom.ker :=
  IsLimit.conePointUniqueUpToIso
    (K.cyclesIsKernel 0 1 ((ComplexShape.up ℤ).next_eq' (by decide)))
    (ModuleCat.kernelIsLimit (K.d 0 1))

@[reassoc (attr := simp)]
lemma cyclesLinearKernelIso_hom_subtype (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (cyclesLinearKernelIso K).hom ≫ ModuleCat.ofHom (K.d 0 1).hom.ker.subtype =
      K.iCycles 0 :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

/-- If the incoming differential is zero, degree-zero homology is its actual cycles. -/
def homologyZeroCyclesIso (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (h : K.d (-1) 0 = 0) : K.homology 0 ≅ K.cycles 0 :=
  ((K.sc 0).asIsoHomologyπ (by
    change K.d ((ComplexShape.up ℤ).prev 0) 0 = 0
    rw [(ComplexShape.up ℤ).prev_eq' (show (ComplexShape.up ℤ).Rel (-1) 0 by decide)]
    exact h)).symm

@[reassoc (attr := simp)]
lemma homologyπ_homologyZeroCyclesIso (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (h : K.d (-1) 0 = 0) :
    K.homologyπ 0 ≫ (homologyZeroCyclesIso K h).hom = 𝟙 _ :=
  (homologyZeroCyclesIso K h).inv_hom_id

/-- Degree-zero homology with zero incoming differential is the concrete linear kernel. -/
def homologyZeroLinearKernelIso (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (h : K.d (-1) 0 = 0) :
    K.homology 0 ≅ ModuleCat.of R (K.d 0 1).hom.ker :=
  homologyZeroCyclesIso K h ≪≫ cyclesLinearKernelIso K

@[reassoc (attr := simp)]
lemma homologyπ_homologyZeroLinearKernelIso_subtype
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (h : K.d (-1) 0 = 0) :
    K.homologyπ 0 ≫ (homologyZeroLinearKernelIso K h).hom ≫
      ModuleCat.ofHom (K.d 0 1).hom.ker.subtype = K.iCycles 0 := by
  simp [homologyZeroLinearKernelIso]

/-- The concrete representative of a homology class commutes with every complex map. -/
lemma homologyZeroLinearKernelIso_naturality
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (φ : K ⟶ L)
    (hK : K.d (-1) 0 = 0) (hL : L.d (-1) 0 = 0) :
    HomologicalComplex.homologyMap φ 0 ≫ (homologyZeroLinearKernelIso L hL).hom ≫
      ModuleCat.ofHom (L.d 0 1).hom.ker.subtype =
    (homologyZeroLinearKernelIso K hK).hom ≫
      ModuleCat.ofHom (K.d 0 1).hom.ker.subtype ≫ φ.f 0 := by
  rw [← cancel_epi (K.homologyπ 0)]
  simp only [HomologicalComplex.homologyπ_naturality_assoc,
    homologyπ_homologyZeroLinearKernelIso_subtype,
    homologyπ_homologyZeroLinearKernelIso_subtype_assoc,
    HomologicalComplex.cyclesMap_i]

/-- Tensoring preserves the condition that the incoming differential is zero. -/
lemma tensorComplex_d_neg_one_zero (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (h : K.d (-1) 0 = 0) (A : ModuleCat.{u} R) :
    ((tensorComplex K).obj A).d (-1) 0 = 0 := by
  change ModuleCat.ofHom (TensorProduct.map (LinearMap.id : A →ₗ[R] A)
    (K.d (-1) 0).hom) = 0
  rw [h]
  ext x p
  simp

/-- Tensor homology is the actual kernel of the tensored degree-zero differential. -/
def tensorHomologyZeroKernelEquiv (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (h : K.d (-1) 0 = 0) (A : ModuleCat.{u} R) :
    ((tensorComplex K).obj A).homology 0 ≃
      (TensorProduct.map (LinearMap.id : A →ₗ[R] A) (K.d 0 1).hom).ker :=
  (homologyZeroLinearKernelIso ((tensorComplex K).obj A)
    (tensorComplex_d_neg_one_zero K h A)).toLinearEquiv.toEquiv

/-- The tensor kernel identification retains every coefficient-linear transition map. -/
lemma tensorHomologyZeroKernelEquiv_naturality
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (h : K.d (-1) 0 = 0)
    {A B : ModuleCat.{u} R} (q : A ⟶ B)
    (z : ((tensorComplex K).obj A).homology 0) :
    tensorHomologyZeroKernelEquiv K h B
      (HomologicalComplex.homologyMap ((tensorComplex K).map q) 0 z) =
    FiniteLinearEquations.TensorKernel.mapKernel (K.d 0 1).hom q.hom
      (tensorHomologyZeroKernelEquiv K h A z) := by
  apply Subtype.ext
  exact ConcreteCategory.congr_hom
    (homologyZeroLinearKernelIso_naturality ((tensorComplex K).map q)
      (tensorComplex_d_neg_one_zero K h A) (tensorComplex_d_neg_one_zero K h B)) z

variable {m n : ℕ}

/-- Finite coordinates turn tensor homology into solutions of the actual differential matrix. -/
def tensorHomologySolutionsEquiv (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (h : K.d (-1) 0 = 0)
    (e₀ : K.X 0 ≃ₗ[R] (Fin n → R)) (e₁ : K.X 1 ≃ₗ[R] (Fin m → R))
    (S : Type u) [CommRing S] [Algebra R S] :
    ((tensorComplex K).obj (ModuleCat.of R S)).homology 0 ≃
      FiniteLinearEquations.Solutions
        (FiniteLinearEquations.TensorKernel.matrix (K.d 0 1).hom e₀ e₁) S :=
  (tensorHomologyZeroKernelEquiv K h (ModuleCat.of R S)).trans
    (FiniteLinearEquations.TensorKernel.kernelEquiv (K.d 0 1).hom e₀ e₁ S)

/-- All coefficient-algebra maps act by the same coordinate restrictions. -/
lemma tensorHomologySolutionsEquiv_naturality
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (h : K.d (-1) 0 = 0)
    (e₀ : K.X 0 ≃ₗ[R] (Fin n → R)) (e₁ : K.X 1 ≃ₗ[R] (Fin m → R))
    {S S' : Type u} [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']
    (q : S →ₐ[R] S')
    (z : ((tensorComplex K).obj (ModuleCat.of R S)).homology 0) :
    tensorHomologySolutionsEquiv K h e₀ e₁ S'
      (HomologicalComplex.homologyMap
        ((tensorComplex K).map (ModuleCat.ofHom q.toLinearMap)) 0 z) =
    FiniteLinearEquations.mapSolutions
      (FiniteLinearEquations.TensorKernel.matrix (K.d 0 1).hom e₀ e₁) q
      (tensorHomologySolutionsEquiv K h e₀ e₁ S z) := by
  change FiniteLinearEquations.TensorKernel.kernelEquiv (K.d 0 1).hom e₀ e₁ S'
    (tensorHomologyZeroKernelEquiv K h (ModuleCat.of R S') _) = _
  rw [tensorHomologyZeroKernelEquiv_naturality]
  exact FiniteLinearEquations.TensorKernel.kernelEquiv_naturality
    (K.d 0 1).hom e₀ e₁ q _

attribute [local instance] FiniteLinearEquations.sectionsAlgebra

/-- The matrix comparison is natural on the entire scheme slice, with the same value lift. -/
def homologyZeroSolutionsPresheafIso (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (h : K.d (-1) 0 = 0)
    (e₀ : K.X 0 ≃ₗ[R] (Fin n → R)) (e₁ : K.X 1 ≃ₗ[R] (Fin m → R)) :
    homologyPresheaf K 0 ≅ FiniteLinearEquations.solutionsPresheaf
      (FiniteLinearEquations.TensorKernel.matrix (K.d 0 1).hom e₀ e₁) :=
  NatIso.ofComponents
    (fun T ↦ (Equiv.ulift.trans
      ((tensorHomologySolutionsEquiv K h e₀ e₁ Γ(T.unop.left, ⊤)).trans
        Equiv.ulift.symm)).toIso)
    (by
      intro T U q
      ext x
      apply ULift.ext
      exact tensorHomologySolutionsEquiv_naturality K h e₀ e₁
        (FiniteLinearEquations.pullSections q.unop) x.down)

/-- The explicit matrix is a finite linear model for connective tensor homology. -/
lemma homologyZero_hasModel (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (h : K.d (-1) 0 = 0)
    (e₀ : K.X 0 ≃ₗ[R] (Fin n → R)) (e₁ : K.X 1 ≃ₗ[R] (Fin m → R)) :
    FiniteLinearEquations.HasModel (homologyPresheaf K 0) :=
  ⟨m, n, FiniteLinearEquations.TensorKernel.matrix (K.d 0 1).hom e₀ e₁,
    ⟨homologyZeroSolutionsPresheafIso K h e₀ e₁⟩⟩

end Langlands.AlgebraicGeometry.TensorSections
