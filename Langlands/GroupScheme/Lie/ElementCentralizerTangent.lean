import Langlands.GroupScheme.Lie.ElementCentralizer
import Langlands.GroupScheme.Lie.RepresentationDifferential
import Langlands.GroupScheme.MatrixRepresentationDifferentialLie
import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Langlands.GroupScheme.RepresentedSubgroup

/-! # A Lie element belongs to its own actual centralizer tangent space -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open GeneralLinear.DualNumber

namespace Lie

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}
    {A : Type u} [CommRing A] [Algebra R A]

/-- Actual conjugation on the identity kernel commutes with homomorphisms. -/
theorem targetMap_conjugation (f : G ⟶ H) (g : AffinePoints G A)
    (X : lieKernel G A) :
    targetMap f A (lieKernelConjugation G g X) =
      lieKernelConjugation H (g ≫ f.hom.hom) (targetMap f A X) := by
  apply Subtype.ext
  change (constant G g * X.val * (constant G g)⁻¹) ≫ f.hom.hom =
    constant H (g ≫ f.hom.hom) * (X.val ≫ f.hom.hom) *
      (constant H (g ≫ f.hom.hom))⁻¹
  simp only [MonObj.mul_comp, GrpObj.inv_comp]
  rfl

/-- A dual-number point `1 + epsilon*M` fixes the constant lift of `M`. -/
theorem generalLinear_self_conjugation {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n A) :
    lieKernelConjugation (GeneralLinear.groupScheme n R) (pointUnit M)
      (pointKernelEquiv (M.map (TrivSqZeroExt.inlHom A A))) =
        pointKernelEquiv (M.map (TrivSqZeroExt.inlHom A A)) := by
  apply Subtype.ext
  change constant _ (pointUnit M) * pointUnit _ * (constant _ (pointUnit M))⁻¹ = _
  rw [pointUnit_conjugation, pointUnit_matrix, matrixUnit_conjugate_constant,
    sub_self, epsilonMatrix_zero, add_zero]
  rfl

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- Every actual Lie element belongs to the tangent space of its all-test
adjoint centralizer. No smoothness or semisimplicity is needed. -/
theorem mem_elementCentralizerLie_self (X : lieKernel G k) :
    Additive.ofMul X ∈ elementCentralizerLie G X := by
  change X.val ∈ (elementCentralizer G X).carrier _
  rw [mem_elementCentralizer_affine_iff]
  obtain ⟨n, ρ, hρ⟩ := affineLinearEmbeddingStatement k G inferInstance inferInstance
  have : IsClosedImmersion ρ.hom.hom.left := hρ
  have hm : Mono ρ.hom.hom := Over.mono_of_mono_left _
  apply lieKernelTarget_injective ρ (DualNumber k) hm
  rw [targetMap_conjugation]
  have hX : X.val ≫ ρ.hom.hom = pointUnit (ρ.tangentMatrix k X) :=
    (congrArg Subtype.val (ρ.pointKernelEquiv_tangentMatrix k X)).symm
  have hY : targetMap ρ (DualNumber k)
      (lieKernelMap G (Algebra.ofId k (DualNumber k)) X) =
      pointKernelEquiv ((ρ.tangentMatrix k X).map (TrivSqZeroExt.inlHom k k)) := by
    rw [← ρ.pointKernelEquiv_tangentMatrix, ρ.tangentMatrix_naturality]
    rfl
  rw [hX, hY]
  exact generalLinear_self_conjugation _

/-- The canonical lift of a Lie element into any representative of its actual
centralizer, obtained by factoring the original dual-number point. -/
def elementCentralizerTangentFactor {C : GroupScheme (Spec (CommRingCat.of k))}
    (X : lieKernel G k) (j : C ⟶ G)
    (hrep : (elementCentralizer G X).IsRepresentedBy j) : lieKernel C k := by
  have hX := mem_elementCentralizerLie_self X
  let y := (hrep.pointsEquiv _).symm ⟨X.val, hX⟩
  have hy : y ≫ j.hom.hom = X.val := hrep.pointsEquiv_symm_comp _
  have : Mono j.hom.hom := hrep.1
  refine ⟨y, mem_lieKernel_of_comp j y ?_⟩
  rw [hy]
  exact X.property

@[simp]
theorem targetMap_elementCentralizerTangentFactor
    {C : GroupScheme (Spec (CommRingCat.of k))}
    (X : lieKernel G k) (j : C ⟶ G)
    (hrep : (elementCentralizer G X).IsRepresentedBy j) :
    targetMap j k (elementCentralizerTangentFactor X j hrep) = X := by
  apply Subtype.ext
  exact hrep.pointsEquiv_symm_comp _

end Lie

end Langlands.GroupScheme
