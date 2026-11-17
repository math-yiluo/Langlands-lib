import Langlands.GroupScheme.Torus.MultiplicativeTypeKernelRigidityReduction
import Langlands.GroupScheme.Torus.MultiplicativeTypeFactorizationFromKernel

/-! # The exact canonical factorization from the two rigidity inputs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The unchanged canonical-factorization proposition follows from the exact
central-rigidity and monomorphism-spreading propositions. Both are explicit inputs. -/
theorem multiplicativeTypeKernelFactorization_of_rigidity_and_spreading
    (h5 : MultiplicativeTypeCentralRigidityStatement.{u})
    (h6 : MultiplicativeTypeMonomorphismSpreadingStatement.{u}) :
    MultiplicativeTypeKernelFactorizationStatement.{u} :=
  multiplicativeTypeKernelFactorization_of_kernelCriterion
    (fun _ _ _ f hH hG hfin =>
      MultiplicativeTypeKernelReduction.isMultiplicativeType_kernel h5 h6 f hH hG hfin)

/-- Choose the actual canonical factorization, with the two exact rigidity
results as explicit inputs and no further geometric assumptions. -/
def factorizationFromRigidityAndSpreading
    (h5 : MultiplicativeTypeCentralRigidityStatement.{u})
    (h6 : MultiplicativeTypeMonomorphismSpreadingStatement.{u})
    {S : Scheme.{u}} {H G : GroupScheme S} (f : H ⟶ G)
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H)
    (hG : IsSeparated G.X.hom)
    (hfin : IsLocallyNoetherian S ∨
      (LocallyOfFinitePresentation G.X.hom ∧ QuasiCompact G.X.hom ∧
        QuasiSeparated G.X.hom)) :
    Σ (Q : GroupScheme S), Σ (q : H ⟶ Q), {v : Q ⟶ G //
      RelativeMultiplicativeType.IsMultiplicativeType Q ∧
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι f)) q ∧
      IsAffineHom q.hom.hom.left ∧ Mono v.hom.hom ∧ q ≫ v = f} :=
  factorizationOfMultiplicativeTypeKernel f hH
    (MultiplicativeTypeKernelReduction.isMultiplicativeType_kernel h5 h6 f hH hG hfin) hG

end Langlands.GroupScheme
