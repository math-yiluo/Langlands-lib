import Langlands.GroupScheme.AffineCartierSmoothStatement
import Langlands.GroupScheme.MatrixRepresentation.NormalKernel
import Langlands.GroupScheme.MatrixRepresentation.FrobeniusNormalKernel
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # Exact normal kernels conditional on Cartier smoothness -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k] [IsAlgClosed k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- Cartier smoothness supplies the characteristic-zero branch of the exact
normal-kernel construction; positive characteristic uses Frobenius coordinates. -/
theorem nonempty_kernelRepresentation_with_cartier
    (hCartier : AffineCartierSmoothStatement.{u})
    (i : H ⟶ G) (hc : IsClosedSubgroup i)
    (hN : (SubgroupFunctor.range i).IsNormal) : Nonempty (KernelRepresentation i) := by
  rcases CharP.exists' k with hzero | ⟨p, hp, hchar⟩
  · have : CharZero k := hzero
    have : Smooth G.X.hom := hCartier k G inferInstance inferInstance
    have : IsReduced G.X.left :=
      Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
        k G.X.left G.X.hom
    exact nonempty_kernelRepresentation_of_normal_closed i hc hN
  · have : Fact p.Prime := hp
    have : CharP k p := hchar
    exact nonempty_kernelRepresentation_of_prime_expChar p hp.out i hc hN

/-- Choose an actual exact-kernel representation over an algebraically closed
field of arbitrary characteristic, conditional on the Cartier proposition. -/
def normalKernelRepresentationWithCartier
    (hCartier : AffineCartierSmoothStatement.{u})
    (i : H ⟶ G) (hc : IsClosedSubgroup i)
    (hN : (SubgroupFunctor.range i).IsNormal) : KernelRepresentation i :=
  Classical.choice (nonempty_kernelRepresentation_with_cartier hCartier i hc hN)

/-- Conditional arbitrary-characteristic exact kernels on all relative tests. -/
theorem exists_normal_kernel_with_cartier
    (hCartier : AffineCartierSmoothStatement.{u})
    (i : H ⟶ G) (hc : IsClosedSubgroup i)
    (hN : (SubgroupFunctor.range i).IsNormal) :
    ∃ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)),
      SubgroupFunctor.range (kernelι ρ) = SubgroupFunctor.range i := by
  let D := normalKernelRepresentationWithCartier hCartier i hc hN
  exact ⟨D.dimension, D.representation, D.kernel_range⟩

end Langlands.GroupScheme.MatrixRepresentation
