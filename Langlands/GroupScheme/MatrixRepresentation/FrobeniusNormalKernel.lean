import Langlands.GroupScheme.MatrixRepresentation.FrobeniusNormalCharacter

/-! # Exact normal kernels in positive characteristic -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k] [IsAlgClosed k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- A normal closed subgroup of an affine finite-type group over an algebraically
closed field of positive characteristic is an exact represented kernel.
Neither the ambient group nor the subgroup is assumed reduced or smooth. -/
theorem nonempty_kernelRepresentation_of_prime_expChar
    (p : ℕ) [ExpChar k p] (hp : p.Prime)
    (i : H ⟶ G) (hc : IsClosedSubgroup i)
    (hN : (SubgroupFunctor.range i).IsNormal) : Nonempty (KernelRepresentation i) := by
  have : IsClosedImmersion i.hom.hom.left := hc
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : IsAffineHom H.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  exact nonempty_kernelRepresentation_of_normal_closed_inverse_multiples i hc hN
    (hasInverseMultipleNormalCharacters_of_prime_expChar p hp i hN)

/-- Choose an actual finite-dimensional representation with the prescribed
normal closed subgroup as its full scheme-theoretic kernel. -/
def normalKernelRepresentationOfPrimeExpChar
    (p : ℕ) [ExpChar k p] (hp : p.Prime)
    (i : H ⟶ G) (hc : IsClosedSubgroup i)
    (hN : (SubgroupFunctor.range i).IsNormal) : KernelRepresentation i :=
  Classical.choice (nonempty_kernelRepresentation_of_prime_expChar p hp i hc hN)

/-- The positive-characteristic normal-kernel theorem in existential form,
with equality of subgroup functors on every relative scheme test. -/
theorem exists_normal_kernel_of_prime_expChar
    (p : ℕ) [ExpChar k p] (hp : p.Prime)
    (i : H ⟶ G) (hc : IsClosedSubgroup i)
    (hN : (SubgroupFunctor.range i).IsNormal) :
    ∃ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)),
      SubgroupFunctor.range (kernelι ρ) = SubgroupFunctor.range i := by
  let D := normalKernelRepresentationOfPrimeExpChar p hp i hc hN
  exact ⟨D.dimension, D.representation, D.kernel_range⟩

end Langlands.GroupScheme.MatrixRepresentation
