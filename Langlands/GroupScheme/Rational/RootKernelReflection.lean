import Langlands.GroupScheme.Rational.RootKernelDivisibility
import Langlands.GroupScheme.Rational.IntegralCoroot

/-! # Integral reflections from full-kernel-centralizing representatives -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]

/-- A root-flipping normalizer centralizing the full character kernel has a
unique actual integral coroot. The normalizing point remains an input. -/
theorem IsSplitTorus.existsUnique_coroot_of_mem_kernelCentralizer
    (hT : IsSplitTorus T.toGrp) (a : characterLattice T) (ha : a ≠ 0)
    (n : normalizerPoints i) (hflip : weylAction i n a = -a)
    (hc : n.val ∈ (RelativeRoot.kernelCentralizer i a).carrier (Over.mk (𝟙 _))) :
    ∃! ν : cocharacterLattice T,
      latticePairing T a ν = 2 ∧
        ∀ χ : characterLattice T,
          weylAction i n χ = χ - latticePairing T χ ν • a := by
  exact hT.existsUnique_coroot_of_integral_difference a ha
    (weylAction i n).toLinearMap hflip
    (exists_integral_difference_of_mem_kernelCentralizer i hT a ha n hc)

variable [IsAffineHom G.X.hom]

/-- Assemble actual reflection data from a supplied family of root-flipping
normalizers that centralize the full root kernels. -/
def RelativeRootReflectionData.ofKernelCentralizingRepresentatives
    (hT : IsSplitTorus T.toGrp)
    (n : relativeRoots i → normalizerPoints i)
    (hflip : ∀ a, weylAction i (n a) a.val = -a.val)
    (hc : ∀ a, (n a).val ∈
      (RelativeRoot.kernelCentralizer i a.val).carrier (Over.mk (𝟙 _))) :
    RelativeRootReflectionData i where
  coroot a := Classical.choose
    (hT.existsUnique_coroot_of_mem_kernelCentralizer i a.val a.property.1
      (n a) (hflip a) (hc a))
  representative := n
  pair_self a := (Classical.choose_spec
    (hT.existsUnique_coroot_of_mem_kernelCentralizer i a.val a.property.1
      (n a) (hflip a) (hc a))).1.1
  action a := (Classical.choose_spec
    (hT.existsUnique_coroot_of_mem_kernelCentralizer i a.val a.property.1
      (n a) (hflip a) (hc a))).1.2

/-- Intrinsic normalizer existence is the remaining input to this assembly
theorem. No integral-difference or cocharacter premise is needed. -/
theorem exists_reflectionData_of_kernelCentralizing_representatives
    (hT : IsSplitTorus T.toGrp)
    (hn : ∀ a : relativeRoots i, ∃ n : normalizerPoints i,
      weylAction i n a.val = -a.val ∧
        n.val ∈ (RelativeRoot.kernelCentralizer i a.val).carrier (Over.mk (𝟙 _))) :
    ∃ D : RelativeRootReflectionData i, ∀ a : relativeRoots i,
      (D.representative a).val ∈
        (RelativeRoot.kernelCentralizer i a.val).carrier (Over.mk (𝟙 _)) := by
  choose n hflip hc using hn
  exact ⟨RelativeRootReflectionData.ofKernelCentralizingRepresentatives i hT n hflip hc,
    hc⟩

end Langlands.GroupScheme
