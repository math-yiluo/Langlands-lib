import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement

/-! # Integral weights and the actual character kernel -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Lie

variable {R : CommRingCat.{u}} {S : CommGroupScheme (Spec R)}
    {A : Type u} [CommRing A] [Algebra R A]

/-- Integer multiples of characters evaluate as integer powers on actual points. -/
theorem characterValue_zsmul (a : characterLattice S) (n : ℤ)
    (t : AffinePoints S.toGrp A) :
    characterValue (n • a) t = characterValue a t ^ n := by
  simp only [characterValue, comp_groupHom_zsmul, map_zpow]

end Lie

namespace RelativeRoot

variable {R : CommRingCat.{u}} {S : CommGroupScheme (Spec R)}
    {A : Type u} [CommRing A] [Algebra R A]

/-- A character is trivial on points of its actual scheme-theoretic kernel. -/
theorem characterValue_kernel (a : characterLattice S)
    (c : Lie.AffinePoints (characterKernel a) A) :
    Lie.characterValue a (c ≫ (characterKernelι a).hom.hom) = 1 := by
  have h : (c ≫ (characterKernelι a).hom.hom) ≫
      (CommGroupScheme.groupHom a).hom.hom = 1 :=
    (kernelPointsEquiv (CommGroupScheme.groupHom a) _ c).property
  simp only [Lie.characterValue, h, map_one]

/-- All integral multiples, including zero, are trivial on the actual kernel. -/
theorem characterValue_zsmul_kernel (a : characterLattice S) (n : ℤ)
    (c : Lie.AffinePoints (characterKernel a) A) :
    Lie.characterValue (n • a) (c ≫ (characterKernelι a).hom.hom) = 1 := by
  rw [Lie.characterValue_zsmul, characterValue_kernel, one_zpow]

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- Vectors fixed by every character-kernel point after every change of coefficient algebra. -/
def kernelLieInvariants (i : T.toGrp ⟶ G) (a : characterLattice T) :
    Submodule k (Additive (lieKernel G k)) where
  carrier := {X | ∀ (B : Type u) [CommRing B] [Algebra k B]
    (c : Lie.AffinePoints (characterKernel a) B),
      adjoint G B (c ≫ (characterKernelι a ≫ i).hom.hom)
        (lieKernelMapLinear G (Algebra.ofId k B) X) =
      lieKernelMapLinear G (Algebra.ofId k B) X}
  zero_mem' := by
    intro B _ _ c
    simp only [map_zero]
  add_mem' := by
    intro X Y hX hY B _ _ c
    simp only [map_add, hX B c, hY B c]
  smul_mem' := by
    intro r X hX B _ _ c
    rw [LinearMap.map_smulₛₗ, LinearMap.map_smul, hX B c]

/-- Each integral character weight is fixed by the actual kernel over every test algebra. -/
theorem weightSpace_zsmul_le_kernelLieInvariants (i : T.toGrp ⟶ G)
    (a : characterLattice T) (n : ℤ) :
    weightSpace i (n • a) ≤ kernelLieInvariants i a := by
  intro X hX B _ _ c
  have h := (mem_weightSpace.mp hX) B (c ≫ (characterKernelι a).hom.hom)
  rw [characterValue_zsmul_kernel, Units.val_one, one_smul] at h
  simpa only [Grp.comp_hom_hom, Category.assoc] using h

/-- The complete integral weight span, including weight zero, is kernel invariant. -/
theorem integralWeightSpan_le_kernelLieInvariants (i : T.toGrp ⟶ G)
    (a : characterLattice T) :
    integralWeightSpan i a ≤ kernelLieInvariants i a :=
  iSup_le (weightSpace_zsmul_le_kernelLieInvariants i a)

end RelativeRoot

end Langlands.GroupScheme
