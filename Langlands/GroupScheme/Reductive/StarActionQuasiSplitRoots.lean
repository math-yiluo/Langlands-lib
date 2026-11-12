import Langlands.GroupScheme.Absolute.RegularCocharacterMaximal
import Langlands.GroupScheme.Dynamic.LieProof

/-! # Roots of a split torus in a represented regular dynamic parabolic -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace StarActionQuasiSplit

variable {k : Type u} [Field k] {G B : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom B.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Along a monomorphism `b`, a Lie vector of `B` is a weight vector for `t` as soon as its image
is a weight vector for `t ≫ b`. -/
theorem mem_weightSpace_of_targetMapLinear (b : B ⟶ G) [Mono b.hom.hom] (t : T.toGrp ⟶ B)
    {χ : characterLattice T} {Y : Additive (lieKernel B k)}
    (hY : Lie.targetMapLinear b k Y ∈ weightSpace (t ≫ b) χ) : Y ∈ weightSpace t χ := by
  intro A _ _ s
  apply Lie.targetMapLinear_injective b A
  have key := hY A s
  rw [Grp.comp_hom_hom, ← Category.assoc] at key
  rw [LinearMap.map_smul, ← adjoint_comp_targetMapLinear, ← lieKernelMapLinear_targetMapLinear]
  exact key

variable [LocallyOfFiniteType G.X.hom]

/-- Let `b : B ⟶ G` represent the dynamic parabolic of a regular cocharacter `ν` of a split
torus `t : T ⟶ B`. Then the roots of `T` in `B` are exactly the roots of `T` in `G` that are
positive on `ν`. -/
theorem mem_roots_iff_of_isRepresentedBy_parabolic (hT : IsSplitTorus T.toGrp)
    (b : B ⟶ G) (t : T.toGrp ⟶ B) (ν : cocharacterLattice T)
    (hrep : (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ (t ≫ b))).IsRepresentedBy b)
    (hν : IsRegularCocharacter (t ≫ b) ν) (α : characterLattice T) :
    α ∈ roots t ↔ α ∈ roots (t ≫ b) ∧ 0 < latticePairing T α ν := by
  have : Mono b.hom.hom := hrep.1
  constructor
  · rintro ⟨hα0, hαne⟩
    obtain ⟨Y, hY, hY0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hαne
    have hX := targetMapLinear_mem_weightSpace t b hY
    have hX0 : Lie.targetMapLinear b k Y ≠ 0 := by
      intro h
      apply hY0
      apply Lie.targetMapLinear_injective b k
      rw [h, map_zero]
    have hroot : α ∈ roots (t ≫ b) := by
      refine ⟨hα0, fun hbot => hX0 ?_⟩
      rw [hbot] at hX
      exact (Submodule.mem_bot _).1 hX
    refine ⟨hroot, ?_⟩
    have hP : (Lie.targetMapLinear b k Y).toMul.val ∈
        (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ (t ≫ b))).carrier _ := by
      rw [← hrep.2]
      exact SubgroupFunctor.mem_range.2 ⟨Y.toMul.val, rfl⟩
    rw [(dynamicLie k G _ (Lie.targetMapLinear b k Y).toMul).2.1,
      iSup_nat_weightSpace_cocharacter_eq_nonnegativeWeightSpan hT] at hP
    by_contra hneg
    have hle : ¬ (0 ≤ latticePairing T α ν) := by
      intro h0
      exact hneg (lt_of_le_of_ne h0 (hν α hroot).symm)
    have hdisj := weightSpace_disjoint_iSup hT (t ≫ b)
      (p := fun χ => 0 ≤ latticePairing T χ ν) hle
    exact hX0 ((Submodule.disjoint_def.1 hdisj) _ hX hP)
  · rintro ⟨hroot, hpos⟩
    refine ⟨hroot.1, ?_⟩
    obtain ⟨X, hX, hX0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hroot.2
    have hXn : X ∈ nonnegativeWeightSpan (t ≫ b) ν := by
      rw [nonnegativeWeightSpan_def]
      exact (le_iSup₂ (f := fun χ (_ : 0 ≤ latticePairing T χ ν) => weightSpace (t ≫ b) χ)
        α hpos.le) hX
    obtain ⟨Z, hZ⟩ :=
      exists_lieKernel_of_mem_nonnegativeWeightSpan dynamicLie hT (t ≫ b) ν b hrep X hXn
    have hZX : Lie.targetMapLinear b k (Additive.ofMul Z) = X := by
      apply Additive.toMul.injective
      apply Subtype.ext
      exact hZ
    have hZw : Additive.ofMul Z ∈ weightSpace t α :=
      mem_weightSpace_of_targetMapLinear b t (by rw [hZX]; exact hX)
    intro hbot
    rw [hbot] at hZw
    apply hX0
    rw [← hZX, (Submodule.mem_bot _).1 hZw, map_zero]

/-- The same statement for a supplied composite `j = t ≫ b`. -/
theorem mem_roots_iff_of_isRepresentedBy_parabolic_of_comp (hT : IsSplitTorus T.toGrp)
    (b : B ⟶ G) (t : T.toGrp ⟶ B) (j : T.toGrp ⟶ G) (hcomp : t ≫ b = j)
    (ν : cocharacterLattice T)
    (hrep : (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j)).IsRepresentedBy b)
    (hν : IsRegularCocharacter j ν) (α : characterLattice T) :
    α ∈ roots t ↔ α ∈ roots j ∧ 0 < latticePairing T α ν := by
  subst hcomp
  exact mem_roots_iff_of_isRepresentedBy_parabolic hT b t ν hrep hν α

end StarActionQuasiSplit

end Langlands.GroupScheme
