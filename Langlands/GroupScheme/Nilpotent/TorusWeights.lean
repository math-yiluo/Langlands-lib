import Langlands.GroupScheme.Nilpotent.Adjoint
import Langlands.GroupScheme.Torus.WeightDecomposition
import Langlands.GroupScheme.Lie.TorusCentralizer
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors

/-! # Split-torus fixed Lie algebra in a nilpotent group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

attribute [local instance] Lie.coordinateOriginAlgebra

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

private theorem pow_apply_eq_pow_smul {A V : Type*} [CommRing A]
    [AddCommGroup V] [Module A V] (f : Module.End A V) (x : V) (a : A)
    (h : f x = a • x) (n : ℕ) : (f ^ n) x = a ^ n • x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, h, smul_smul, pow_succ]

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left]

private theorem split_weightSpace_eq_bot
    (hG : IsNilpotentGroupScheme G)
    (I : Type u) [Fintype I] [DecidableEq I]
    (i : splitTorus (Spec (CommRingCat.of k)) I ⟶ G)
    (χ : characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I))
    (hχ : χ ≠ 0) : weightSpace i χ = ⊥ := by
  apply bot_unique
  intro X hX
  rw [Submodule.mem_bot]
  let A := AddMonoidAlgebra k (I → ℤ)
  let t := splitTorus.universalPoint (R := CommRingCat.of k) I
  let m := splitTorus.characterLatticeEquiv k I χ
  let Y := lieKernelMapLinear G (Algebra.ofId k A) X
  let a : A := AddMonoidAlgebra.single m 1 - 1
  have hm : m ≠ 0 := by
    intro hm
    exact hχ ((splitTorus.characterLatticeEquiv k I).map_eq_zero_iff.mp hm)
  have ha : a ≠ 0 := by
    intro ha
    have he : AddMonoidAlgebra.single m (1 : k) = 1 := sub_eq_zero.mp ha
    have hc := congrArg (fun p : A => p.coeff m) he
    simp [AddMonoidAlgebra.one_def, hm] at hc
  have hval : (Lie.characterValue χ t : A) = AddMonoidAlgebra.single m 1 := by
    have h := splitTorus.characterValue_characterLatticeEquiv_symm k I m t
    rw [AddEquiv.symm_apply_apply, splitTorus.exponentValue_universalPoint] at h
    exact congrArg Units.val h
  have hY : Lie.adjointDifference G (t ≫ i.hom.hom) Y = a • Y := by
    change adjoint G A (t ≫ i.hom.hom) Y - Y = a • Y
    rw [(mem_weightSpace.mp hX) A t, hval]
    change AddMonoidAlgebra.single m (1 : k) • Y - Y =
      (AddMonoidAlgebra.single m (1 : k) - (1 : A)) • Y
    rw [sub_smul, one_smul]
  obtain ⟨d, hd⟩ := hG.isNilpotent_adjointDifference (t ≫ i.hom.hom)
  have hzero : a ^ d • Y = 0 := by
    rw [← pow_apply_eq_pow_smul _ _ _ hY, hd, LinearMap.zero_apply]
  apply (Lie.kernelDerivationLinearEquiv G (A := k)).injective
  apply Derivation.ext
  intro c
  rw [(Lie.kernelDerivationLinearEquiv G (A := k)).map_zero, Derivation.zero_apply]
  have hc := congrArg (fun z : Additive (lieKernel G A) =>
    Lie.kernelDerivationLinearEquiv G (A := A) z c) hzero
  rw [(Lie.kernelDerivationLinearEquiv G (A := A)).map_smul,
    (Lie.kernelDerivationLinearEquiv G (A := A)).map_zero] at hc
  simp only [Derivation.smul_apply, Derivation.zero_apply] at hc
  change a ^ d * Lie.kernelDerivationLinearEquiv G
    (lieKernelMapLinear G (Algebra.ofId k A) X) c = 0 at hc
  rw [Lie.kernelDerivationLinearEquiv_map G (Algebra.ofId k A) X c] at hc
  have hc' : algebraMap k A (Lie.kernelDerivationLinearEquiv G X c) = 0 :=
    (mul_eq_zero.mp hc).resolve_left (pow_ne_zero _ ha)
  exact (FaithfulSMul.algebraMap_injective k A)
    (hc'.trans (map_zero (algebraMap k A)).symm)

/-- A nonzero split-torus character has zero Lie weight space in a smooth
connected affine geometrically nilpotent group, in every characteristic. -/
theorem IsNilpotentGroupScheme.weightSpace_eq_bot
    (hG : IsNilpotentGroupScheme G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (χ : characterLattice T) (hχ : χ ≠ 0) :
    weightSpace i χ = ⊥ := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let := Fintype.ofFinite I
  let c := characterLattice.comapIso
    (T' := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) e
  have hψ : c.symm χ ≠ 0 := by
    intro h
    exact hχ (c.symm.map_eq_zero_iff.mp h)
  have he := weightSpace_comapIso
    (T' := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) e i (c.symm χ)
  rw [show characterLattice.comapIso e (c.symm χ) = χ from c.apply_symm_apply χ] at he
  rw [he]
  exact split_weightSpace_eq_bot hG I (e.inv ≫ i) (c.symm χ) hψ

/-- Every actual Lie vector has weight zero under a split torus in a
smooth connected affine geometrically nilpotent group. -/
theorem IsNilpotentGroupScheme.weightSpace_zero_eq_top
    (hG : IsNilpotentGroupScheme G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) : weightSpace i 0 = ⊤ := by
  classical
  apply top_unique
  rw [← (isInternal_weightSpace_of_isSplitTorus k G T hT i).submodule_iSup_eq_top]
  apply iSup_le
  intro χ
  by_cases hχ : χ = 0
  · subst χ
    exact le_rfl
  · rw [hG.weightSpace_eq_bot T hT i χ hχ]
    exact bot_le

/-- Identify the actual split-torus fixed Lie space with the full Lie
algebra of a smooth connected affine geometrically nilpotent group. -/
def IsNilpotentGroupScheme.splitTorusFixedLieEquiv
    (hG : IsNilpotentGroupScheme G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) :
    weightSpace i 0 ≃ₗ[k] Additive (lieKernel G k) :=
  LinearEquiv.ofBijective (weightSpace i 0).subtype
    ⟨Subtype.val_injective, fun X =>
      ⟨⟨X, by rw [hG.weightSpace_zero_eq_top T hT i]; trivial⟩, rfl⟩⟩

@[simp] theorem IsNilpotentGroupScheme.splitTorusFixedLieEquiv_apply
    (hG : IsNilpotentGroupScheme G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (X : weightSpace i 0) :
    hG.splitTorusFixedLieEquiv T hT i X = X := rfl

end Langlands.GroupScheme
