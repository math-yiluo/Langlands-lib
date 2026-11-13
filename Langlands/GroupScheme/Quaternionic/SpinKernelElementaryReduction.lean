import Langlands.GroupScheme.Quaternionic.KneserThreeSpinSubgroupStatement
import Langlands.GroupScheme.Quaternionic.SpinLeviLift
import Langlands.GroupScheme.Quaternionic.SpinLeviUniqueness
import Langlands.GroupScheme.Rational.ElementarySubgroupHom

/-!
# The rational kernel element of a quaternionic spin cover is elementary

Assuming `CentralSimpleUnits.DegreeTwoNormOneSimplyConnectedStatement` and
`KneserThreeSpinSubgroupStatement`, every Levi lift `(μ, ψ)` into a spin cover `π : S ⟶ O(q)`
factors through the lift `a : C ⟶ S` of the simply connected group `C` of
`KneserThreeSpinSubgroupStatement`, so `z(-1) = a(j(-1, -1))` lies in `S(K)⁺`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Langlands.CentralSimple
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Quaternionic.SpinKernel

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  [Algebra.IsCentral K D]

/-- `z` is natural in the pair `(μ, ψ)`: composing both with a homomorphism `a` composes
`z(u)` with `a`. -/
theorem kernelPoint_comp_hom (hdeg : reducedDegree K D = 2)
    {C S : GroupScheme (Spec (CommRingCat.of K))}
    (mu : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ C) (psi : CentralSimpleUnits.normOne K D ⟶ C)
    (a : C ⟶ S) (A : CommAlgCat.{u} (CommRingCat.of K)) (w : rootsOfUnity 2 A) :
    kernelPoint hdeg (mu ≫ a) (psi ≫ a) A w = kernelPoint hdeg mu psi A w ≫ a.hom.hom := by
  rw [kernelPoint, kernelPoint, MonObj.mul_comp, Grp.comp_hom_hom, Grp.comp_hom_hom,
    Category.assoc, Category.assoc]

/-- A rational point given by an affine point maps under `a` to the rational point given by
the composite affine point. -/
theorem rationalCoeffEquiv_symm_comp_hom {C S : GroupScheme (Spec (CommRingCat.of K))}
    (a : C ⟶ S) (x : C.affinePoints (CommAlgCat.of (CommRingCat.of K) K)) :
    (GaloisPointComparison.rationalCoeffEquiv K S).symm (x ≫ a.hom.hom) =
      rationalPoints.map a ((GaloisPointComparison.rationalCoeffEquiv K C).symm x) := by
  apply (GaloisPointComparison.rationalCoeffEquiv K S).injective
  rw [MulEquiv.apply_symm_apply, ← rationalCoeffEquiv_comp_hom, MulEquiv.apply_symm_apply]

variable [Infinite K] (σ : FirstKindInvolution K D)
  (hdim : Module.finrank K D = 4) (hsym : Module.finrank K σ.symmetricSubspace = 3)
  {n : Type} [Fintype n] [DecidableEq n]
  {q : σ.QuadraticForms n} {e f : n → D} (h : σ.IsHyperbolicPair q e f)
  {S : GroupScheme (Spec (CommRingCat.of K))}
  {π : S ⟶ σ.isometryGroup q}

/-- **One spin cover.** If the binary action of `h` factors as `j ≫ c` through a simply
connected group `C` in which `j(-1, -1)` is elementary, then for every Levi lift `(μ, ψ)` of
`h` into the spin cover `π`, the rational point `z(-1) = μ(-1) ψ(-1)` is elementary. -/
theorem kernelPoint_negOne_mem_of_subgroup (hπ : σ.IsSpinCover q π)
    (hsc : CentralSimpleUnits.DegreeTwoNormOneSimplyConnectedStatement.{u})
    {C : GroupScheme (Spec (CommRingCat.of K))} (hC : IsSimplyConnected C)
    (c : C ⟶ σ.isometryGroup q) (j : BinaryScheme.groupScheme (K := K) (D := D) ⟶ C)
    (hjc : j ≫ c = AmbientBinaryScheme.isometryHom σ hdim hsym h)
    (hneg : (GaloisPointComparison.rationalCoeffEquiv K C).symm
        (kernelPoint (FirstKindInvolution.reducedDegree_eq_two_of_finrank_four hdim)
          (SpecialLinear.BinaryRoot.upperCocharacter (CommRingCat.of K) ≫
            BinarySpinLift.firstFactor ≫ j)
          (BinarySpinLift.secondFactor ≫ j) _ negOneRoot) ∈
        parabolicElementarySubgroup C)
    {mu : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ S} {psi : CentralSimpleUnits.normOne K D ⟶ S}
    (hl : IsLeviLift h π mu psi) :
    (GaloisPointComparison.rationalCoeffEquiv K S).symm
        (kernelPoint (FirstKindInvolution.reducedDegree_eq_two_of_finrank_four hdim) mu psi _
          negOneRoot) ∈ parabolicElementarySubgroup S := by
  let a := hπ.liftHom hC c
  have hja : j ≫ a ≫ π = AmbientBinaryScheme.isometryHom σ hdim hsym h := by
    rw [hπ.liftHom_comp, hjc]
  have hl' := isLeviLift_binarySpinLift σ hdim hsym h hπ hsc
  -- The norm-one part of the Levi lift factors through `a`.
  have hpsi : psi = BinarySpinLift.secondFactor ≫ j ≫ a := by
    rw [hl.normOne_eq hl' hπ (hsc K D hdim).isSemisimple.isConnectedReductive]
    symm
    apply hπ.liftHom_unique (hsc K D hdim)
    rw [Category.assoc, Category.assoc, hja]
  -- The scalar part of the Levi lift factors through `a`.
  have hmu : mu = SpecialLinear.BinaryRoot.upperCocharacter (CommRingCat.of K) ≫
      BinarySpinLift.firstFactor ≫ j ≫ a := by
    rw [hl.scalar_eq hl' hπ, BinarySpinLift.scalar]
    congr 1
    symm
    apply hπ.liftHom_unique (BinarySpinLift.specialLinear_simplyConnected hsc K)
    rw [Category.assoc, Category.assoc, hja]
  have hk : kernelPoint (FirstKindInvolution.reducedDegree_eq_two_of_finrank_four hdim)
      mu psi (CommAlgCat.of (CommRingCat.of K) K) negOneRoot =
      kernelPoint (FirstKindInvolution.reducedDegree_eq_two_of_finrank_four hdim)
        (SpecialLinear.BinaryRoot.upperCocharacter (CommRingCat.of K) ≫
          BinarySpinLift.firstFactor ≫ j)
        (BinarySpinLift.secondFactor ≫ j) _ negOneRoot ≫ a.hom.hom := by
    rw [← kernelPoint_comp_hom, hpsi, hmu, Category.assoc, Category.assoc, Category.assoc]
  rw [hk, rationalCoeffEquiv_symm_comp_hom]
  exact parabolicElementarySubgroup_map_le_of_hom hC.isSemisimple.isConnectedReductive
    hπ.isSimplyConnected.isSemisimple.isConnectedReductive a ⟨_, hneg, rfl⟩

end Langlands.GroupScheme.Quaternionic.SpinKernel

namespace Langlands.GroupScheme.Quaternionic.SpinKernel

/-- In characteristic `2`, `-1 = 1` in `μ₂(K)`. -/
theorem negOneRoot_eq_one {K : Type u} [Field K] (h2 : (2 : K) = 0) :
    (negOneRoot : rootsOfUnity 2 (CommAlgCat.of (CommRingCat.of K) K)) = 1 := by
  apply Subtype.ext
  apply Units.ext
  change (-1 : K) = 1
  rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, h2]

/-- **Reduction of `SpinKernelElementaryLiftStatement`.** Simple connectedness of the norm-one
groups of quaternion algebras and `KneserThreeSpinSubgroupStatement` imply
`SpinKernelElementaryLiftStatement`. In characteristic `2` the point `z(-1) = z(1)` is the
identity. -/
theorem spinKernelElementaryLift_of_kneserThreeSpinSubgroup
    (hsc : CentralSimpleUnits.DegreeTwoNormOneSimplyConnectedStatement.{u})
    (hK : KneserThreeSpinSubgroupStatement.{u}) :
    SpinKernelElementaryLiftStatement.{u} := by
  intro K _ _ _ _ D _ _ _ _ hD σ hsym m hm q hq hw S π hπ e f h mu psi hl
  by_cases h2 : (2 : K) = 0
  · rw [negOneRoot_eq_one h2, kernelPoint_one, map_one]
    exact Subgroup.one_mem _
  have : Infinite K := Langlands.LocalField.infinite_of_isNonarchimedeanLocalField K
  obtain ⟨C, c, j, hC, hjc, hneg⟩ := hK K h2 D hD σ hsym m hm q hq hw e f h
  exact kernelPoint_negOne_mem_of_subgroup σ hD hsym h hπ hsc hC c j hjc hneg hl

end Langlands.GroupScheme.Quaternionic.SpinKernel
