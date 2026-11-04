import Langlands.GroupScheme.CentralIsogeny.CommutatorTangent
import Langlands.GroupScheme.CentralIsogeny.NonzeroWeights
import Langlands.GroupScheme.Lie.TargetCoefficients

/-! # Nonzero weight equivalences for central isogenies -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace splitTorus

variable (k : Type u) [Field k] (I : Type u) [Fintype I] [DecidableEq I]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom]
  (q : G ⟶ H) (hqi : IsCentralIsogeny q)
  (i : splitTorus (Spec (CommRingCat.of k)) I ⟶ G)

include hqi in
/-- A nonzero weight for a standard split torus lies in the full differential image. -/
theorem mem_range_targetMapLinear_of_nonzero_weight
    {χ : characterLattice (commGroupScheme (Spec (CommRingCat.of k)) I)}
    (hχ : χ ≠ 0) {X : Additive (lieKernel H k)}
    (hX : X ∈ weightSpace (i ≫ q) χ) :
    X ∈ LinearMap.range (Lie.targetMapLinear q k) := by
  classical
  let m := characterLatticeEquiv k I χ
  have hm : m ≠ 0 := by
    intro hz
    apply hχ
    apply (characterLatticeEquiv k I).injective
    simpa only [map_zero] using hz
  let A := AddMonoidAlgebra k (I → ℤ)
  let U := lieKernelMapLinear H (Algebra.ofId (CommRingCat.of k) A) X
  let n := universalPoint (R := CommRingCat.of k) I ≫ i.hom.hom
  have hrange := CommutatorDescent.range_adjoint_sub_id_le_of_centralIsogeny q hqi n
    (A := A)
  have hU : adjoint H A (n ≫ q.hom.hom) U - U ∈
      LinearMap.range (Lie.targetMapLinear q A) :=
    hrange ⟨U, rfl⟩
  obtain ⟨Y, hY⟩ := hU
  refine ⟨Lie.kernelCoefficient G k (I → ℤ) m Y, ?_⟩
  rw [← Lie.kernelCoefficient_targetMapLinear q, hY, map_sub]
  have hadjoint : Lie.kernelCoefficient H k (I → ℤ) m
      (adjoint H A (n ≫ q.hom.hom) U) = X := by
    have hc := congrArg (fun p => p χ)
      (characterAdjointCoefficients_of_mem_weightSpace k I H (i ≫ q) χ X hX)
    simp only [characterAdjointCoefficients_apply, Finsupp.single_eq_same] at hc
    rw [universalAdjointCoefficients_apply] at hc
    have heq : adjoint H A (n ≫ q.hom.hom) U =
        universalAdjoint I H (i ≫ q) X := by
      dsimp only [universalAdjoint, LinearMap.coe_mk, AddHom.coe_mk, U, n]
      simp only [Grp.comp_hom_hom, Category.assoc]
      rfl
    rw [heq]
    exact hc
  have hconstant : Lie.kernelCoefficient H k (I → ℤ) m U = 0 := by
    have hc := Lie.kernelCoefficient_monomial H (A := k) (M := I → ℤ) m 0 1 X
    have hone : AddMonoidAlgebra.single (0 : I → ℤ) (1 : k) = 1 := rfl
    rw [hone, one_smul, ite_eq_right (Ne.symm hm)] at hc
    exact hc
  rw [hadjoint, hconstant, sub_zero]

end splitTorus

namespace Lie

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (q : G ⟶ H) (hqi : IsCentralIsogeny q)
  (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)

include hqi hT

/-- Every nonzero target weight lies in the full differential image of a central isogeny. -/
theorem mem_range_targetMapLinear_of_nonzero_weight_centralIsogeny
    {χ : characterLattice T} (hχ : χ ≠ 0)
    {X : Additive (lieKernel H k)} (hX : X ∈ weightSpace (i ≫ q) χ) :
    X ∈ LinearMap.range (targetMapLinear q k) := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let := Fintype.ofFinite I
  let c := characterLattice.comapIso
    (T' := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) e
  let ψ := c.symm χ
  have hχψ : c ψ = χ := c.apply_symm_apply χ
  have hψ : ψ ≠ 0 := by
    intro hz
    apply hχ
    rw [← hχψ, hz, map_zero]
  have hX' : X ∈ weightSpace (e.inv ≫ i ≫ q) ψ := by
    rw [← weightSpace_comapIso
      (T' := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) e (i ≫ q)]
    change X ∈ weightSpace (i ≫ q) (c ψ)
    rw [hχψ]
    exact hX
  apply splitTorus.mem_range_targetMapLinear_of_nonzero_weight k I q hqi
    (e.inv ≫ i) hψ
  simpa only [Category.assoc] using hX'

/-- A central isogeny is surjective on every nonzero split-torus weight space. -/
theorem weightSpaceMap_surjective_of_centralIsogeny
    {χ : characterLattice T} (hχ : χ ≠ 0) :
    Function.Surjective (weightSpaceMap q i χ) := by
  intro X
  have hrange := mem_range_targetMapLinear_of_nonzero_weight_centralIsogeny
    q hqi i hT hχ X.property
  obtain ⟨Y, hY, hYX⟩ := exists_weightSpace_preimage q i hT X.property hrange
  exact ⟨⟨Y, hY⟩, Subtype.ext hYX⟩

/-- The actual differential of a central isogeny is an equivalence on every nonzero weight. -/
def nonzeroWeightSpaceEquivOfCentralIsogeny
    {χ : characterLattice T} (hχ : χ ≠ 0) :
    weightSpace i χ ≃ₗ[k] weightSpace (i ≫ q) χ :=
  LinearEquiv.ofBijective (weightSpaceMap q i χ)
    ⟨weightSpaceMap_injective_of_central_kernel q hqi.isCentral_kernelι i hT hχ,
      weightSpaceMap_surjective_of_centralIsogeny q hqi i hT hχ⟩

@[simp]
theorem nonzeroWeightSpaceEquivOfCentralIsogeny_coe
    {χ : characterLattice T} (hχ : χ ≠ 0) (X : weightSpace i χ) :
    (nonzeroWeightSpaceEquivOfCentralIsogeny q hqi i hT hχ X :
      Additive (lieKernel H k)) = targetMapLinear q k X := rfl

end Lie

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A central isogeny preserves the root support for the same split-torus action. -/
theorem roots_comp_eq_of_centralIsogeny (q : G ⟶ H) (hqi : IsCentralIsogeny q)
    (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp) :
    roots (i ≫ q) = roots i := by
  apply Set.Subset.antisymm
  · intro χ hχ
    refine ⟨hχ.1, ?_⟩
    intro hbot
    apply hχ.2
    apply eq_bot_iff.mpr
    intro X hX
    obtain ⟨Y, hYX⟩ := Lie.weightSpaceMap_surjective_of_centralIsogeny
      q hqi i hT hχ.1 ⟨X, hX⟩
    have hY : (Y : Additive (lieKernel G k)) = 0 := by
      simpa only [hbot, Submodule.mem_bot] using Y.property
    have h := congrArg Subtype.val hYX
    change Lie.targetMapLinear q k (Y : Additive (lieKernel G k)) = X at h
    rw [hY, map_zero] at h
    exact h.symm
  · exact roots_subset_comp_of_central_kernel q hqi.isCentral_kernelι i hT

end Langlands.GroupScheme
