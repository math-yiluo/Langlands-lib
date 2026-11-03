import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.Lie.WeightImagePullback
import Langlands.GroupScheme.Lie.TorusCentralizer
import Langlands.GroupScheme.Absolute.RegularCocharacterWeights

/-! # Nonzero adjoint weights through a homomorphism with central kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section GeneralBase

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  {T : CommGroupScheme (Spec R)}

/-- The kernel of the actual differential of a homomorphism with central full kernel
lies in the zero adjoint weight space of every commutative subgroup action. -/
theorem mem_weightSpace_zero_of_central_kernel (q : G ⟶ H)
    (hq : IsCentral (kernelι q)) (i : T.toGrp ⟶ G)
    {X : Additive (lieKernel G R)} (hX : Lie.targetMapLinear q R X = 0) :
    X ∈ weightSpace i 0 := by
  apply Lie.mem_weightSpace_zero_of_mem_torusCentralizer i X.toMul
  have hk : X.toMul.val ≫ q.hom.hom = 1 :=
    congrArg (fun Y : Additive (lieKernel H R) => Y.toMul.val) hX
  have hc := (isCentral_kernelι_iff q).mp hq _ X.toMul.val hk
  intro V a t
  exact hc V a (t ≫ i.hom.hom)

end GeneralBase

section Field

variable {k : Type u} [Field k] {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A homomorphism with central full kernel is injective on each nonzero
adjoint weight space of a split torus. -/
theorem Lie.weightSpaceMap_injective_of_central_kernel (q : G ⟶ H)
    (hq : IsCentral (kernelι q)) (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    {χ : characterLattice T} (hχ : χ ≠ 0) :
    Function.Injective (Lie.weightSpaceMap q i χ) := by
  intro X Y hXY
  have hdiff : Lie.targetMapLinear q k
      ((X : Additive (lieKernel G k)) - (Y : Additive (lieKernel G k))) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr (congrArg Subtype.val hXY)
  have hzero := mem_weightSpace_zero_of_central_kernel q hq i hdiff
  have hweight : (X : Additive (lieKernel G k)) - (Y : Additive (lieKernel G k)) ∈
      weightSpace i χ := (weightSpace i χ).sub_mem X.property Y.property
  have h : (X : Additive (lieKernel G k)) - (Y : Additive (lieKernel G k)) = 0 :=
    (Submodule.disjoint_def.mp (weightSpace_disjoint hT i hχ)) _ hweight hzero
  exact Subtype.ext (sub_eq_zero.mp h)

/-- The actual nonzero source weight space is identified with its differential image
inside the corresponding target weight space. -/
def Lie.nonzeroWeightSpaceEquivRange (q : G ⟶ H)
    (hq : IsCentral (kernelι q)) (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    {χ : characterLattice T} (hχ : χ ≠ 0) :
    weightSpace i χ ≃ₗ[k] LinearMap.range (Lie.weightSpaceMap q i χ) :=
  LinearEquiv.ofInjective (Lie.weightSpaceMap q i χ)
    (Lie.weightSpaceMap_injective_of_central_kernel q hq i hT hχ)

@[simp]
theorem Lie.nonzeroWeightSpaceEquivRange_coe (q : G ⟶ H)
    (hq : IsCentral (kernelι q)) (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    {χ : characterLattice T} (hχ : χ ≠ 0) (X : weightSpace i χ) :
    ((Lie.nonzeroWeightSpaceEquivRange q hq i hT hχ X :
      weightSpace (i ≫ q) χ) : Additive (lieKernel H k)) =
        Lie.targetMapLinear q k X := rfl

/-- Central full kernels preserve every source root for the same split torus action. -/
theorem roots_subset_comp_of_central_kernel (q : G ⟶ H)
    (hq : IsCentral (kernelι q)) (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp) :
    roots i ⊆ roots (i ≫ q) := by
  intro χ hχ
  refine ⟨hχ.1, ?_⟩
  intro hbot
  apply hχ.2
  apply eq_bot_iff.mpr
  intro X hX
  have himage := lieKernelHomLinear_mem_weightSpace q i χ hX
  rw [hbot, Submodule.mem_bot] at himage
  have hzero := mem_weightSpace_zero_of_central_kernel q hq i himage
  exact (Submodule.disjoint_def.mp (weightSpace_disjoint hT i hχ.1)) X hX hzero

end Field

end Langlands.GroupScheme
