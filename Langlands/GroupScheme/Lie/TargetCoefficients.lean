import Langlands.GroupScheme.Lie.WeightImagePullback
import Langlands.GroupScheme.Torus.WeightDecomposition

/-! # Target maps and split-torus coefficients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Lie

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  [LocallyOfFiniteType G.X.hom]
  (q : G ⟶ H) (A : Type u) [CommRing A] [Algebra R A]
  (M : Type u) [AddCommMonoid M]

/-- Reading a group-algebra coefficient commutes with the actual differential. -/
theorem kernelCoefficient_targetMapLinear (m : M)
    (X : Additive (lieKernel G (AddMonoidAlgebra A M))) :
    kernelCoefficient H A M m (targetMapLinear q _ X) =
      targetMapLinear q A (kernelCoefficient G A M m X) := by
  classical
  have hsum (p : M →₀ Additive (lieKernel G A)) :
      kernelCoefficient H A M m
          (targetMapLinear q _
            (p.sum fun n y => AddMonoidAlgebra.single n (1 : A) •
              lieKernelMapLinear G (IsScalarTower.toAlgHom R A (AddMonoidAlgebra A M)) y)) =
        targetMapLinear q A (p m) := by
    induction p using Finsupp.induction_linear with
    | zero => simp
    | add p s hp hs =>
        rw [Finsupp.sum_add_index]
        · simp only [map_add, hp, hs, Finsupp.add_apply]
        · intro n; simp
        · intro n y z; simp [smul_add]
    | single n y =>
        rw [Finsupp.sum_single_index (by simp), map_smul,
          lieKernelTargetLinear_map, kernelCoefficient_monomial]
        by_cases h : n = m
        · subst m; simp
        · simp [h, Ne.symm h]
  simpa only [kernelCoefficients_reconstruct, kernelCoefficients_apply] using
    hsum (kernelCoefficients G X)

end Lie

namespace splitTorus

variable (k : Type u) [Field k] (I : Type u) [Fintype I] [DecidableEq I]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom]
  (q : G ⟶ H) (i : splitTorus (Spec (CommRingCat.of k)) I ⟶ G)

/-- Character-indexed adjoint coefficients commute with the actual differential. -/
theorem characterAdjointCoefficients_targetMapLinear
    (X : Additive (lieKernel G k))
    (χ : characterLattice (commGroupScheme (Spec (CommRingCat.of k)) I)) :
    characterAdjointCoefficients k I H (i ≫ q) (Lie.targetMapLinear q k X) χ =
      Lie.targetMapLinear q k (characterAdjointCoefficients k I G i X χ) := by
  have h : universalAdjoint I H (i ≫ q) (Lie.targetMapLinear q k X) =
      Lie.targetMapLinear q _ (universalAdjoint I G i X) := by
    dsimp only [universalAdjoint, LinearMap.coe_mk, AddHom.coe_mk]
    rw [lieKernelHomLinear_adjoint, lieKernelTargetLinear_map]
    simp only [Grp.comp_hom_hom, Category.assoc]
  simp only [characterAdjointCoefficients_apply]
  change Lie.kernelCoefficient H k (I → ℤ) _
      (universalAdjoint I H (i ≫ q) (Lie.targetMapLinear q k X)) =
    Lie.targetMapLinear q k (Lie.kernelCoefficient G k (I → ℤ) _
      (universalAdjoint I G i X))
  rw [h, Lie.kernelCoefficient_targetMapLinear q]

end splitTorus

namespace Lie

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (q : G ⟶ H) (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)

include hT

/-- A target weight vector in the differential image has a preimage of the same weight. -/
theorem exists_weightSpace_preimage {χ : characterLattice T}
    {X : Additive (lieKernel H k)} (hX : X ∈ weightSpace (i ≫ q) χ)
    (hrange : X ∈ LinearMap.range (targetMapLinear q k)) :
    ∃ Y ∈ weightSpace i χ, targetMapLinear q k Y = X := by
  classical
  obtain ⟨Y, hY⟩ := hrange
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let := Fintype.ofFinite I
  let c := characterLattice.comapIso
    (T' := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) e
  let ψ := c.symm χ
  have hχ : c ψ = χ := c.apply_symm_apply χ
  have hX' : X ∈ weightSpace (e.inv ≫ i ≫ q) ψ := by
    rw [← weightSpace_comapIso
      (T' := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) e (i ≫ q)]
    change X ∈ weightSpace (i ≫ q) (c ψ)
    rw [hχ]
    exact hX
  let Z := splitTorus.characterAdjointCoefficients k I G (e.inv ≫ i) Y ψ
  refine ⟨Z, ?_, ?_⟩
  · rw [← hχ]
    change Z ∈ weightSpace i (characterLattice.comapIso
      (T' := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) e ψ)
    rw [weightSpace_comapIso]
    exact splitTorus.characterAdjointCoefficients_mem k I G (e.inv ≫ i) Y ψ
  · have h := splitTorus.characterAdjointCoefficients_targetMapLinear
      k I q (e.inv ≫ i) Y ψ
    rw [hY] at h
    rw [Category.assoc,
      splitTorus.characterAdjointCoefficients_of_mem_weightSpace
        k I H (e.inv ≫ i ≫ q) ψ X hX'] at h
    simpa only [Finsupp.single_eq_same] using h.symm

/-- Restricting to a weight space gives exactly the corresponding part of the
full differential image. -/
theorem range_weightSpaceMap_eq_comap_range (χ : characterLattice T) :
    LinearMap.range (weightSpaceMap q i χ) =
      (LinearMap.range (targetMapLinear q k)).comap
        (weightSpace (i ≫ q) χ).subtype := by
  ext X
  constructor
  · rintro ⟨Y, rfl⟩
    exact ⟨Y, rfl⟩
  · intro hX
    obtain ⟨Y, hY, hYX⟩ := exists_weightSpace_preimage q i hT X.property hX
    exact ⟨⟨Y, hY⟩, Subtype.ext hYX⟩

/-- The differential image inside a target weight space is the intersection
with the full differential image, with the actual target vector unchanged. -/
def weightSpaceRangeEquiv (χ : characterLattice T) :
    LinearMap.range (weightSpaceMap q i χ) ≃ₗ[k]
      (LinearMap.range (targetMapLinear q k)).comap
        (weightSpace (i ≫ q) χ).subtype :=
  LinearEquiv.ofEq _ _ (range_weightSpaceMap_eq_comap_range q i hT χ)

@[simp] theorem weightSpaceRangeEquiv_coe (χ : characterLattice T)
    (X : LinearMap.range (weightSpaceMap q i χ)) :
    (weightSpaceRangeEquiv q i hT χ X : weightSpace (i ≫ q) χ) = X := rfl

end Lie

end Langlands.GroupScheme
