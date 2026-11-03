import Langlands.GroupScheme.Rational.GenericLieWeights
import Langlands.GroupScheme.Dynamic.LieProof
import Langlands.GroupScheme.Dynamic.OppositeIntersection
import Langlands.GroupScheme.Rational.RootKernelReflection
import Langlands.GroupScheme.Rational.IntegralRootLine

/-! # Root movement by opposing dynamic parabolics -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

private theorem opposite_twice {B : Scheme.{u}} {G : GroupScheme B}
    (χ : (Gm B).toGrp ⟶ G) :
    Dynamic.oppositeCocharacter (Dynamic.oppositeCocharacter χ) = χ := by
  simp only [Dynamic.oppositeCocharacter, ← Category.assoc]
  change CommGroupScheme.groupHom
    (Gm.powerHom B (-1) ≫ Gm.powerHom B (-1)) ≫ χ = χ
  have h : Gm.powerHom B (-1) ≫ Gm.powerHom B (-1) = 𝟙 _ := by
    simp [Gm.powerHom_apply, Preadditive.comp_neg]
  rw [h]
  exact Category.id_comp χ

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

private theorem positive_weight_mem_unipotent
    {a : characterLattice T} (hpos : 0 < latticePairing T a ν)
    {X : Additive (lieKernel G k)} (hX : X ∈ weightSpace i a) :
    X.toMul.val ∈
      (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier _ := by
  apply (dynamicLie k G (CommGroupScheme.groupHom ν ≫ i) X.toMul).2.2.mpr
  have hcomp : ν ≫ a = Gm.powerHom _ (latticePairing T a ν) := by
    apply (gmEndEquiv k).injective
    simp only [← latticePairing_apply, Gm.powerHom_apply, gmEndEquiv_zsmul_id]
  have hweight := weightSpace_le_comp ν i a hX
  rw [hcomp] at hweight
  let m := (latticePairing T a ν - 1).toNat
  have hm : (m : ℤ) + 1 = latticePairing T a ν := by
    dsimp only [m]
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  apply (le_iSup
    (fun n : ℕ => weightSpace (CommGroupScheme.groupHom ν ≫ i)
      (Gm.powerHom _ (n + 1))) m)
  simpa only [hm, ofMul_toMul] using hweight

variable [Mono i.hom.hom.left]

/-- If conjugation by a supplied normalizer carries a dynamic parabolic into
its opposite, that normalizer moves every character with positive pairing and
nonzero actual adjoint weight space. -/
theorem weylAction_ne_of_parabolic_le_opposite_comap
    {a : characterLattice T} (ha : weightSpace i a ≠ ⊥)
    (hpos : 0 < latticePairing T a ν) (n : normalizerPoints i)
    (hconj : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤
      (Dynamic.parabolic
        (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom ν ≫ i))).comap
          (G.innerIso n.val).hom) :
    weylAction i n a ≠ a := by
  intro hfix
  obtain ⟨X, hX, hX0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ha
  let χ := CommGroupScheme.groupHom ν ≫ i
  let Y := basePointAdjoint n.val X
  have hY : Y ∈ weightSpace i a := by
    have h := (isNormalizingPoint_normalizingAut i n).adjoint_mem_weightSpace hX
    rw [← weylAction_apply, hfix] at h
    exact h
  have hXU := positive_weight_mem_unipotent i ν hpos hX
  have hYU := positive_weight_mem_unipotent i ν hpos hY
  have hXP := Dynamic.unipotent_le_parabolic χ _ hXU
  have hYP := hconj _ hXP
  rw [SubgroupFunctor.mem_comap, comp_innerIso_hom] at hYP
  have hconstant :
      Lie.constant G (G.constantPoint n.val
        ((algSpec (CommRingCat.of k)).obj (Opposite.op (CommAlgCat.of k k)))) =
      G.constantPoint n.val _ :=
    G.constantPoint_naturality n.val _
  have hYval : Y.toMul.val =
      G.constantPoint n.val _ * X.toMul.val * (G.constantPoint n.val _)⁻¹ := by
    change Lie.constant G (G.constantPoint n.val _) * X.toMul.val *
      (Lie.constant G (G.constantPoint n.val _))⁻¹ = _
    rw [hconstant]
  rw [← hYval] at hYP
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hY1 : Y.toMul.val = 1 := by
    apply Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_parabolic
      (Dynamic.oppositeCocharacter χ) _ hYP
    simpa only [opposite_twice] using hYU
  have hY0 : Y = 0 := by
    apply Additive.toMul.injective
    exact Subtype.ext hY1
  apply hX0
  have h := congrArg (basePointAdjoint n.val⁻¹) hY0
  change (basePointAdjoint n.val⁻¹ * basePointAdjoint n.val) X = _ at h
  rw [basePointAdjoint_inv_mul n.val, Module.End.one_apply, map_zero] at h
  exact h

/-- Full scheme-kernel centralization promotes positive-root movement to the
negative sign on the integral character lattice, including divisible roots. -/
theorem weylAction_eq_neg_of_kernelCentralizing_opposite_parabolic
    (hT : IsSplitTorus T.toGrp) {a : characterLattice T}
    (ha : a ∈ relativeRoots i) (hpos : 0 < latticePairing T a ν)
    (n : normalizerPoints i)
    (hc : n.val ∈ (RelativeRoot.kernelCentralizer i a).carrier (Over.mk (𝟙 _)))
    (hconj : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤
      (Dynamic.parabolic
        (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom ν ≫ i))).comap
          (G.innerIso n.val).hom) :
    weylAction i n a = -a := by
  have := hT.isPerfPair_latticePairing
  have := Module.IsReflexive.of_isPerfPair (p := latticePairing T)
  exact IntegralRootLine.apply_eq_neg_of_ne a ha.1 (weylAction i n)
    (exists_integral_difference_of_mem_kernelCentralizer i hT a ha.1 n hc)
    (weylAction_ne_of_parabolic_le_opposite_comap i ν ha.2 hpos n hconj)

/-- Extract an actual integral coroot from a supplied full-kernel-centralizing
normalizer carrying the positive dynamic parabolic into its opposite. -/
def corootOfKernelCentralizingOppositeParabolic
    (hT : IsSplitTorus T.toGrp) {a : characterLattice T}
    (ha : a ∈ relativeRoots i) (hpos : 0 < latticePairing T a ν)
    (n : normalizerPoints i)
    (hc : n.val ∈ (RelativeRoot.kernelCentralizer i a).carrier (Over.mk (𝟙 _)))
    (hconj : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤
      (Dynamic.parabolic
        (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom ν ≫ i))).comap
          (G.innerIso n.val).hom) :
    {mu : cocharacterLattice T // latticePairing T a mu = 2 ∧
      ∀ b : characterLattice T, weylAction i n b = b - latticePairing T b mu • a} :=
  let h := hT.existsUnique_coroot_of_mem_kernelCentralizer i a ha.1 n
    (weylAction_eq_neg_of_kernelCentralizing_opposite_parabolic
      i ν hT ha hpos n hc hconj) hc
  ⟨Classical.choose h, (Classical.choose_spec h).1⟩

end Langlands.GroupScheme
