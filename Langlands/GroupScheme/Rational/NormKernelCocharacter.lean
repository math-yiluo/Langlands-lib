import Langlands.GroupScheme.Rational.RelativeWeylFaithfulness
import Langlands.GroupScheme.Rational.WeylPositiveCocharacter
import Langlands.GroupScheme.Rational.RelativeWeylRootKernel
import Langlands.GroupScheme.Rational.StandardParabolic
import Langlands.Geometry.Building.CocharacterUniformizerEvaluation

/-! # Standard cocharacters annihilating all ambient rational characters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj BigOperators

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]

variable [Fintype (relativeWeylGroup i)]

/-- The integral Weyl correction removes the invariant part without division. -/
def normKernelCocharacter (ζ : cocharacterLattice T) : cocharacterLattice T :=
  Fintype.card (relativeWeylGroup i) • ζ - relativeWeylCocharacterSum i ζ

/-- Every restricted ambient rational character annihilates the correction. -/
theorem latticePairing_normKernelCocharacter_restrict
    (ζ : cocharacterLattice T) (χ : rationalCharacters G) :
    latticePairing T (torusCharacterRestrict i χ) (normKernelCocharacter i ζ) = 0 := by
  classical
  have hs : latticePairing T (torusCharacterRestrict i χ)
      (relativeWeylCocharacterSum i ζ) =
      Fintype.card (relativeWeylGroup i) • latticePairing T (torusCharacterRestrict i χ) ζ := by
    rw [relativeWeylCocharacterSum_apply, map_sum]
    simp only [latticePairing_relativeWeyl_right,
      relativeWeylCharacterAction_eq_latticeAction,
      relativeWeylLatticeAction_torusCharacterRestrict, Finset.sum_const,
      Finset.card_univ]
  rw [normKernelCocharacter, map_sub, map_nsmul, hs, sub_self]

variable [IsAffineHom G.X.hom]

/-- Root pairings are multiplied by the positive Weyl-group order. -/
theorem latticePairing_normKernelCocharacter_root
    (hT : IsSplitTorus T.toGrp)
    (href : ∀ α ∈ relativeRoots i, ∃ w, IsRelativeReflection i α w)
    (ζ : cocharacterLattice T) (α : characterLattice T) (hα : α ∈ relativeRoots i) :
    latticePairing T α (normKernelCocharacter i ζ) =
      Fintype.card (relativeWeylGroup i) • latticePairing T α ζ := by
  rw [normKernelCocharacter, map_sub, map_nsmul,
    latticePairing_relativeWeylCocharacterSum_eq_zero i hT href ζ α hα, sub_zero]

/-- The correction preserves exactly the standard-cocharacter sign conditions. -/
theorem IsStandardCocharacter.normKernelCocharacter
    (hT : IsSplitTorus T.toGrp)
    (href : ∀ α ∈ relativeRoots i, ∃ w, IsRelativeReflection i α w)
    {ν ζ : cocharacterLattice T} {J : Set (characterLattice T)}
    (hζ : IsStandardCocharacter i ν J ζ) :
    IsStandardCocharacter i ν J (normKernelCocharacter i ζ) := by
  refine ⟨hζ.1, ?_, ?_⟩
  · intro α hα
    rw [latticePairing_normKernelCocharacter_root i hT href ζ α
      (hζ.1 hα).1.1, hζ.2.1 α hα, smul_zero]
  · intro α hα hαJ
    rw [latticePairing_normKernelCocharacter_root i hT href ζ α hα.1.1,
      nsmul_eq_mul]
    exact mul_pos (by exact_mod_cast Fintype.card_pos) (hζ.2.2 α hα hαJ)

omit [Fintype (relativeWeylGroup i)] [IsAffineHom G.X.hom] [Mono i.hom.hom.left] in
/-- Restriction and intrinsic cocharacter evaluation compute every ambient character. -/
theorem rationalCharacterEval_map_cocharacterPoints
    (ζ : cocharacterLattice T) (b : kˣ) (χ : rationalCharacters G) :
    rationalCharacterEval χ
      (rationalPoints.map i (CocharacterUniformizer.cocharacterPoints k T ζ b)) =
      b ^ latticePairing T (torusCharacterRestrict i χ) ζ := by
  rw [← rationalCharacterEval_characterRestrict]
  exact CocharacterUniformizer.rationalCharacterEval_cocharacterPoints k T
    (torusCharacterRestrict i χ) ζ b

omit [IsAffineHom G.X.hom] in
/-- At every field unit, all ambient rational characters of the corrected point equal one. -/
theorem rationalCharacterEval_normKernelCocharacter
    (ζ : cocharacterLattice T) (b : kˣ) (χ : rationalCharacters G) :
    rationalCharacterEval χ
      (rationalPoints.map i
        (CocharacterUniformizer.cocharacterPoints k T (normKernelCocharacter i ζ) b)) = 1 := by
  rw [rationalCharacterEval_map_cocharacterPoints,
    latticePairing_normKernelCocharacter_restrict, zpow_zero]

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [IsAffineHom G.X.hom] in
/-- Every corrected cocharacter value lies in the actual common rational norm kernel. -/
theorem normKernelCocharacter_mem_rationalCommonNormKernel
    (ζ : cocharacterLattice T) (b : kˣ) :
    rationalPoints.map i
      (CocharacterUniformizer.cocharacterPoints k T (normKernelCocharacter i ζ) b) ∈
        Plancherel.rationalCommonNormKernel G := by
  rw [Plancherel.mem_rationalCommonNormKernel]
  intro χ
  rw [rationalCharacterEval_normKernelCocharacter, map_one]

end Langlands.GroupScheme
