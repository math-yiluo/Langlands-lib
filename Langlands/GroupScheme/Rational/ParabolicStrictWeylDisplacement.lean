import Langlands.GroupScheme.Rational.ParabolicWeylDisplacement
import Langlands.Representation.LanglandsClassification.LanglandsTriplet

/-! # Strict dominant displacement outside the actual Levi Weyl subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RealTorusSpace RelativeRootSystem
open Langlands.Aubert.General.RationalPointFamily Langlands.Group.RelativeWeylIndexing

variable {k : Type u} [Field k]
  {T A : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]

/-- The actual Weyl elements preserving restriction of every full real character
along a specified torus morphism. -/
def relativeWeylRestrictionStabilizer (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (f : A ⟶ T) : Subgroup (relativeWeylGroup i) where
  carrier := {w | ∀ x : Vstar T,
    rationalCharacterRestrictReal (CommGroupScheme.groupHom f)
      (relativeWeylFullRealAction i w x) =
        rationalCharacterRestrictReal (CommGroupScheme.groupHom f) x}
  one_mem' := by simp
  mul_mem' := by
    intro w v hw hv x
    rw [map_mul, LinearEquiv.mul_apply, hw, hv]
  inv_mem' := by
    intro w hw x
    have h := hw (relativeWeylFullRealAction i w⁻¹ x)
    simpa only [map_inv, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] using h.symm

namespace ParabolicRootPresentation

variable {P M : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

local instance : Mono r.data.i.hom.hom.left := r.isCompatible.maximalSplit.isSplitSubtorus.mono

/-- The actual standard Levi Weyl subgroup fixes restriction along its split component. -/
theorem standardRelativeWeylGroup_le_restrictionStabilizer
    (D : RelativeRootReflectionData r.data.i)
    [Finite (relativeWeylGroup r.data.i)]
    {C : CoxeterMatrix (SimpleRoot r.data.i r.data.ν)}
    (cs : CoxeterSystem C (relativeWeylGroup r.data.i))
    (hcs : IsRelativeWeylCoxeterRealization r.data.i r.data.ν cs) :
    standardRelativeWeylGroup r.data.i r.data.ν r.data.J ≤
      relativeWeylRestrictionStabilizer r.data.i r.data.f := by
  classical
  have := r.finite_simpleRoots.to_subtype
  let I : Finset (SimpleRoot r.data.i r.data.ν) :=
    (Set.toFinite {α : SimpleRoot r.data.i r.data.ν | α.val ∈ r.data.J}).toFinset
  have hI (α : SimpleRoot r.data.i r.data.ν) : α ∈ I ↔ α.val ∈ r.data.J := by
    simp only [I, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  have hJ : rootSet r.data.i r.data.ν I = r.data.J := by
    ext α
    constructor
    · rintro ⟨β, hβ, rfl⟩
      exact (hI β).mp hβ
    · intro hα
      exact ⟨⟨α, r.isCompatible.subset_simpleRoots hα⟩, (hI _).mpr hα, rfl⟩
  rw [← hJ, ← hcs.2.2.2.2 I, standardSubgroup, Subgroup.closure_le]
  rintro _ ⟨α, hα, rfl⟩
  intro x
  have hT := r.isCompatible.maximalSplit.isSplitSubtorus.1
  have hs := hcs.eq_simple_of_isRelativeReflection hT α
    (D.isRelativeReflection_representative hT (hT.finite_relativeRoots r.data.i)
      ⟨α.val, α.property.1.1⟩)
  rw [← hs, D.fullRealAction_representative, map_sub, map_smul]
  have hz : rationalCharacterRestrictReal (CommGroupScheme.groupHom r.data.f)
      ((1 : ℝ) ⊗ₜ[ℤ] α.val) = 0 := by
    change (1 : ℝ) ⊗ₜ[ℤ] (r.data.f ≫ α.val) = 0
    rw [r.selectedRoot_restrict_eq_zero ((hI α).mp hα), tmul_zero]
  rw [hz, smul_zero, sub_zero]

/-- A dominant character strictly positive outside the selected simple roots
has zero restricted displacement exactly on the actual Levi Weyl subgroup. -/
theorem restrict_displacement_eq_zero_iff_of_coxeter
    (D : RelativeRootReflectionData r.data.i)
    [Finite (relativeWeylGroup r.data.i)]
    {C : CoxeterMatrix (SimpleRoot r.data.i r.data.ν)}
    (cs : CoxeterSystem C (relativeWeylGroup r.data.i))
    (hcs : IsRelativeWeylCoxeterRealization r.data.i r.data.ν cs)
    (x : Vstar r.data.T)
    (hx : ∀ α : SimpleRoot r.data.i r.data.ν,
      0 ≤ pair r.data.T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot ⟨α.val, α.property.1.1⟩))
    (hpos : ∀ α : SimpleRoot r.data.i r.data.ν, α.val ∉ r.data.J →
      0 < pair r.data.T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot ⟨α.val, α.property.1.1⟩))
    (w : relativeWeylGroup r.data.i) :
    rationalCharacterRestrictReal (CommGroupScheme.groupHom r.data.f)
      (relativeWeylDisplacement w x) = 0 ↔
        w ∈ standardRelativeWeylGroup r.data.i r.data.ν r.data.J := by
  let R := rationalCharacterRestrictReal (CommGroupScheme.groupHom r.data.f)
  let H := standardRelativeWeylGroup r.data.i r.data.ν r.data.J
  have hfix := r.standardRelativeWeylGroup_le_restrictionStabilizer D cs hcs
  have hT := r.isCompatible.maximalSplit.isSplitSubtorus.1
  have hs (α : SimpleRoot r.data.i r.data.ν) :
      (QuotientGroup.mk (D.representative ⟨α.val, α.property.1.1⟩) :
        relativeWeylGroup r.data.i) = cs.simple α :=
    hcs.eq_simple_of_isRelativeReflection hT α
      (D.isRelativeReflection_representative hT (hT.finite_relativeRoots r.data.i)
        ⟨α.val, α.property.1.1⟩)
  constructor
  · intro hzero
    suffices h : ∀ n (v : relativeWeylGroup r.data.i), cs.length v = n →
        R (relativeWeylDisplacement v x) = 0 → v ∈ H from h _ w rfl hzero
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv hvzero
      by_cases hv1 : v = 1
      · simpa only [hv1] using H.one_mem
      obtain ⟨α, hα⟩ := cs.exists_rightDescent_of_ne_one hv1
      change cs.length (v * cs.simple α) < cs.length v at hα
      let v' := v * cs.simple α
      have hv' : cs.length v' < n := by simpa only [v', ← hv] using hα
      have hv's : v' * cs.simple α = v := cs.simple_mul_simple_cancel_right α
      have hstep : cs.length v' < cs.length (v' * cs.simple α) := by
        rw [hv's, hv]
        exact hv'
      have hrootpos := (hcs.2.2.1 v' α).mp hstep
      let c := pair r.data.T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot ⟨α.val, α.property.1.1⟩)
      let β := R (relativeWeylFullRealAction r.data.i v' ((1 : ℝ) ⊗ₜ[ℤ] α.val))
      have hβ : β ∈ r.nonnegCone := by
        change (1 : ℝ) ⊗ₜ[ℤ] (r.data.f ≫
          schemeWeylCharacterAction r.data.i v' α.val) ∈ _
        exact r.one_tmul_restrict_mem_nonnegCone hrootpos
      have hvcone := r.restrict_displacement_mem_nonnegCone_of_coxeter D cs hcs x hx v'
      have hcβ := r.smul_mem_nonnegCone (hx α) hβ
      have hsimple : relativeWeylDisplacement (cs.simple α) x =
          c • ((1 : ℝ) ⊗ₜ[ℤ] α.val) := by
        rw [← hs α, relativeWeylDisplacement_apply, D.fullRealAction_representative]
        dsimp [c]
        abel
      have hsum : R (relativeWeylDisplacement v' x) + c • β = 0 := by
        rw [← hv's, relativeWeylDisplacement_mul, hsimple, map_smul, map_add,
          map_smul] at hvzero
        exact hvzero
      have hvzero' : R (relativeWeylDisplacement v' x) = 0 := by
        by_contra hne
        exact (r.add_ne_zero_of_mem_nonnegCone hcβ hvcone hne)
          (by simpa only [add_comm] using hsum)
      have hvH : v' ∈ H := ih _ hv' v' rfl hvzero'
      have hαJ : α.val ∈ r.data.J := by
        by_contra hnotJ
        have hcpos : 0 < c := hpos α hnotJ
        have hβfix : β = R ((1 : ℝ) ⊗ₜ[ℤ] α.val) := hfix hvH _
        have hβevalpos : 0 < r.splitComponentEvaluation β := by
          rw [hβfix]
          exact r.splitComponentEvaluation_pos_of_mem_restrictedRoots
            (r.mem_restrictedRoots.mpr ⟨α.val, α.property, hnotJ, rfl⟩)
        have heval := congrArg r.splitComponentEvaluation hsum
        rw [hvzero', zero_add, map_smul, map_zero, smul_eq_mul] at heval
        exact (mul_pos hcpos hβevalpos).ne' heval
      have hsH : cs.simple α ∈ H := by
        classical
        have := r.finite_simpleRoots.to_subtype
        let I : Finset (SimpleRoot r.data.i r.data.ν) :=
          (Set.toFinite {α : SimpleRoot r.data.i r.data.ν | α.val ∈ r.data.J}).toFinset
        have hI (β : SimpleRoot r.data.i r.data.ν) : β ∈ I ↔ β.val ∈ r.data.J := by
          simp only [I, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
        have hJ : rootSet r.data.i r.data.ν I = r.data.J := by
          ext β
          constructor
          · rintro ⟨bidx, hbidx, rfl⟩
            exact (hI bidx).mp hbidx
          · intro hβ
            exact ⟨⟨β, r.isCompatible.subset_simpleRoots hβ⟩, (hI _).mpr hβ, rfl⟩
        change cs.simple α ∈ standardRelativeWeylGroup r.data.i r.data.ν r.data.J
        rw [← hJ, ← hcs.2.2.2.2 I]
        exact simple_mem_standardSubgroup cs ((hI α).mpr hαJ)
      rw [← hv's]
      exact H.mul_mem hvH hsH
  · intro hw
    change R (x - relativeWeylFullRealAction r.data.i w x) = 0
    rw [map_sub, hfix hw x, sub_self]

/-- The connected reductive version discharges the Coxeter realization. -/
theorem restrict_displacement_eq_zero_iff (hG : IsConnectedReductive G)
    (D : RelativeRootReflectionData r.data.i) (x : Vstar r.data.T)
    (hx : ∀ α : SimpleRoot r.data.i r.data.ν,
      0 ≤ pair r.data.T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot ⟨α.val, α.property.1.1⟩))
    (hpos : ∀ α : SimpleRoot r.data.i r.data.ν, α.val ∉ r.data.J →
      0 < pair r.data.T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot ⟨α.val, α.property.1.1⟩))
    (w : relativeWeylGroup r.data.i) :
    rationalCharacterRestrictReal (CommGroupScheme.groupHom r.data.f)
      (relativeWeylDisplacement w x) = 0 ↔
        w ∈ standardRelativeWeylGroup r.data.i r.data.ν r.data.J := by
  obtain ⟨hW, _, C, cs, hcs⟩ := relativeWeylCoxeter k G hG r.data.T r.data.i
    r.isCompatible.maximalSplit r.data.ν r.isCompatible.generic
  have := hW
  exact r.restrict_displacement_eq_zero_iff_of_coxeter D cs hcs x hx hpos w

/-- Outside the Levi Weyl subgroup, the restricted displacement has strictly
positive defining evaluation. -/
theorem evaluation_restrict_displacement_pos (hG : IsConnectedReductive G)
    (D : RelativeRootReflectionData r.data.i) (x : Vstar r.data.T)
    (hx : ∀ α : SimpleRoot r.data.i r.data.ν,
      0 ≤ pair r.data.T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot ⟨α.val, α.property.1.1⟩))
    (hpos : ∀ α : SimpleRoot r.data.i r.data.ν, α.val ∉ r.data.J →
      0 < pair r.data.T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot ⟨α.val, α.property.1.1⟩))
    (w : relativeWeylGroup r.data.i)
    (hw : w ∉ standardRelativeWeylGroup r.data.i r.data.ν r.data.J) :
    0 < r.splitComponentEvaluation
      (rationalCharacterRestrictReal (CommGroupScheme.groupHom r.data.f)
        (relativeWeylDisplacement w x)) := by
  exact r.splitComponentEvaluation_pos_of_mem_nonnegCone
    (r.restrict_displacement_mem_nonnegCone hG D x hx w)
    (fun hz => hw ((r.restrict_displacement_eq_zero_iff hG D x hx hpos w).mp hz))

/-- Every parameter in the published open coroot chamber admits a single lift
whose Weyl translates outside the Levi subgroup restrict to that parameter
minus a nonzero vector of the actual parabolic cone. -/
theorem exists_lift_strict_displacement_of_mem_restrictedCorootChamber
    (hG : IsConnectedReductive G) (D : RelativeRootReflectionData r.data.i)
    {paramA : Vstar A}
    (hparamA : paramA ∈ restrictedCorootChamber r.data.i r.data.ν r.data.J r.data.f D) :
    ∃ x : Vstar r.data.T,
      rationalCharacterRestrictReal (CommGroupScheme.groupHom r.data.f) x = paramA ∧
      ∀ w : relativeWeylGroup r.data.i,
        w ∉ standardRelativeWeylGroup r.data.i r.data.ν r.data.J →
        ∃ δ : Vstar A, δ ∈ r.nonnegCone ∧ δ ≠ 0 ∧
          rationalCharacterRestrictReal (CommGroupScheme.groupHom r.data.f)
            (relativeWeylFullRealAction r.data.i w x) = paramA - δ := by
  obtain ⟨x, hxparamA, hxJ, hxpos⟩ := hparamA
  have hxnonneg (α : SimpleRoot r.data.i r.data.ν) :
      0 ≤ pair r.data.T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot ⟨α.val, α.property.1.1⟩) := by
    by_cases hαJ : α.val ∈ r.data.J
    · rw [hxJ _ hαJ]
    · exact (hxpos _ α.property hαJ).le
  have hxstrict (α : SimpleRoot r.data.i r.data.ν) (hαJ : α.val ∉ r.data.J) :
      0 < pair r.data.T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot ⟨α.val, α.property.1.1⟩) :=
    hxpos _ α.property hαJ
  refine ⟨x, hxparamA, fun w hw => ?_⟩
  refine ⟨rationalCharacterRestrictReal (CommGroupScheme.groupHom r.data.f)
    (relativeWeylDisplacement w x), r.restrict_displacement_mem_nonnegCone hG D x hxnonneg w,
    fun hz => hw ((r.restrict_displacement_eq_zero_iff hG D x hxnonneg hxstrict w).mp hz), ?_⟩
  rw [relativeWeylDisplacement_apply, map_sub, hxparamA]
  abel

end ParabolicRootPresentation

end Langlands.GroupScheme
