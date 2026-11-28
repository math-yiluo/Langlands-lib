import Langlands.Global.AdelicTruncatedEisensteinPairing
import Langlands.GroupScheme.Rational.DominantInvariantFormComparison

/-! # Orientation of the Weyl terms in the regularized cone limit -/

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Set
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme GroupScheme.RealTorusSpace Langlands.Aubert.General.RationalPointFamily

variable {F : Type} [Field F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

local notation "T" => fam.T
local notation "Δ" => simpleRelativeRoots fam.i fam.ν
local notation "W" => relativeWeylGroup fam.i
local notation "χ" => characterLattice T

/-- Coroot evaluation of the displacement transported back from the inducing face to the
face of the Weyl term. The Weyl class maps the term's Levi simple roots to the inducing
Levi simple roots. -/
def weylConeSlope (Q : StandardIndex F G fam.i fam.ν) (w : W) (Λ : Vstar T)
    (α : fam.relativeSimpleRoots Q) : ℝ :=
  pair T (relativeWeylFullRealAction fam.i w⁻¹ Λ)
    (fam.coroots.realCoroot ⟨α, fam.mem_relativeRoots_of_mem_relativeSimpleRoots Q α⟩)

/-- For a displacement in the open inducing face and a Weyl class carrying the term's
Levi simple roots onto the inducing Levi simple roots, no slope vanishes. All slopes
are positive exactly for the identity class at the inducing index. -/
def WeylConeOrientationStatement : Prop :=
  ∀ (P Q : StandardIndex F G fam.i fam.ν) (w : W) (Λ : Vstar T),
    (∀ α : relativeRoots fam.i, α.val ∈ P.val → pair T Λ (fam.coroots.realCoroot α) = 0) →
    (∀ α : relativeRoots fam.i, α.val ∈ Δ → α.val ∉ P.val → 0 < pair T Λ (fam.coroots.realCoroot α)) →
    schemeWeylCharacterAction fam.i w '' Q.val = P.val →
    (∀ α, fam.weylConeSlope Q w Λ α ≠ 0) ∧
    ((∀ α, 0 < fam.weylConeSlope Q w Λ α) ↔ Q = P ∧ w = 1)

theorem weylConeOrientation : WeylConeOrientationStatement fam := by
  classical
  intro P Q w Λ hΛzero hΛpos hw
  have hG := fam.connectedReductive
  have hi := fam.maximalSplit
  have hT := hi.isSplitSubtorus.1
  have hAllRoots := hT.finite_relativeRoots fam.i
  have hRootSystem := relativeRootSystem F G hG T fam.i hi
  obtain ⟨hW, _, C, cs, hcs⟩ := relativeWeylCoxeter F G hG T fam.i hi fam.ν fam.generic
  let : Fintype W := @Fintype.ofFinite _ hW
  let v (a : χ) : Vstar T := (1 : ℝ) ⊗ₜ[ℤ] a
  let B := relativeWeylInvariantForm fam.i hT
  let A := relativeWeylFullRealAction fam.i w
  let aW := schemeWeylCharacterAction fam.i w
  have hRootMem (α : fam.relativeSimpleRoots Q) : (α : χ) ∈ Δ :=
    (ArthurTruncation.mem_simpleFinset hG hi).mp (Finset.mem_filter.mp α.property).1
  have hOut (α : fam.relativeSimpleRoots Q) : (α : χ) ∉ Q.val :=
    (Finset.mem_filter.mp α.property).2
  have hΛnonneg (α : relativeRoots fam.i) (hα : α.val ∈ Δ) :
      0 ≤ pair T Λ ((1 : ℝ) ⊗ₜ[ℤ] fam.coroots.coroot α) := by
    by_cases hp : α.val ∈ P.val
    · exact (hΛzero α hp).ge
    · exact (hΛpos α hα hp).le
  have hBnonneg {a : χ} (ha : a ∈ positiveRelativeRoots fam.i fam.ν) : 0 ≤ B Λ (v a) :=
    fam.coroots.invariantForm_positiveRoot_nonneg hT fam.ν hΛnonneg ha
  have hLen (α : relativeRoots fam.i) : 0 < B (v α.val) (v α.val) := by
    apply relativeWeylInvariantForm_pos
    intro h
    have hz := congrArg (fun x => pair T x (fam.coroots.realCoroot α)) h
    change pair T ((1 : ℝ) ⊗ₜ[ℤ] α.val) ((1 : ℝ) ⊗ₜ[ℤ] fam.coroots.coroot α) =
      pair T 0 ((1 : ℝ) ⊗ₜ[ℤ] fam.coroots.coroot α) at hz
    norm_num [pair_tmul_tmul, fam.coroots.pair_self] at hz
  have hBtransport (α : fam.relativeSimpleRoots Q) :
      2 * B Λ (v (aW α.val)) = fam.weylConeSlope Q w Λ α * B (v α.val) (v α.val) := by
    have he := relativeWeylInvariantForm_invariant fam.i hT w
      (relativeWeylFullRealAction fam.i w⁻¹ Λ) (v α.val)
    change B (relativeWeylFullRealAction fam.i w
      (relativeWeylFullRealAction fam.i w⁻¹ Λ)) (v (aW α.val)) = _ at he
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one] at he
    change B Λ (v (aW α.val)) = _ at he
    rw [he]
    exact fam.coroots.two_mul_invariantForm_root hT
      ⟨α.val, fam.mem_relativeRoots_of_mem_relativeSimpleRoots Q α⟩ _
  have hNeg (β : relativeRoots fam.i) (hβ : β.val ∉ positiveRelativeRoots fam.i fam.ν) :
      -β.val ∈ positiveRelativeRoots fam.i fam.ν := by
    by_contra h
    exact hβ (mem_positiveRelativeRoots_of_neg_not_mem hRootSystem hT fam.generic β.property h)
  have hvneg (a : χ) : v (-a) = -v a := tmul_neg _ _
  have hzeroSpan {a : χ} (ha : a ∈ positiveRelativeRoots fam.i fam.ν) :
      B Λ (v a) = 0 → v a ∈ Submodule.span ℝ (v '' P.val) := by
    refine positiveRelativeRoots_induction fam.i fam.ν
      (P := fun a => B Λ (v a) = 0 → v a ∈ Submodule.span ℝ (v '' P.val)) ?_ ?_ ha
    · intro b hb hzero
      have hb' : b ∈ P.val := by
        by_contra hout
        let β : relativeRoots fam.i := ⟨b, hb.1.1⟩
        have h := fam.coroots.two_mul_invariantForm_root hT β Λ
        change 2 * B Λ (v b) = pair T Λ (fam.coroots.realCoroot β) * B (v b) (v b) at h
        rw [hzero, mul_zero] at h
        exact (mul_pos (hΛpos β hb hout) (hLen β)).ne' h.symm
      exact Submodule.subset_span ⟨b, hb', rfl⟩
    · intro b hb c hc h₁ h₂ hsum
      have hvadd : v (b + c) = v b + v c := tmul_add _ _ _
      rw [hvadd, map_add] at hsum
      rw [hvadd]
      exact Submodule.add_mem _ (h₁ (by linarith [hBnonneg hb, hBnonneg hc]))
        (h₂ (by linarith [hBnonneg hb, hBnonneg hc]))
  have hmapSpan : (Submodule.span ℝ (v '' Q.val)).map A.toLinearMap =
      Submodule.span ℝ (v '' P.val) := by
    rw [Submodule.map_span, Set.image_image]
    exact congrArg (Submodule.span ℝ) ((Set.image_image v aW Q.val).symm.trans
      (congrArg (Set.image v) hw))
  have hOutsideSpan (α : fam.relativeSimpleRoots Q) :
      v (aW α.val) ∉ Submodule.span ℝ (v '' P.val) := by
    intro h
    rw [← hmapSpan, Submodule.mem_map] at h
    obtain ⟨x, hx, he⟩ := h
    have hEq : x = v α.val := A.injective he
    rw [hEq] at hx
    let S : Set Δ := Subtype.val ⁻¹' Q.val
    have himage : (fun β : Δ => v β.val) '' S = v '' Q.val := by
      ext y
      constructor
      · rintro ⟨β, hβ, rfl⟩
        exact ⟨β.val, hβ, rfl⟩
      · rintro ⟨β, hβ, rfl⟩
        exact ⟨⟨β, Q.property hβ⟩, hβ, rfl⟩
    have hlin := fam.coroots.linearIndependent_realSimpleRoots fam.i fam.ν hT hAllRoots fam.generic
    exact hlin.notMem_span_image (s := S) (x := ⟨α.val, hRootMem α⟩) (hOut α) (himage ▸ hx)
  have hbarRoot (α : fam.relativeSimpleRoots Q) : aW α.val ∈ relativeRoots fam.i :=
    schemeWeylCharacterAction_mem_relativeRoots w (fam.mem_relativeRoots_of_mem_relativeSimpleRoots Q α)
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · intro α hzero
    have hBzero : B Λ (v (aW α.val)) = 0 := by
      have h := hBtransport α
      rw [hzero, zero_mul] at h
      linarith
    apply hOutsideSpan α
    by_cases hb : aW α.val ∈ positiveRelativeRoots fam.i fam.ν
    · exact hzeroSpan hb hBzero
    · have hneg := hNeg ⟨aW α.val, hbarRoot α⟩ hb
      have hm := hzeroSpan hneg (by rw [hvneg, map_neg, hBzero, neg_zero])
      rw [hvneg] at hm
      simpa only [neg_neg] using (Submodule.span ℝ (v '' P.val)).neg_mem hm
  · intro hpos
    have hone : w = 1 := by
      by_contra hne
      obtain ⟨α, hdescent⟩ := cs.exists_rightDescent_of_ne_one hne
      have hnot : aW α.val ∉ positiveRelativeRoots fam.i fam.ν :=
        fun h => lt_asymm hdescent ((hcs.2.2.1 w α).2 h)
      have hQ : α.val ∉ Q.val := by
        intro hmem
        have hP : aW α.val ∈ P.val := hw ▸ Set.mem_image_of_mem aW hmem
        exact hnot (P.property hP).1
      let β : fam.relativeSimpleRoots Q :=
        ⟨α.val, Finset.mem_filter.mpr ⟨(ArthurTruncation.mem_simpleFinset hG hi).mpr α.property, hQ⟩⟩
      have hneg := hBnonneg (hNeg ⟨aW β.val, hbarRoot β⟩ hnot)
      rw [hvneg, map_neg] at hneg
      have hprod := mul_pos (hpos β) (hLen ⟨β.val, fam.mem_relativeRoots_of_mem_relativeSimpleRoots Q β⟩)
      rw [← hBtransport β] at hprod
      linarith
    refine ⟨Subtype.ext ?_, hone⟩
    simpa only [hone, map_one, LinearEquiv.coe_one, Set.image_id] using hw
  · rintro ⟨rfl, rfl⟩ α
    simpa only [weylConeSlope, inv_one, map_one, LinearEquiv.coe_one, id_eq] using
      hΛpos ⟨α.val, fam.mem_relativeRoots_of_mem_relativeSimpleRoots Q α⟩ (hRootMem α) (hOut α)

end Langlands.Global.StandardParabolicFamily
