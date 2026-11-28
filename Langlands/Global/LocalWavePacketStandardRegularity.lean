import Langlands.Global.AdelicStandardRootFunctional
import Langlands.GroupScheme.Rational.DominantInvariantFormComparison
import Langlands.GroupScheme.Rational.DominantWeylDisplacementRoots
import Langlands.Global.AdelicEisensteinRegularityParabolicTransport
import Langlands.Global.AdelicTruncatedEisensteinAsymptoticsStatement

/-! # Standard regularity of parameters and regularity for a standard root presentation -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
  Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) [Mono fam.i.hom.hom.left]
  [Fintype (relativeWeylGroup fam.i)]
  [∀ J, Mono (CommGroupScheme.groupHom (fam.f J)).hom.hom.left]

/-- For every threshold `R₁` there is a threshold `R` such that a parameter `λ` of `P_J` whose
restriction to the maximal split torus has coroot pairings `⟨Re λ|_T, α^∨⟩ > R` for all simple
roots `α ∉ J` (coroots taken from any reflection data `D`) is `R₁`-regular for the root
presentation of `P_J` in the family: `B(Re λ|_A, α) > R₁` for every root `α` of `A_J` in the
unipotent radical. -/
theorem exists_isRegularParameter_of_coroot_lt
    (D : RelativeRootReflectionData fam.i) (J : StandardIndex F G fam.i fam.ν)
    (hA : IsSplitTorus (fam.A J).toGrp) (hT : IsSplitTorus fam.T.toGrp) (R₁ : ℝ) :
    ∃ R : ℝ, ∀ lam : ComplexCharacterParameter F (fam.P J),
      (∀ α ∈ simpleRelativeRoots fam.i fam.ν, α ∉ J.val →
        R < RealTorusSpace.pair fam.T (fam.torusRestrictReal J (parameterRealPart F _ lam)) (ArthurTruncation.corootVector D α)) →
      (fam.rootPresentation J).IsRegularParameter hA hT R₁ lam := by
  classical
  let B := relativeWeylInvariantForm fam.i hT
  have hfin : (simpleRelativeRoots fam.i fam.ν).Finite :=
    (ArthurRelative.finite_relativeRoots fam.connectedReductive fam.maximalSplit).subset
      (simpleRelativeRoots_subset_relativeRoots fam.i fam.ν)
  have hrel : ∀ β ∈ simpleRelativeRoots fam.i fam.ν, β ∈ relativeRoots fam.i :=
    fun β hβ => simpleRelativeRoots_subset_relativeRoots fam.i fam.ν hβ
  have hpos (β : characterLattice fam.T) (hβ : β ∈ relativeRoots fam.i) :
      0 < B ((1 : ℝ) ⊗ₜ[ℤ] β) ((1 : ℝ) ⊗ₜ[ℤ] β) := by
    apply relativeWeylInvariantForm_pos
    intro h0
    have h2 := D.pair_root_realCoroot ⟨β, hβ⟩
    change RealTorusSpace.pair fam.T ((1 : ℝ) ⊗ₜ[ℤ] β) (D.realCoroot ⟨β, hβ⟩) = 2 at h2
    rw [h0, map_zero, LinearMap.zero_apply] at h2
    norm_num at h2
  let s := hfin.toFinset
  let S : ℝ := ∑ β ∈ s, 2 / B ((1 : ℝ) ⊗ₜ[ℤ] β) ((1 : ℝ) ⊗ₜ[ℤ] β)
  have hS : 0 ≤ S := Finset.sum_nonneg fun β hβ =>
    div_nonneg (by norm_num) (hpos β (hrel β (hfin.mem_toFinset.mp hβ))).le
  let c : ℝ := 1 / (1 + S)
  have hc : 0 < c := by positivity
  have hcle (β : characterLattice fam.T) (hβ : β ∈ simpleRelativeRoots fam.i fam.ν) :
      c ≤ B ((1 : ℝ) ⊗ₜ[ℤ] β) ((1 : ℝ) ⊗ₜ[ℤ] β) / 2 := by
    have hQ := hpos β (hrel β hβ)
    have h1 : 2 / B ((1 : ℝ) ⊗ₜ[ℤ] β) ((1 : ℝ) ⊗ₜ[ℤ] β) ≤ 1 + S := by
      have := Finset.single_le_sum (f := fun β => 2 / B ((1 : ℝ) ⊗ₜ[ℤ] β) ((1 : ℝ) ⊗ₜ[ℤ] β))
        (fun β hβ => div_nonneg (by norm_num) (hpos β (hrel β (hfin.mem_toFinset.mp hβ))).le)
        (hfin.mem_toFinset.mpr hβ)
      linarith
    calc c = 1 / (1 + S) := rfl
      _ ≤ 1 / (2 / B ((1 : ℝ) ⊗ₜ[ℤ] β) ((1 : ℝ) ⊗ₜ[ℤ] β)) :=
        one_div_le_one_div_of_le (div_pos (by norm_num) hQ) h1
      _ = _ := by rw [one_div_div]
  refine ⟨max 0 R₁ / c, fun lam hlam α hα => ?_⟩
  obtain ⟨hα0, χ, hχ, rfl⟩ := hα
  let y := fam.torusRestrictReal J (parameterRealPart F _ lam)
  have hR0 : 0 ≤ max 0 R₁ / c := div_nonneg (le_max_left _ _) hc.le
  have hRc : max 0 R₁ / c * c = max 0 R₁ := div_mul_cancel₀ _ hc.ne'
  have hJ0 : ∀ x ∈ AddSubmonoid.closure J.val, B y ((1 : ℝ) ⊗ₜ[ℤ] x) = 0 := by
    intro x hx
    induction hx using AddSubmonoid.closure_induction with
    | mem β hβ =>
      have hβr := hrel β (J.property hβ)
      have hann := fam.torusRestrictReal_mem_corootAnnihilator J (parameterRealPart F _ lam)
      rw [mem_corootAnnihilator] at hann
      exact fam.coroots.invariantForm_root_eq_zero hT ⟨β, hβr⟩ (hann ⟨β, hβr⟩ hβ)
    | zero => simp
    | add a b _ _ ha hb => rw [TensorProduct.tmul_add, map_add, ha, hb, add_zero]
  have hbig : ∀ x ∈ AddSubmonoid.closure (simpleRelativeRoots fam.i fam.ν),
      x ∈ AddSubmonoid.closure J.val ∨ max 0 R₁ < B y ((1 : ℝ) ⊗ₜ[ℤ] x) := by
    intro x hx
    induction hx using AddSubmonoid.closure_induction with
    | mem β hβ =>
      by_cases hβJ : β ∈ J.val
      · exact Or.inl (AddSubmonoid.subset_closure hβJ)
      · right
        have hβr := hrel β hβ
        have hlt := hlam β hβ hβJ
        have hcv : ArthurTruncation.corootVector D β = (1 : ℝ) ⊗ₜ[ℤ] D.coroot ⟨β, hβr⟩ := by
          simp only [ArthurTruncation.corootVector, hβr, ↓reduceDIte]
          rfl
        rw [hcv] at hlt
        have h2 := D.two_mul_invariantForm_root hT ⟨β, hβr⟩ y
        have hQ := hpos β hβr
        have hcβ := hcle β hβ
        have hm1 := mul_lt_mul_of_pos_right hlt hQ
        have hm2 := mul_le_mul_of_nonneg_left hcβ hR0
        change 2 * B y ((1 : ℝ) ⊗ₜ[ℤ] β) =
          RealTorusSpace.pair fam.T y ((1 : ℝ) ⊗ₜ[ℤ] D.coroot ⟨β, hβr⟩) * B ((1 : ℝ) ⊗ₜ[ℤ] β) ((1 : ℝ) ⊗ₜ[ℤ] β)
          at h2
        nlinarith
    | zero => exact Or.inl (zero_mem _)
    | add a b _ _ ha hb =>
      rcases ha with ha | ha
      · rcases hb with hb | hb
        · exact Or.inl (add_mem ha hb)
        · right
          rw [TensorProduct.tmul_add, map_add, hJ0 a ha, zero_add]
          exact hb
      · right
        rcases hb with hb | hb
        · rw [TensorProduct.tmul_add, map_add, hJ0 b hb, add_zero]
          exact ha
        · rw [TensorProduct.tmul_add, map_add]
          linarith [le_max_left 0 R₁]
  have hform : Langlands.Plancherel.weylInducedCharacterForm hA hT (fam.f J) fam.i
      (realParameterRestriction (fam.a J ≫ fam.l J) (parameterRealPart F _ lam))
        ((1 : ℝ) ⊗ₜ[ℤ] (fam.f J ≫ χ)) = B y ((1 : ℝ) ⊗ₜ[ℤ] χ) :=
    fam.realRootFunctional_eq J χ (parameterRealPart F _ lam)
  rcases hbig χ (DominantDisplacement.positive_mem_closure hχ) with hJ | hlt
  · exact absurd (((fam.rootPresentation J).restrict_positiveRoot_eq_zero_iff hχ).mpr hJ) hα0
  · have key : R₁ < B y ((1 : ℝ) ⊗ₜ[ℤ] χ) := lt_of_le_of_lt (le_max_right 0 R₁) hlt
    rw [← hform] at key
    exact key

end Langlands.Global.StandardParabolicFamily
