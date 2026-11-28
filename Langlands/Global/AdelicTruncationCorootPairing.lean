import Langlands.Global.AdelicTruncationAffineDenominators
import Langlands.Global.AdelicStandardRootFunctional
import Langlands.Global.AdelicWeylParameterEquivalence
import Langlands.Representation.Exponents.MaximalLeviExponentTransport

/-! # Nonvanishing coroot denominators for conjugate Levi parameters -/

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Set
open scoped CategoryTheory.MonObj TensorProduct Classical

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
  Langlands.Global.AdelicGroupPoints Langlands.Global.ImaginaryAxis

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (Q : StandardIndex F G fam.i fam.ν)

omit [NumberField F] in
private theorem chamberEmbedding_eq_torusRestrictReal
    (x : RealCharacterParameter F (fam.P Q)) :
    fam.chamberEmbedding Q x = fam.torusRestrictReal Q x := by
  induction x using TensorProduct.inductionOn with
  | tmul a χ => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Each relative coroot has a real parabolic character parameter dual to it in the
list of relative coroots. -/
def RelativeCorootDualityStatement : Prop :=
  ∀ α : fam.relativeSimpleRoots Q, ∃ x : RealCharacterParameter F (fam.P Q),
    ∀ β : fam.relativeSimpleRoots Q,
      realParameterPairing F (fam.P Q) x (fam.relativeCoroot Q β) = if α = β then 1 else 0

omit [NumberField F] in
/-- Pull the corresponding fundamental weight back through the standard Levi. -/
theorem relativeCorootDuality : fam.RelativeCorootDualityStatement Q := by
  classical
  intro α
  let Δ := simpleRelativeRoots fam.i fam.ν
  let wt := ArthurRelative.weight fam.connectedReductive fam.maximalSplit fam.ν
    fam.coroots Δ α.val
  let : (pair fam.T).IsPerfPair := isPerfPair_of_isSplitTorus fam.maximalSplit.isSplitSubtorus.1
  obtain ⟨w, hw⟩ := (LinearMap.IsPerfPair.bijective_left (pair fam.T)).surjective wt
  have hpair (v : V fam.T) : pair fam.T w v = wt v := LinearMap.congr_fun hw v
  have hαN : α.val ∉ Q.val := (Finset.mem_filter.mp α.property).2
  have hα : α.val ∈ Δ := by
    apply (ArthurTruncation.mem_simpleFinset _ _).mp
    exact (Finset.mem_filter.mp α.property).1
  have hAnn : w ∈ corootAnnihilator fam.i fam.coroots Q.val := by
    apply (mem_corootAnnihilator fam.i fam.coroots Q.val w).mpr
    intro β hβ
    change pair fam.T w (fam.coroots.realCoroot β) = 0
    rw [hpair]
    change ArthurRelative.weight fam.connectedReductive fam.maximalSplit fam.ν
      fam.coroots Δ α.val (fam.coroots.realCoroot β) = 0
    rw [ArthurRelative.weight_coroot fam.connectedReductive fam.maximalSplit fam.coroots
      fam.generic (subset_rfl : Δ ⊆ Δ) hα β (Q.property hβ)]
    have hn : α.val ≠ β.val := fun he => hαN (he.symm ▸ hβ)
    simp only [ite_eq_right hn]
  rw [← fam.range_restrictReal_torus Q] at hAnn
  obtain ⟨m, hm⟩ := hAnn
  obtain ⟨_, _, r, _, _, hr, _⟩ := (fam.isCompatible Q).levi.exists_unipotentRadical_retraction
  let x := rationalCharacterRestrictReal r m
  have hx : fam.chamberEmbedding Q x = w := by
    rw [chamberEmbedding_eq_torusRestrictReal]
    change rationalCharacterRestrictReal (fam.torus Q ≫ fam.l Q)
      (rationalCharacterRestrictReal r m) = _
    rw [rationalCharacterRestrictReal_comp_apply, Category.assoc, hr, Category.comp_id, hm]
  refine ⟨x, fun β => ?_⟩
  rw [relativeCoroot, realParameterPairing_splitDual, hx, hpair]
  have hβ : β.val ∈ Δ :=
    (ArthurTruncation.mem_simpleFinset _ _).mp (Finset.mem_filter.mp β.property).1
  change ArthurRelative.weight fam.connectedReductive fam.maximalSplit fam.ν
    fam.coroots Δ α.val (fam.coroots.realCoroot ⟨β.val, _⟩) = _
  rw [ArthurRelative.weight_coroot fam.connectedReductive fam.maximalSplit fam.coroots
    fam.generic (subset_rfl : Δ ⊆ Δ) hα ⟨β.val, _⟩ hβ]
  by_cases he : α = β
  · subst β
    simp
  · rw [ite_eq_right he, ite_eq_right (fun hv => he (Subtype.ext hv))]

omit [NumberField F] in
private theorem complexParameterPairing_complexify_re
    {P : GroupScheme (Spec (CommRingCat.of F))} (x : RealCharacterParameter F P)
    (H : RealCharacterDual F P) :
    (complexParameterPairing F P (complexify x) H).re = realParameterPairing F P x H := by
  induction x using TensorProduct.inductionOn with
  | tmul t χ => simp [Complex.mul_re]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, Complex.add_re, hx, hy]

omit [NumberField F] in
/-- A relative simple coroot gives a nonzero complex linear evaluation. -/
theorem exists_corootValue_ne_zero (α : fam.relativeSimpleRoots Q) :
    ∃ x : ComplexCharacterParameter F (fam.P Q), fam.corootValue Q x α ≠ 0 := by
  obtain ⟨x, hx⟩ := fam.relativeCorootDuality Q α
  refine ⟨complexify x, fun h => ?_⟩
  have hpair := complexParameterPairing_complexify_re x (fam.relativeCoroot Q α)
  change (fam.corootValue Q (complexify x) α).re = _ at hpair
  simp [h, hx] at hpair

variable (P : StandardIndex F G fam.i fam.ν) {n : ℕ}
  (ec : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F (fam.P P))

omit [NumberField F] in
/-- A surjective label linear part has a nonvanishing imaginary coroot evaluation,
even with an arbitrary affine offset. In particular the linear part can be an
actual Weyl parameter equivalence. -/
theorem exists_imaginary_corootValue_ne_zero
    (A : ComplexCharacterParameter F (fam.P P) →ₗ[ℂ] ComplexCharacterParameter F (fam.P Q))
    (hA : Function.Surjective A) (b : ComplexCharacterParameter F (fam.P Q))
    (α : fam.relativeSimpleRoots Q) :
    ∃ x : Fin n → ℝ, fam.corootValue Q (A (ec (imaginarySlice x)) + b) α ≠ 0 := by
  let ℓ := (complexParameterPairingAt (fam.P Q) (fam.relativeCoroot Q α)).comp
    (A.comp ec.toLinearMap)
  have hne : ∃ s, ℓ s ≠ 0 := by
    obtain ⟨y, hy⟩ := fam.exists_corootValue_ne_zero Q α
    obtain ⟨s, hs⟩ := (hA.comp ec.surjective) y
    change A (ec s) = y at hs
    exact ⟨s, by change fam.corootValue Q (A (ec s)) α ≠ 0; rwa [hs]⟩
  let c := fam.corootValue Q b α
  have he (s : Fin n → ℂ) :
      fam.corootValue Q (A (ec s) + b) α = ℓ s + c := by
    simp only [corootValue, map_add, LinearMap.add_apply]
    rfl
  by_cases hc : c = 0
  · obtain ⟨s, hs⟩ := hne
    by_contra h
    push Not at h
    have hzero (x : Fin n → ℝ) : ℓ (fun j => (x j : ℂ)) = 0 := by
      have hi := h x
      rw [he, hc, add_zero] at hi
      have hix : imaginarySlice x = Complex.I • (fun j => (x j : ℂ)) := rfl
      rw [hix, map_smul, smul_eq_mul] at hi
      exact (mul_eq_zero.mp hi).resolve_left Complex.I_ne_zero
    have hsplit : s = (fun j => ((s j).re : ℂ)) + Complex.I • (fun j => ((s j).im : ℂ)) := by
      ext j
      change s j = (s j).re + Complex.I * (s j).im
      rw [mul_comm Complex.I]
      exact (Complex.re_add_im (s j)).symm
    apply hs
    rw [hsplit, map_add, map_smul, hzero, hzero, smul_zero, zero_add]
  · refine ⟨0, ?_⟩
    have hs : imaginarySlice (0 : Fin n → ℝ) = 0 := by ext j; simp [imaginarySlice]
    rwa [he, hs, map_zero, zero_add]

/-- The Weyl map for an isomorphism of the two Levi subgroups supplies the needed
nonvanishing witness for every relative simple coroot. -/
theorem exists_imaginary_weylCoroot_ne_zero
    (c : fam.M Q ⟶ fam.M P) [IsIso c] (r : fam.P Q ⟶ fam.M Q)
    (hr : fam.l Q ≫ r = 𝟙 (fam.M Q)) (b : ComplexCharacterParameter F (fam.P Q))
    (α : fam.relativeSimpleRoots Q) :
    ∃ x : Fin n → ℝ,
      fam.corootValue Q (weylParameter (fam.l P) c r (ec (imaginarySlice x)) + b) α ≠ 0 := by
  obtain ⟨e, he⟩ := exists_weylParameter_linearEquiv (fam.l P) (fam.l Q)
    (fam.isCompatible P).levi (fam.isCompatible Q).levi c r hr
  exact fam.exists_imaginary_corootValue_ne_zero Q P ec _
    (he ▸ e.surjective) b α

omit [NumberField F] in
private theorem parameterRealPart_weylParameter_imaginary
    (c : fam.M Q ⟶ fam.M P) (r : fam.P Q ⟶ fam.M Q)
    (x : RealCharacterParameter F (fam.P P)) :
    parameterRealPart F (fam.P Q) (weylParameter (fam.l P) c r
      (imaginaryParameter F (fam.P P) x)) = 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul t χ =>
    simp [imaginaryParameter, AlgebraTensorModule.map_tmul, weylParameter_tmul]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

omit [NumberField F] in
/-- In a chart matching the given imaginary coordinates, the Weyl coroot linear
form is real on real inputs. -/
theorem affineCorootLinear_im_eq_zero_of_weylParameter
    (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F (fam.P P))
    (he : ∀ x, ec (imaginarySlice x) = imaginaryParameter F (fam.P P) (e x))
    (L : ∀ J, fam.AffineExponentLabels P J) (k : Fin (L Q).size)
    (c : fam.M Q ⟶ fam.M P) (r : fam.P Q ⟶ fam.M Q)
    (hL : (L Q).linear k = weylParameter (fam.l P) c r)
    (α : fam.relativeSimpleRoots Q) (x : Fin n → ℝ) :
    (fam.affineCorootLinear P L ec ⟨Q, k, α⟩ (fun j => (x j : ℂ))).im = 0 := by
  let ℓ := fam.affineCorootLinear P L ec ⟨Q, k, α⟩
  have hi : (ℓ (imaginarySlice x)).re = 0 := by
    change (complexParameterPairing F (fam.P Q)
      ((L Q).linear k (ec (imaginarySlice x))) (fam.relativeCoroot Q α)).re = 0
    rw [complexParameterPairing_re, hL, he, parameterRealPart_weylParameter_imaginary]
    simp
  have hx : imaginarySlice x = Complex.I • (fun j => (x j : ℂ)) := rfl
  rw [hx, map_smul, smul_eq_mul, Complex.mul_re, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, zero_sub, neg_eq_zero] at hi
  exact hi

end Langlands.Global.StandardParabolicFamily
