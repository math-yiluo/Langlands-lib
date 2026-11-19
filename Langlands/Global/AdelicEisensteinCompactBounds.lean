import Langlands.Global.AdelicEisensteinSeries
import Langlands.Global.RankinSelberg.CompactFactorDescent

/-! # Compact bounds for adelic Eisenstein terms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct Topology NumberField
open scoped CategoryTheory.MonObj TensorProduct Pointwise

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}

/-- The Iwasawa height is continuous for the topology of character evaluations. -/
theorem IsIwasawaCompact.continuous_height (hK : IsIwasawaCompact p K) :
    Continuous hK.height := by
  let includeP := map F P G p
  let B := includeP.toMonoidHom.range
  have hincludeP : IsClosedEmbedding includeP := isClosedEmbedding_map F P G p
  let e : AdelicGroupPoints F P ≃ₜ B := hincludeP.isEmbedding.toHomeomorph
  let m : B × K → AdelicGroupPoints F G := fun z => (z.1 : AdelicGroupPoints F G) * z.2
  have hm : Function.Surjective m := by
    intro g
    obtain ⟨q, k, hk, rfl⟩ := hK.exists_eq g
    exact ⟨(e q, ⟨k, hk⟩), rfl⟩
  have hquot := RankinSelbergGlobal.GaugeDescent.isQuotientMap_subgroup_mul_compact
    B K hincludeP.isClosed_range hK.isCompact hm
  apply hquot.continuous_iff.mpr
  have heq : hK.height ∘ m = characterLog F P ∘ e.symm ∘ Prod.fst := by
    funext z
    apply hK.height_eq z.2.property
    have hz : includeP (e.symm z.1) = (z.1 : AdelicGroupPoints F G) :=
      congrArg Subtype.val (e.apply_symm_apply z.1)
    change includeP (e.symm z.1) * (z.2 : AdelicGroupPoints F G) = m z
    rw [hz]
  change Continuous (hK.height ∘ m)
  rw [heq]
  exact (continuous_characterLog F P).comp (e.symm.continuous.comp continuous_fst)

/-- The Iwasawa height as a continuous map into the real character dual. -/
def IsIwasawaCompact.heightContinuousMap (hK : IsIwasawaCompact p K) :
    C(AdelicGroupPoints F G, RealCharacterDual F P) :=
  ⟨hK.height, hK.continuous_height⟩

/-- Every increment of the Iwasawa height under right translation by `g` is the height
of a product `k * g` for some `k ∈ K`. -/
theorem IsIwasawaCompact.exists_height_mul_eq_add (hK : IsIwasawaCompact p K)
    (x g : AdelicGroupPoints F G) :
    ∃ k ∈ K, hK.height (x * g) = hK.height x + hK.height (k * g) := by
  obtain ⟨q, k, hk, rfl⟩ := hK.exists_eq x
  exact ⟨k, hk, by rw [mul_assoc, hK.height_map_mul, hK.height_eq hk rfl]⟩

omit [NumberField F] [IsAffine G.X.left] [IsAffine P.X.left]
  [IsClosedImmersion p.hom.hom.left] in
/-- Taking the real part of the complex pairing gives the real parameter pairing. -/
theorem complexParameterPairing_re (lam : ComplexCharacterParameter F P)
    (H : RealCharacterDual F P) :
    (complexParameterPairing F P lam H).re =
      realParameterPairing F P (parameterRealPart F P lam) H := by
  induction lam using TensorProduct.inductionOn with
  | tmul z χ => simp [Complex.mul_re]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, Complex.add_re, hx, hy]

omit [NumberField F] [IsAffine G.X.left] [IsAffine P.X.left]
  [IsClosedImmersion p.hom.hom.left] in
/-- Evaluation at a fixed complex parameter is continuous on the real character dual. -/
theorem continuous_complexParameterPairing_apply (lam : ComplexCharacterParameter F P) :
    Continuous fun H => complexParameterPairing F P lam H := by
  induction lam using TensorProduct.inductionOn with
  | tmul z χ =>
    simp only [complexParameterPairing_tmul]
    have heval : Continuous (fun H : RealCharacterDual F P => H χ) :=
      continuous_dualEval F P χ
    exact continuous_const.mul (Complex.continuous_ofReal.comp heval)
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply]
    exact hx.add hy

omit [NumberField F] [IsAffine G.X.left] [IsAffine P.X.left]
  [IsClosedImmersion p.hom.hom.left] in
/-- The complex pairing is jointly continuous in finite parameter coordinates and the
real character dual. -/
theorem continuous_complexParameterPairing_coordinates {n : ℕ}
    (e : (Fin n → ℂ) →ₗ[ℂ] ComplexCharacterParameter F P) :
    Continuous fun z : (Fin n → ℂ) × RealCharacterDual F P =>
      complexParameterPairing F P (e z.1) z.2 := by
  classical
  have hexpand (s : Fin n → ℂ) : s = ∑ i, s i • Pi.single i 1 := by
    have hsingle (i : Fin n) : s i • Pi.single i (1 : ℂ) = Pi.single i (s i) := by
      ext j
      by_cases hij : j = i
      · subst j
        simp
      · simp [Pi.single_eq_of_ne hij]
    simp only [hsingle]
    ext j
    simp only [Finset.sum_apply, Finset.sum_pi_single, Finset.mem_univ, ite_true]
  have hpair (s : Fin n → ℂ) (H : RealCharacterDual F P) :
      complexParameterPairing F P (e s) H =
        ∑ i, s i • complexParameterPairing F P (e (Pi.single i 1)) H := by
    conv_lhs => rw [hexpand s]
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
  let f : (Fin n → ℂ) × RealCharacterDual F P → ℂ := fun z =>
    ∑ i, z.1 i • complexParameterPairing F P (e (Pi.single i 1)) z.2
  have hf : Continuous f := continuous_finsetSum _ fun i _ =>
    ((continuous_apply i).comp continuous_fst).smul
      ((continuous_complexParameterPairing_apply (e (Pi.single i 1))).comp continuous_snd)
  rw [show (fun z : (Fin n → ℂ) × RealCharacterDual F P =>
    complexParameterPairing F P (e z.1) z.2) = f from funext fun z => hpair z.1 z.2]
  exact hf

omit [IsAffine G.X.left] [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
/-- The absolute value of the height power is the exponential of the pairing with the
real part of the parameter. -/
theorem IsIwasawaCompact.norm_heightPower (hK : IsIwasawaCompact p K)
    (lam : ComplexCharacterParameter F P) (x : AdelicGroupPoints F G) :
    ‖hK.heightPower lam x‖ =
      Real.exp (realParameterPairing F P (parameterRealPart F P lam) (hK.height x)) := by
  rw [IsIwasawaCompact.heightPower, Complex.norm_exp, complexParameterPairing_re]

/-- On compact sets of right translations and parameters, the height power at `x * g`
is bounded by a constant times its value in absolute value at `x`. -/
theorem IsIwasawaCompact.exists_norm_heightPower_mul_le (hK : IsIwasawaCompact p K)
    {C : Set (AdelicGroupPoints F G)} (hC : IsCompact C) {n : ℕ}
    (e : (Fin n → ℂ) →ₗ[ℂ] ComplexCharacterParameter F P)
    {Λ : Set (Fin n → ℂ)} (hΛ : IsCompact Λ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (x : AdelicGroupPoints F G), ∀ g ∈ C, ∀ s ∈ Λ,
      ‖hK.heightPower (e s) (x * g)‖ ≤ B * ‖hK.heightPower (e s) x‖ := by
  let f : (Fin n → ℂ) × AdelicGroupPoints F G → ℝ :=
    fun z => (complexParameterPairing F P (e z.1) (hK.height z.2)).re
  have hf : Continuous f := Complex.continuous_re.comp
    ((continuous_complexParameterPairing_coordinates e).comp
      (continuous_fst.prodMk (hK.heightContinuousMap.continuous.comp continuous_snd)))
  obtain ⟨b, hb⟩ := (hΛ.prod (hK.isCompact.mul hC)).bddAbove_image hf.continuousOn
  refine ⟨Real.exp b, Real.exp_pos _, fun x g hg s hs => ?_⟩
  obtain ⟨k, hk, heq⟩ := hK.exists_height_mul_eq_add x g
  have hbkg : f (s, k * g) ≤ b := hb ⟨(s, k * g), ⟨hs, ⟨k, hk, g, hg, rfl⟩⟩, rfl⟩
  rw [hK.norm_heightPower, hK.norm_heightPower, heq, map_add, Real.exp_add, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
  apply Real.exp_le_exp.mpr
  rw [← complexParameterPairing_re]
  exact hbkg

end Langlands.Global.AdelicGroupPoints
