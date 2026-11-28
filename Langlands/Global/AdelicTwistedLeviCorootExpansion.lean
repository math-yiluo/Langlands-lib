import Langlands.Global.AdelicTruncatedEisensteinPairing
import Langlands.Global.AdelicWeakConstantTermPairingPolynomials
import Langlands.Global.AdelicNestedSplitComponents
import Langlands.Global.AdelicEisensteinCentralCovariance
import Langlands.Global.AdelicInducedInnerProductIntegrable
import Langlands.GroupScheme.Rational.StandardParabolicEndpointsProof

/-! # Coroot expansions of finite sums of twisted Levi pairings -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

private theorem exists_coordinatePolynomial {Index W : Type*} [Fintype Index] [AddCommGroup W]
    [Module ℝ W] (v : Index → W) (b : W) {n : ℕ} {f : W → ℂ}
    (hf : f ∈ polynomialFunctions W n) :
    ∃ coeff : MvPolynomial Index ℂ, ∀ c : Index → ℝ,
      MvPolynomial.eval (fun i => (c i : ℂ)) coeff = f (b + ∑ i, c i • v i) := by
  classical
  refine Submodule.span_induction (p := fun f _ => ∃ coeff : MvPolynomial Index ℂ, ∀ c : Index → ℝ,
    MvPolynomial.eval (fun i => (c i : ℂ)) coeff = f (b + ∑ i, c i • v i)) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨k, _, l, rfl⟩
    refine ⟨∏ j, (MvPolynomial.C (l j b : ℂ) +
      ∑ i, MvPolynomial.C (l j (v i) : ℂ) * MvPolynomial.X i), fun c => ?_⟩
    simp only [map_prod, map_add, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
      map_smul, smul_eq_mul, Complex.ofReal_add, Complex.ofReal_sum, Complex.ofReal_mul, mul_comm]
  · exact ⟨0, fun _ => map_zero _⟩
  · rintro f g _ _ ⟨coeff, hp⟩ ⟨q, hq⟩
    exact ⟨coeff + q, fun c => by rw [map_add, hp, hq]; rfl⟩
  · rintro s f _ ⟨coeff, hp⟩
    exact ⟨MvPolynomial.C s * coeff, fun c => by rw [map_mul, MvPolynomial.eval_C, hp]; rfl⟩

namespace StandardParabolicFamily

open GroupScheme AdelicGroupPoints

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)
  {K : Subgroup (AdelicGroupPoints F G)} {Q : StandardIndex F G fam.i fam.ν}

local notation "Forms" => (AdelicGroupPoints F G → ℂ)
local notation "Param" => ComplexCharacterParameter F (fam.P Q)
local notation "Poly" => MvPolynomial (fam.relativeSimpleRoots Q) ℂ

private theorem exists_centralPoint_lift (z : fam.positiveSplitComponent fam.top) :
    ∃ a : fam.positiveSplitComponent Q,
      map F (fam.P Q) G (fam.p Q) a.val = fam.centralPoint z ∧
      (∀ g, Commute (fam.centralPoint z) g) ∧ fam.halfModulus Q a.val = 1 := by
  have hr : (⊤ : SubgroupFunctor G).IsRepresentedBy (fam.l fam.top ≫ fam.p fam.top) := by
    have hp := standardParabolicEndpoints F G fam.connectedReductive fam.T fam.i fam.maximalSplit
      fam.ν fam.generic
    have htop := (fam.isCompatible fam.top).levi_eq.trans hp.2.2.2.1
    rw [← htop]
    exact ((fam.isCompatible fam.top).levi.isClosedSubgroup.comp
      (fam.isCompatible fam.top).parabolic.isClosedSubgroup).isRepresentedBy_range
  let i := fam.a fam.top ≫ fam.l fam.top ≫ fam.p fam.top
  have hi : IsCentral i := by
    have h := (fam.isCompatible fam.top).splitComponent.isCentralSplitTorus.isCentral
    simpa only [i, hr.topIso_hom] using h.comp_iso hr.topIso
  let h := fam.le_top Q
  let f := fam.nestedSplitComponentHom h
  let j := CommGroupScheme.groupHom f ≫ fam.a Q ≫ fam.l Q
  have hj : j ≫ fam.p Q = i := by
    have he : j ≫ fam.nestedParabolicHom h = fam.a fam.top ≫ fam.l fam.top := by
      simpa only [j, f, Category.assoc] using fam.nestedSplitComponentHom_parabolic_comp h
    rw [← fam.nestedParabolicHom_comp h, ← Category.assoc, he, Category.assoc]
  obtain ⟨t, ht, hz⟩ := z.property
  let a := map F (fam.A fam.top).toGrp (fam.P Q) j t
  have ha : a ∈ fam.positiveSplitComponent Q := by
    let tQ := map F (fam.A fam.top).toGrp (fam.A Q).toGrp (CommGroupScheme.groupHom f) t
    refine ⟨tQ, PositiveRealTorus.map_intrinsicSubgroup_le F (fam.A fam.top) (fam.A Q) f
      ⟨t, ht, rfl⟩, ?_⟩
    change map F (fam.A Q).toGrp (fam.P Q) (fam.a Q ≫ fam.l Q)
      (map F (fam.A fam.top).toGrp (fam.A Q).toGrp (CommGroupScheme.groupHom f) t) = a
    rw [← map_comp_apply_of_hom]
  have hm : map F (fam.A fam.top).toGrp G i t = fam.centralPoint z := by
    rw [centralPoint, ← hz]
    change map F (fam.A fam.top).toGrp G i t =
      map F (fam.P fam.top) G (fam.p fam.top)
        (map F (fam.A fam.top).toGrp (fam.P fam.top) (fam.a fam.top ≫ fam.l fam.top) t)
    rw [← map_comp_apply_of_hom, Category.assoc]
  refine ⟨⟨a, ha⟩, ?_, fun g => ?_, ?_⟩
  · change map F (fam.P Q) G (fam.p Q)
      (map F (fam.A fam.top).toGrp (fam.P Q) j t) = _
    rw [← map_comp_apply_of_hom, hj, hm]
  · rw [← hm]
    exact commute_of_mem_center (hi _ t) g
  · have hAT := (fam.isCompatible fam.top).splitComponent.isCentralSplitTorus
    let : IsAffineHom (fam.A fam.top).toGrp.X.hom := hAT.isSplitSubtorus.1.isAffineHom
    let : IsAffine (fam.A fam.top).toGrp.X.left :=
      isAffine_of_isAffineHom (fam.A fam.top).toGrp.X.hom
    let := (fam.isCompatible Q).parabolic.isClosedSubgroup.mono
    let : Mono (fam.p Q).hom.hom := Over.mono_of_mono_left _
    change parameterPower F (fam.P Q) (halfModulusParameter F (fam.P Q))
      (map F (fam.A fam.top).toGrp (fam.P Q) j t) = 1
    exact parameterPower_halfModulus_map_of_isCentral (hj.symm ▸ hi) t

private theorem parameterPower_conj_of_unitary {mu : Param}
    (hmu : parameterRealPart F (fam.P Q) mu = 0) (x : AdelicGroupPoints F (fam.P Q)) :
    (starRingEnd ℂ) (parameterPower F (fam.P Q) mu x) =
      parameterPower F (fam.P Q) (-mu) x := by
  unfold parameterPower
  rw [← Complex.exp_conj, map_neg, LinearMap.neg_apply]
  congr 1
  have hRe : (complexParameterPairing F (fam.P Q) mu (characterLog F (fam.P Q) x)).re = 0 := by
    rw [complexParameterPairing_re, hmu, map_zero, LinearMap.zero_apply]
  exact Complex.ext (by simp [hRe]) (by simp)

private theorem parameterPower_eq_coroot_exp (lam : Param) (x : AdelicGroupPoints F (fam.P Q))
    (c : fam.relativeSimpleRoots Q → ℝ)
    (hc : characterLog F (fam.P Q) x = ∑ α, c α • fam.relativeCoroot Q α) :
    parameterPower F (fam.P Q) lam x =
      Complex.exp (∑ α, (c α : ℂ) * fam.corootValue Q lam α) := by
  simp only [parameterPower, hc, map_sum, corootValue, map_smul, Complex.real_smul]

attribute [local instance] isClosedImmersion_p

/-- The normalized pairing of a twisted inducing form and a unitary exponent component
has exponent `lam - mu`. The common central translate contributes a shift of the polynomial
and a scalar character value at the lifted central point. -/
theorem normalizedPairing_twistedComponent_corootExpansion
    (hKQ : IsIwasawaCompact (fam.p Q) K) (z : fam.positiveSplitComponent fam.top)
    (lam mu : Param) {φ ψ : Forms}
    (hφ : IsSplitComponentEquivariant (fam.p Q) (fam.l Q) φ)
    (hψ : fam.HasExponent Q mu ψ) (hmu : parameterRealPart F (fam.P Q) mu = 0)
    (hint : ∀ x ∈ fam.positiveSplitComponent Q,
      Integrable (fam.squareIntegrablePairingIntegrand K Q x φ ψ)
        (fam.squareIntegrablePairingMeasure K hKQ.isCompact Q)) :
    ∃ coeff : Poly, ∀ x ∈ fam.positiveSplitComponent Q, ∀ c : fam.relativeSimpleRoots Q → ℝ,
      characterLog F (fam.P Q) x = ∑ α, c α • fam.relativeCoroot Q α →
      Integrable (fam.squareIntegrablePairingIntegrand K Q x
        (fam.centralTranslate z (hKQ.parameterTwist φ lam)) (fam.centralTranslate z ψ))
          (fam.squareIntegrablePairingMeasure K hKQ.isCompact Q) ∧
      fam.normalizedPairing K hKQ.isCompact Q x
          (fam.centralTranslate z (hKQ.parameterTwist φ lam)) (fam.centralTranslate z ψ) =
        Complex.exp (∑ α, (c α : ℂ) * fam.corootValue Q (lam - mu) α) *
          MvPolynomial.eval (fun α => (c α : ℂ)) coeff := by
  obtain ⟨a, ha, hcomm, hhalf⟩ := fam.exists_centralPoint_lift (Q := Q) z
  obtain ⟨n, q, hq, hpair⟩ := fam.squareIntegrablePairing_polynomial_of_integrable Q K
    hKQ.isCompact hφ hψ hint
  obtain ⟨r, hr⟩ := exists_coordinatePolynomial (fam.relativeCoroot Q)
    (characterLog F (fam.P Q) a.val) hq
  refine ⟨MvPolynomial.C (parameterPower F (fam.P Q) (lam - mu) a.val) * r,
    fun x hx c hc => ?_⟩
  let y := x * a.val
  have hy : y ∈ fam.positiveSplitComponent Q := (fam.positiveSplitComponent Q).mul_mem hx a.property
  have hIntEq : fam.squareIntegrablePairingIntegrand K Q x
      (fam.centralTranslate z (hKQ.parameterTwist φ lam)) (fam.centralTranslate z ψ) =
      fun w => parameterPower F (fam.P Q) lam y * fam.squareIntegrablePairingIntegrand K Q y φ ψ w := by
    funext w
    let m := (w.2.out : normOneSubgroup F (fam.M Q))
    let k := (w.1 : AdelicGroupPoints F G)
    let xG (p : AdelicGroupPoints F (fam.P Q)) := map F (fam.P Q) G (fam.p Q) p
    let mG := map F (fam.M Q) G (fam.l Q ≫ fam.p Q) m.val
    have hmove : (xG x * mG * k) * fam.centralPoint z = xG y * mG * k := by
      rw [mul_assoc (xG x) mG k, mul_assoc (xG x) (mG * k), ← (hcomm (mG * k)).eq,
        ← mul_assoc, ← ha]
      simp only [xG, y, map_mul, mul_assoc]
    have hheight : hKQ.height (xG y * mG * k) = characterLog F (fam.P Q) y := by
      dsimp only [xG, mG]
      rw [mul_assoc, hKQ.height_map_mul, map_comp_apply_of_hom, hKQ.height_map_mul,
        InducedInnerProductIntegrable.characterLog_map_of_mem_normOne (fam.l Q) m.property,
        hKQ.height_of_mem w.1.property, add_zero, add_zero]
    change hKQ.parameterTwist φ lam ((xG x * mG * k) * fam.centralPoint z) *
      (starRingEnd ℂ) (ψ ((xG x * mG * k) * fam.centralPoint z)) =
      parameterPower F (fam.P Q) lam y * (φ (xG y * mG * k) * (starRingEnd ℂ) (ψ (xG y * mG * k)))
    rw [hmove, IsIwasawaCompact.parameterTwist, IsIwasawaCompact.heightPower, hheight, parameterPower]
    ring
  refine ⟨hIntEq.symm ▸ (hint y hy).const_mul _, ?_⟩
  have hMod : parameterPower F (fam.P Q) (modulusParameter F (fam.P Q)) y =
      fam.halfModulus Q x ^ 2 := by
    have hHalfY : fam.halfModulus Q y = fam.halfModulus Q x := by
      change fam.halfModulus Q (x * a.val) = _
      rw [halfModulus, parameterPower_mul]
      change fam.halfModulus Q x * fam.halfModulus Q a.val = _
      rw [hhalf, mul_one]
    rw [← hHalfY, pow_two, halfModulus, ← parameterPower_add, halfModulusParameter,
      ← TensorProduct.add_tmul]
    norm_num [modulusParameter]
  have hne : fam.halfModulus Q x ≠ 0 := Complex.exp_ne_zero _
  have hlog : characterLog F (fam.P Q) y =
      characterLog F (fam.P Q) a.val + ∑ α, c α • fam.relativeCoroot Q α := by
    rw [characterLog_mul, hc, add_comm]
  calc
    _ = parameterPower F (fam.P Q) (lam - mu) y * q (characterLog F (fam.P Q) y) := by
      rw [normalizedPairing, hIntEq, integral_const_mul, hpair y hy, hMod,
        fam.parameterPower_conj_of_unitary hmu, sub_eq_add_neg, parameterPower_add]
      field_simp [hne]
    _ = _ := by
      rw [show parameterPower F (fam.P Q) (lam - mu) y =
        parameterPower F (fam.P Q) (lam - mu) x * parameterPower F (fam.P Q) (lam - mu) a.val
        from parameterPower_mul _ _ _ _, fam.parameterPower_eq_coroot_exp _ _ c hc, hlog,
        ← hr c, map_mul, MvPolynomial.eval_C, mul_assoc]

/-- The two finite label sets retain one term for every pair of an inducing twist and a
unitary component, even when the difference parameters coincide. -/
def TwistedLeviPairingCorootExpansionStatement
    (hKQ : IsIwasawaCompact (fam.p Q) K) (z : fam.positiveSplitComponent fam.top)
    {I J : Type*} (s : Finset I) (t : Finset J) (lam : I → Param) (mu : J → Param)
    (φ : I → Forms) (ψ : J → Forms) : Prop :=
  (∀ i ∈ s, IsSplitComponentEquivariant (fam.p Q) (fam.l Q) (φ i)) →
  (∀ j ∈ t, fam.HasExponent Q (mu j) (ψ j) ∧ parameterRealPart F (fam.P Q) (mu j) = 0) →
  (∀ i ∈ s, ∀ j ∈ t, ∀ x ∈ fam.positiveSplitComponent Q,
    Integrable (fam.squareIntegrablePairingIntegrand K Q x (φ i) (ψ j))
      (fam.squareIntegrablePairingMeasure K hKQ.isCompact Q)) →
  ∃ poly : I × J → Poly, ∀ x ∈ fam.positiveSplitComponent Q, ∀ c : fam.relativeSimpleRoots Q → ℝ,
    characterLog F (fam.P Q) x = ∑ α, c α • fam.relativeCoroot Q α →
    (∀ i ∈ s, Integrable (fam.squareIntegrablePairingIntegrand K Q x
      (fam.centralTranslate z (hKQ.parameterTwist (φ i) (lam i)))
      (fam.centralTranslate z (∑ j ∈ t, ψ j))) (fam.squareIntegrablePairingMeasure K hKQ.isCompact Q)) ∧
    ∑ i ∈ s, fam.normalizedPairing K hKQ.isCompact Q x
        (fam.centralTranslate z (hKQ.parameterTwist (φ i) (lam i)))
        (fam.centralTranslate z (∑ j ∈ t, ψ j)) =
      ∑ ij ∈ s ×ˢ t,
        Complex.exp (∑ α, (c α : ℂ) * fam.corootValue Q (lam ij.1 - mu ij.2) α) *
          MvPolynomial.eval (fun α => (c α : ℂ)) (poly ij)

/-- Integral additivity and the component expansion give the finite labelled formula. -/
theorem normalizedPairing_finsetSum_corootExpansion
    (hKQ : IsIwasawaCompact (fam.p Q) K) (z : fam.positiveSplitComponent fam.top)
    {I J : Type*} (s : Finset I) (t : Finset J) (lam : I → Param) (mu : J → Param)
    (φ : I → Forms) (ψ : J → Forms) :
    fam.TwistedLeviPairingCorootExpansionStatement hKQ z s t lam mu φ ψ := by
  classical
  intro hφ hψ hint
  choose coeff hcoeff using fun (i : s) (j : t) =>
    fam.normalizedPairing_twistedComponent_corootExpansion hKQ z (lam i) (mu j) (hφ i i.property)
      (hψ j j.property).1 (hψ j j.property).2 (hint i i.property j j.property)
  let poly (ij : I × J) : Poly :=
    if hi : ij.1 ∈ s then if hj : ij.2 ∈ t then coeff ⟨ij.1, hi⟩ ⟨ij.2, hj⟩ else 0 else 0
  refine ⟨poly, fun x hx c hc => ?_⟩
  let f := fun i => fam.centralTranslate z (hKQ.parameterTwist (φ i) (lam i))
  let g := fun j => fam.centralTranslate z (ψ j)
  let measure := fam.squareIntegrablePairingMeasure K hKQ.isCompact Q
  have he (i : I) :
      fam.squareIntegrablePairingIntegrand K Q x (f i) (fam.centralTranslate z (∑ j ∈ t, ψ j)) =
        fun w => ∑ j ∈ t, fam.squareIntegrablePairingIntegrand K Q x (f i) (g j) w := by
    funext w
    simp only [squareIntegrablePairingIntegrand, centralTranslate, Finset.sum_apply, map_sum,
      Finset.mul_sum, g]
  have hInt (i) (hi : i ∈ s) (j) (hj : j ∈ t) :
      Integrable (fam.squareIntegrablePairingIntegrand K Q x (f i) (g j)) measure :=
    (hcoeff ⟨i, hi⟩ ⟨j, hj⟩ x hx c hc).1
  refine ⟨fun i hi => (he i).symm ▸ integrable_finsetSum t (hInt i hi), ?_⟩
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i hi
  change fam.normalizedPairing K hKQ.isCompact Q x (f i) (fam.centralTranslate z (∑ j ∈ t, ψ j)) = _
  rw [normalizedPairing, he, integral_finsetSum t (hInt i hi), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  change fam.normalizedPairing K hKQ.isCompact Q x (f i) (g j) = _
  simpa only [poly, dite_eq_left hi, dite_eq_left hj] using (hcoeff ⟨i, hi⟩ ⟨j, hj⟩ x hx c hc).2

end StandardParabolicFamily

end Langlands.Global
