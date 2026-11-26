import Langlands.Automorphic.AssociatedGammaAutomorphicTwist
import Langlands.Automorphic.AssociatedPresentationSpectrum
import Langlands.Automorphic.ContragredientSphericalSpectrum
import Langlands.Automorphic.ContragredientUniqueness
import Langlands.Automorphic.CuspidalAllLocalIrreduciblePresentationProof
import Langlands.Automorphic.CuspidalOperatorUnitaryMultiplicityOneReduction
import Langlands.Automorphic.DeterminantMultipleSpectrum
import Langlands.Automorphic.HeckeTwist.LocalSphericalSpectrum
import Langlands.Global.Factors.CuspidalPairFiniteLayer
import Langlands.Global.Factors.CuspidalNormPowerTwist
import Langlands.Global.Factors.CuspidalPartialPairOrderOneComparison
import Langlands.Global.Factors.CuspidalPartialPairOrderOneStatement
import Langlands.Global.RankinSelberg.EqualEulerLocalSum

/-! # Order at one of the partial cuspidal pair L-function from the completed poles

`CuspidalPartialPairOrderOneFromPairPole` is the implication from the completed pair pole
theorem and partial boundary nonvanishing to `CuspidalPartialPairOrderOneStatement`; this
file proves it as `cuspidalPartialPairOrderOne_of_pairPole`. See the paired Markdown. -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u uQ

namespace Langlands.Global

open Automorphic
open NumberField CompletionPadic
open CuspidalPairPoles
open CuspidalPairFunctionalEquation
open CuspidalPairBoundaryNonvanishing
open Langlands.ClassFieldTheory.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)

namespace CuspidalPartialPairOrderOne

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

local instance (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance {n : ℕ} (V : OperatorRealization F n) : AddCommGroup V.Space :=
  Submodule.addCommGroup _
local instance {n : ℕ} {v : FinitePlace F} (V : LocalRealization F n v) :
    AddCommGroup V.Space :=
  Submodule.addCommGroup _

section Normalization

variable {r : ℕ} {T U : CuspidalOperatorRealization F r}

/-- Triviality of the normalized realization determines the original
central character on the one-parameter split centre. -/
private theorem centralCharacter_splitCentre {ω : HeckeCharacter F}
    (hω : T.HasCentralCharacter ω) {a : ℂ}
    (hT : IsTrivialOnSplitCentre (T.heckeDeterminantTwist (HeckeCharacter.normPower F (-a))))
    (y : ℝ) :
    (centralIdeleCharacter F ω (PositiveRealIdeles.full F (PositiveRealTorus.expUnit y)) : ℂ) =
      Complex.exp (a * ((Module.finrank ℚ F : ℂ) * (r + 1)) * y) := by
  let χ := HeckeCharacter.normPower F (-a)
  let T₀ := T.heckeDeterminantTwist χ
  let z := PositiveRealIdeles.full F (PositiveRealTorus.expUnit y)
  have hω₀ : T₀.HasCentralCharacter (χ ^ (r + 1) * ω) := by
    change (T.realization.heckeDeterminantTwist χ).toFiniteRealization.HasCentralCharacter _
    rw [OperatorRealization.toFiniteRealization_heckeDeterminantTwist]
    exact T.realization.toFiniteRealization.heckeDeterminantTwist_hasCentralCharacter χ ω hω
  obtain ⟨f, x, hx⟩ := T₀.realization.exists_evaluate_ne_zero T₀.irreducible
  have he := T₀.realization.centralCharacter_evaluate _ hω₀ f z x
  rw [hT z (isPositiveArchimedeanScalar_positiveRealIdeles _) f x] at he
  have h₁ : (centralIdeleCharacter F (χ ^ (r + 1) * ω) z : ℂ) = 1 :=
    mul_right_cancel₀ hx (he.symm.trans (one_mul _).symm)
  change (((χ ^ (r + 1) * ω) (ideleClassMap F z) : ℂˣ) : ℂ) = 1 at h₁
  rw [ContinuousMonoidHom.mul_apply, ContinuousMonoidHom.pow_apply,
    Units.val_mul, Units.val_pow_eq_pow_val] at h₁
  change (centralIdeleCharacter F (HeckeCharacter.normPower F (-a)) z : ℂ) ^ (r + 1) *
    (centralIdeleCharacter F ω z : ℂ) = 1 at h₁
  rw [NormPowerTwist.normPower_full_expUnit, ← Complex.exp_nat_mul] at h₁
  have hexponent :
      ((r + 1 : ℕ) : ℂ) * (-a * (((Module.finrank ℚ F : ℝ) * y : ℝ) : ℂ)) =
        -(a * ((Module.finrank ℚ F : ℂ) * (r + 1)) * y) := by
    push_cast
    ring
  rw [hexponent] at h₁
  apply mul_left_cancel₀ (Complex.exp_ne_zero _)
  rw [h₁, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]

/-- A split-centre normalizing norm power for a unitary cusp is imaginary. -/
theorem normalizer_re_eq_zero {ω : HeckeCharacter F}
    (hω : T.HasCentralCharacter ω) (hunit : ∀ z, ‖(ω z : ℂ)‖ = 1) {a : ℂ}
    (hT : IsTrivialOnSplitCentre (T.heckeDeterminantTwist (HeckeCharacter.normPower F (-a)))) :
    a.re = 0 := by
  have h := congrArg norm (centralCharacter_splitCentre hω hT 1)
  change ‖(ω (ideleClassMap F (PositiveRealIdeles.full F (PositiveRealTorus.expUnit 1))) : ℂ)‖ =
    ‖Complex.exp (a * ((Module.finrank ℚ F : ℂ) * (r + 1)) * (↑(1 : ℝ) : ℂ))‖ at h
  rw [hunit, Complex.ofReal_one, mul_one, Complex.norm_exp, ← Real.exp_zero] at h
  have he := Real.exp_injective h
  simp only [Complex.mul_re, Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
    Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, mul_zero, zero_mul,
    add_zero, sub_zero] at he
  have hd : 0 < (Module.finrank ℚ F : ℝ) := Nat.cast_pos.mpr Module.finrank_pos
  have hr : 0 < (r : ℝ) + 1 := by positivity
  exact (mul_eq_zero.mp he.symm).resolve_right (mul_ne_zero hd.ne' hr.ne')

omit [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] in
private theorem exponent_eq_zero {z : ℂ} (h : ∀ y : ℝ, Complex.exp (z * y) = 1) :
    z = 0 := by
  have he : (fun y : ℝ => Complex.exp (z * y)) = fun _ => (1 : ℂ) := funext h
  have hd : HasDerivAt (fun y : ℝ => Complex.exp (z * y)) z 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul z).cexp
  rw [he] at hd
  exact hd.unique (hasDerivAt_const (0 : ℝ) (1 : ℂ))

/-- Opposite central characters force opposite exponents in the actual dual case. -/
private theorem normalizer_add_eq_zero_of_contragredient
    (hT : HasUnitaryCentralCharacter T) (hU : HasUnitaryCentralCharacter U)
    (hd : T.realization.IsContragredientOf U.realization) {a b : ℂ}
    (ha : IsTrivialOnSplitCentre (T.heckeDeterminantTwist (HeckeCharacter.normPower F (-a))))
    (hb : IsTrivialOnSplitCentre (U.heckeDeterminantTwist (HeckeCharacter.normPower F (-b)))) :
    a + b = 0 := by
  obtain ⟨ω, _, hω⟩ := hT
  obtain ⟨ω', hω'u, hω'⟩ := hU
  have hconj := RankinSelbergGlobal.SelfPair.conjugate_isContragredientOf U ⟨ω', hω'u, hω'⟩
  obtain ⟨e⟩ := OperatorRealization.IsContragredientOf.nonempty_equivalence hconj hd
  have hωc := e.hasCentralCharacter (OperatorRealization.HasCentralCharacter.conjugate _ hω')
  obtain ⟨_, _, huniq⟩ := T.realization.existsUnique_hasCentralCharacter T.irreducible
  have hchar : conjCharacter F ω' = ω := (huniq _ hωc).trans (huniq _ hω).symm
  let d : ℂ := (Module.finrank ℚ F : ℂ) * (r + 1)
  have hexp : ∀ y : ℝ, Complex.exp (((a + b) * d) * y) = 1 := by
    intro y
    let z := PositiveRealIdeles.full F (PositiveRealTorus.expUnit y)
    rw [add_mul, add_mul, Complex.exp_add, ← centralCharacter_splitCentre hω ha y,
      ← centralCharacter_splitCentre hω' hb y, ← hchar]
    change (conjCharacter F ω' (ideleClassMap F z) : ℂ) * (ω' (ideleClassMap F z) : ℂ) = 1
    rw [conjCharacter_apply, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hω'u]
    norm_num
  have hdne : d ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.mpr Module.finrank_pos.ne')
    (by exact_mod_cast Nat.succ_ne_zero r)
  exact (mul_eq_zero.mp (exponent_eq_zero hexp)).resolve_right hdne

omit [CompactSpace (AdeleQuotient F)] in
private theorem normPower_neg (a : ℂ) :
    HeckeCharacter.normPower F (-a) = (HeckeCharacter.normPower F a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← HeckeCharacter.normPower_add, neg_add_cancel, HeckeCharacter.normPower_zero]

/-- Applying mutually inverse determinant twists preserves and reflects the
actual contragredient relation. -/
private theorem contragredient_iff_twists {a b : ℂ} (hab : a + b = 0) :
    (T.heckeDeterminantTwist (HeckeCharacter.normPower F (-a))).realization.IsContragredientOf
      (U.heckeDeterminantTwist (HeckeCharacter.normPower F (-b))).realization ↔
        T.realization.IsContragredientOf U.realization := by
  have hb : b = -a := eq_neg_of_add_eq_zero_right hab
  subst b
  let χ := HeckeCharacter.normPower F a
  change (T.realization.heckeDeterminantTwist (HeckeCharacter.normPower F (-a))).IsContragredientOf
    (U.realization.heckeDeterminantTwist (HeckeCharacter.normPower F (- -a))) ↔ _
  rw [neg_neg, normPower_neg, show HeckeCharacter.normPower F a = χ from rfl]
  constructor
  · intro hd
    simpa only [inv_inv, OperatorRealization.heckeDeterminantTwist_heckeDeterminantTwist_inv]
      using hd.heckeDeterminantTwist_inv χ⁻¹
  · intro hd
    exact hd.heckeDeterminantTwist_inv χ

end Normalization

section ShiftedDual

variable {r t : ℕ} {T : CuspidalOperatorRealization F r} {U : CuspidalOperatorRealization F t}

/-- The normalized completed pole condition at the translated point is equivalent
to the original actual contragredient condition. -/
theorem isDual_iff_shift_eq_zero_and_normalizedDual
    (hT : HasUnitaryCentralCharacter T) (hU : HasUnitaryCentralCharacter U) {a b : ℂ}
    (ha : IsTrivialOnSplitCentre (T.heckeDeterminantTwist (HeckeCharacter.normPower F (-a))))
    (hb : IsTrivialOnSplitCentre (U.heckeDeterminantTwist (HeckeCharacter.normPower F (-b)))) :
    (∃ hrt : r = t, OperatorRealization.IsContragredientOf (n := t + 1)
      (hrt ▸ T.realization) U.realization) ↔
    a + b = 0 ∧ ∃ hrt : r = t, OperatorRealization.IsContragredientOf (n := t + 1)
      (hrt ▸ (T.heckeDeterminantTwist (HeckeCharacter.normPower F (-a))).realization)
        (U.heckeDeterminantTwist (HeckeCharacter.normPower F (-b))).realization := by
  constructor
  · rintro ⟨hrt, hd⟩
    subst t
    have hab := normalizer_add_eq_zero_of_contragredient hT hU hd ha hb
    exact ⟨hab, rfl, (contragredient_iff_twists hab).mpr hd⟩
  · rintro ⟨hab, hrt, hd⟩
    subst t
    exact ⟨rfl, (contragredient_iff_twists hab).mp hd⟩

end ShiftedDual

section Average

open MeasureTheory CompactSplitting

universe uG uV uW

/-- If intertwiner images span the target, a nonzero compact-open fixed vector
in the target requires one in the source. -/
private theorem fixedVectors_ne_bot_of_isotypicPart_eq_top
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (μ : Measure G) [μ.IsHaarMeasure]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (σ : Representation ℂ G W) (hσ : IsSmooth σ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (htop : isotypicPart ρ σ = ⊤)
    (w : fixedVectors σ K.toSubgroup) (hw : w ≠ 0) :
    fixedVectors ρ K.toSubgroup ≠ ⊥ := by
  intro hbot
  let A := Hecke.fixedProjection μ σ hσ K hK
  have hker : isotypicPart ρ σ ≤ LinearMap.ker A := by
    apply iSup_le
    rintro f _ ⟨x, rfl⟩
    have hx : Hecke.fixedProjection μ ρ hρ K hK x = 0 := by
      apply Subtype.ext
      exact (Submodule.eq_bot_iff _).mp hbot _
        (Hecke.fixedProjection μ ρ hρ K hK x).property
    change Hecke.fixedProjection μ σ hσ K hK (f x) = 0
    rw [← Hecke.fixedProjection_intertwiner μ ρ hρ K hK hσ f, hx, map_zero]
  rw [htop, top_le_iff] at hker
  have hAw : (w : W) ∈ LinearMap.ker A := by rw [hker]; exact Submodule.mem_top
  exact hw ((Hecke.fixedProjection_fixed μ σ hσ K hK w).symm.trans
    (LinearMap.mem_ker.mp hAw))

end Average

section Spherical

open FiniteAdelicGL

variable {r : ℕ} {T : CuspidalOperatorRealization F r} (v : FinitePlace F)

local instance : TopologicalSpace (FiniteLocalGL F (r + 1) v) :=
  (padicField v).canonicalGeneralLinearTopology (r + 1)
local instance : IsTopologicalGroup (FiniteLocalGL F (r + 1) v) :=
  (padicField v).canonicalGeneralLinearTopologicalGroup (r + 1)
local instance : MeasurableSpace (FiniteLocalGL F (r + 1) v) := borel _
local instance : BorelSpace (FiniteLocalGL F (r + 1) v) := ⟨rfl⟩

/-- The supplied spectrum holds on the auxiliary component wherever the
supplied presentation has a spectrum. -/
private theorem localSpectrum
    (P : CuspidalSpectralPresentation.{u, uQ} T) (Q : CuspidalSpectralPresentation.{u, u} T)
    (hv : v ∉ P.exceptional) :
    (Q.localComponent v).HasSphericalHeckeSpectrum (P.spectralSystem.eigenvalues v hv) := by
  let μ := Unramified.sphericalHaar (padicField v) r
  have : μ.IsHaarMeasure := Unramified.sphericalHaar_isHaar (padicField v) r
  let K := Unramified.sphericalOpenSubgroup (padicField v) r
  obtain ⟨w, hw⟩ := P.exists_spherical_ne_zero v hv
  refine ⟨?_, P.localComponent_standardHeckeOperator_eq v Q _ (P.hasSpectrum v hv)⟩
  exact fixedVectors_ne_bot_of_isotypicPart_eq_top μ
    (Q.localComponent v).representation (Q.localComponent v).isSmooth_canonical
    (T.realization.localRepresentation v) (T.realization.localRepresentation_isSmooth_canonical v)
    K (Unramified.sphericalOpenSubgroup_isCompact (padicField v) r)
    (Q.localComponent_isotypicPart_eq_top v) w hw

/-- The auxiliary presentation of the normalized cusp carries the original
spectrum multiplied by the norm power's uniformizer value. -/
private theorem twistedLocalSpectrum
    (P : CuspidalSpectralPresentation.{u, uQ} T) (Q : CuspidalSpectralPresentation.{u, u} T)
    (hQ : HasIrreducibleAdmissibleComponents Q) (hv : v ∉ P.exceptional) (a : ℂ) :
    let χ := HeckeCharacter.normPower F (-a)
    let h := Q.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents χ hQ
    Unramified.HasSphericalSpectrum (padicField v)
      (((Q.heckeDeterminantTwist χ).localComponent v).padicObject (h v).1 (h v).2)
      (Unramified.Eigenvalues.scale (χ.finiteUniformizerValue v) (P.spectralSystem.eigenvalues v hv)) := by
  dsimp only
  let χ := HeckeCharacter.normPower F (-a)
  let A := (Q.localComponent v).heckeDeterminantTwist χ
  let B := (Q.heckeDeterminantTwist χ).localComponent v
  let e := Q.heckeDeterminantTwistLocalComponentEquiv χ v
  have hI : A.IsIrreducible :=
    ((Q.localComponent v).heckeDeterminantTwist_isIrreducible_iff χ).mpr (hQ v).1
  have hA : A.IsAdmissible :=
    ((Q.localComponent v).heckeDeterminantTwist_isAdmissible_iff χ).mpr (hQ v).2
  have hB := Q.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents χ hQ v
  have hs := (Q.localComponent v).hasSphericalHeckeSpectrum_heckeDeterminantTwist χ
    (χ.finiteLocalDeterminant_eq_one_of_isUnramifiedAt (r + 1) v
      (HeckeCharacter.normPower_isUnramifiedAt F (-a) v)) _ (localSpectrum v P Q hv)
  apply (Unramified.sphericalHeckeComparison (padicField v) r _ _).mpr
  exact (Unramified.hasSphericalHeckeSpectrum_iff_of_equiv (padicField v)
    (A := A.padicObject hI hA) (B := B.padicObject hB.1 hB.2) e.symm _).mp hs

end Spherical

section EulerFactors

omit [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] in
private theorem eval_pairEulerPolynomial_scale {n m : ℕ}
    (a : Unramified.Eigenvalues n) (b : Unramified.Eigenvalues m) (α β : ℂˣ) (x : ℂ) :
    (pairEulerPolynomial (a.scale α) (b.scale β)).eval x =
      (pairEulerPolynomial a b).eval ((α : ℂ) * (β : ℂ) * x) := by
  obtain ⟨a, rfl⟩ := Unramified.Eigenvalues.ofTuple_surjective n a
  obtain ⟨b, rfl⟩ := Unramified.Eigenvalues.ofTuple_surjective m b
  simp only [Unramified.Eigenvalues.scale_ofTuple,
    RankinSelbergGlobal.EqualEulerLocal.eval_pairEulerPolynomial_ofTuple, Units.val_mul]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  ring

omit [CompactSpace (AdeleQuotient F)] in
private theorem scaled_spectralPoint (v : FinitePlace F) (a b s : ℂ) :
    ((HeckeCharacter.normPower F (-a)).finiteUniformizerValue v : ℂ) *
      ((HeckeCharacter.normPower F (-b)).finiteUniformizerValue v : ℂ) *
      RankinSelberg.spectralPoint (residueCardinality v) (s + (a + b)) =
    RankinSelberg.spectralPoint (residueCardinality v) s := by
  have hq : (residueCardinality v : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by have := CuspidalPairEulerConvergence.two_le_residueCardinality v; omega)
  simp only [NormPowerTwist.finiteUniformizerValue_normPower, neg_neg, RankinSelberg.spectralPoint]
  rw [← Complex.cpow_add _ _ hq, ← Complex.cpow_add _ _ hq]
  congr 1
  ring

variable {r t : ℕ} {T : CuspidalOperatorRealization F r} {U : CuspidalOperatorRealization F t}

/-- Certified completed local factors at the translated variable agree with
the supplied partial Euler factors at every finite place outside `S`. -/
theorem finiteL_shift_eq_partialEulerFactor
    (P : CuspidalSpectralPresentation.{u, uQ} T) (P' : CuspidalSpectralPresentation.{u, uQ} U)
    (Q : CuspidalSpectralPresentation.{u, u} T) (Q' : CuspidalSpectralPresentation.{u, u} U)
    (hQ : HasIrreducibleAdmissibleComponents Q) (hQ' : HasIrreducibleAdmissibleComponents Q')
    {S : Finset (FinitePlace F)} (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S) (a b : ℂ)
    (c : FinitePairLChoice (Q.heckeDeterminantTwist (HeckeCharacter.normPower F (-a)))
      (Q'.heckeDeterminantTwist (HeckeCharacter.normPower F (-b)))
      (Q.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents _ hQ)
      (Q'.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents _ hQ'))
    (v : {v : FinitePlace F // v ∉ S}) (s : ℂ) :
    c.finiteL v.1 (s + (a + b)) = partialEulerFactor P P' hP hP' v s := by
  have hs := twistedLocalSpectrum v.1 P Q hQ (fun h => v.2 (hP h)) a
  have hs' := twistedLocalSpectrum v.1 P' Q' hQ' (fun h => v.2 (hP' h)) b
  have hpoly := isAutomorphicPairLPolynomial_eq_pairEulerPolynomial (padicField v.1)
    (c.additive v.1) (c.measure_spec v.1) _ _ hs hs' (c.lPolynomial_spec v.1)
  rw [FinitePairLChoice.finiteL, partialEulerFactor, hpoly,
    eval_pairEulerPolynomial_scale, scaled_spectralPoint]

end EulerFactors

private theorem eq_neg_one_of_le_of_lt {n : WithTop ℤ} (hLower : -1 ≤ n) (hNeg : n < 0) :
    n = -1 := by
  induction n with
  | top => exact absurd hNeg (not_lt.mpr le_top)
  | coe m =>
    have hLower' : (-1 : ℤ) ≤ m :=
      WithTop.coe_le_coe.mp (hLower : ((-1 : ℤ) : WithTop ℤ) ≤ m)
    have hNeg' : m < 0 := WithTop.coe_lt_coe.mp (hNeg : (m : WithTop ℤ) < ((0 : ℤ) : WithTop ℤ))
    have hm : m = -1 := by omega
    rw [hm]
    rfl

end CuspidalPartialPairOrderOne

open CuspidalPartialPairOrderOne

/-- The order at `1` of the partial cuspidal pair L-function follows from the
completed pair pole theorem (for presentations with factors in the field universe)
and from boundary nonvanishing of the partial pair L-functions. -/
def CuspidalPartialPairOrderOneFromPairPole : Prop :=
  CuspidalPairPoleStatement.{u, u} → CuspidalPairBoundaryNonvanishingStatement.{u, uQ} →
    CuspidalPartialPairOrderOneStatement.{u, uQ}

/-- **`CuspidalPartialPairOrderOneFromPairPole`.** The completed pole profile and
boundary nonvanishing give the exact order at `1` of each supplied partial pair
L-function; archimedean regularity is `Automorphic.cuspidalArchimedeanPairRegularity`. -/
theorem cuspidalPartialPairOrderOne_of_pairPole :
    CuspidalPartialPairOrderOneFromPairPole.{u, uQ} := by
  classical
  intro hPole hBoundary F _ _ _ r t T T' hT hT' P P' S hP hP' L hL
  obtain ⟨a, hU, ha, _⟩ := NormPowerTwist.exists_normPower_twist T
  obtain ⟨b, hU', hb, _⟩ := NormPowerTwist.exists_normPower_twist T'
  have hare : a.re = 0 := by
    obtain ⟨_, hωu, hω⟩ := hT
    exact normalizer_re_eq_zero hω hωu ha
  have hbre : b.re = 0 := by
    obtain ⟨_, hωu, hω⟩ := hT'
    exact normalizer_re_eq_zero hω hωu hb
  have hd : (a + b).re = 0 := by rw [Complex.add_re, hare, hbre, add_zero]
  obtain ⟨Q, hQ⟩ := cuspidalAllLocalIrreduciblePresentationExistence.{u, uQ} F r T P
  obtain ⟨Q', hQ'⟩ := cuspidalAllLocalIrreduciblePresentationExistence.{u, uQ} F t T' P'
  let χ := HeckeCharacter.normPower F (-a)
  let χ' := HeckeCharacter.normPower F (-b)
  let U := T.heckeDeterminantTwist χ
  let U' := T'.heckeDeterminantTwist χ'
  let Q₀ := Q.heckeDeterminantTwist χ
  let Q₀' := Q'.heckeDeterminantTwist χ'
  have hQ₀ := Q.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents χ hQ
  have hQ₀' := Q'.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents χ' hQ'
  obtain ⟨⟨⟨c⟩, hR, hC⟩, hΛexists⟩ := hPole F r t U U' ha hb Q₀ Q₀' hQ₀ hQ₀'
  choose dR hdR using fun v => (hR v).1
  choose dR' hdR' using fun v => (hR v).2
  choose dC hdC using fun v => (hC v).1
  choose dC' hdC' using fun v => (hC v).2
  obtain ⟨Λ, hΛprod, hprofile, _⟩ := hΛexists c dR dR' hdR hdR' dC dC' hdC hdC'
  have hAnalytic (z : ℂ) (hz : z ∉ ({0, 1} : Set ℂ)) : AnalyticAt ℂ Λ z :=
    hprofile.1.analyticAt ((Set.toFinite _).isClosed.isOpen_compl.mem_nhds hz)
  have hΛ : MeromorphicOn Λ Set.univ := by
    intro z _
    by_cases hz : z ∈ ({0, 1} : Set ℂ)
    · exact (hprofile.2 z hz).1
    · exact (hAnalytic z hz).meromorphicAt
  have horder := completedOrder_eq c dR dR' dC dC' hdR hdR' hdC hdC' hU hU'
    hL hΛ hΛprod hd (finiteL_shift_eq_partialEulerFactor P P' Q Q' hQ hQ' hP hP' a b c)
  have hDual := isDual_iff_shift_eq_zero_and_normalizedDual hT hT' ha hb
  have hOne : (1 : ℂ) ∈ ({0, 1} : Set ℂ) := by simp
  constructor
  · intro h
    obtain ⟨hab, hnormalized⟩ := hDual.mp h
    rw [horder, hab, add_zero]
    exact eq_neg_one_of_le_of_lt (hprofile.2 1 hOne).2.1
      ((hprofile.2 1 hOne).2.2.mpr hnormalized)
  · intro hn
    have hUpper : meromorphicOrderAt L 1 ≤ 0 := by
      simpa using (hBoundary F r t T T' hT hT' P P' S hP hP').2 L hL 0
    apply le_antisymm hUpper
    rw [horder]
    by_cases h1 : 1 + (a + b) = 1
    · rw [h1]
      have hab : a + b = 0 := add_left_cancel (h1.trans (add_zero _).symm)
      exact le_of_not_gt fun hneg =>
        hn (hDual.mpr ⟨hab, (hprofile.2 1 hOne).2.2.mp hneg⟩)
    · have h0 : 1 + (a + b) ≠ 0 := by
        intro heq
        have hre := congrArg Complex.re heq
        simp [Complex.add_re, hd] at hre
      exact (hAnalytic _ (by simp [h0, h1])).meromorphicOrderAt_nonneg

end Langlands.Global
