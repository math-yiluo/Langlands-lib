import Langlands.Global.AdelicEisensteinWeakConstantTermRemainderStatement
import Langlands.Analysis.ShiftRecurrenceBound
import Langlands.Global.AdelicSiegelSplitRays
import Langlands.Global.AdelicStandardParabolicFamilyConstruction
import Langlands.Global.AdelicPositiveTorusLogHeightBound
import Langlands.Global.AdelicRepresentationHeightPropernessProof
import Langlands.GroupScheme.Rational.RelativeRootNegationProof
import Langlands.GroupScheme.Rational.RelativeCharacterRootComplementProof

/-! # Exponential decay on cones from cone shift equations

A function on `G(𝔸)` with a unitary central character, the polynomial bound
`δ(b)^{1/2} σ(b ω)^m` on Siegel sets and cone shift equations along the split component of a
standard parabolic `Q_J` (`HasConeShiftEquations`) decays like `δ(b)^{1/2} e^{−ε' R}` on the cones
`|log |β(b)|| ≤ R` (`β ∈ Δ`), `δ R ≤ log |α(b)|` (`α ∉ J`): `ConeShiftDecay.exists_coneBound`.
This is the argument of Delorme 2023, proofs of Lemmas 5.1 and 5.2, with Lapid's Lemma 3 on
exponential polynomials replaced by the bound for linear recurrences of
`Langlands.Analysis.ShiftRecurrenceBound`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj NNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Global.ConeShiftDecay

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  AdelicSiegelFactors PositiveRealTorus RepresentationGrowth

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
  {ν : cocharacterLattice T} {T₀ : CommGroupScheme (Spec (CommRingCat.of F))} {j : T₀ ⟶ T}

local notation "Δ" => simpleRelativeRoots i ν
local notation "Torus" => PositiveRealTorus.intrinsicSubgroup F T₀
local notation "aG" => positiveMap F G T i T₀ j

/-- Every assignment of real numbers to the simple roots is the family of logarithms
`log |α(y)|` at some positive point `y` of the Siegel torus. -/
theorem exists_logNormHom_eq (hG : IsConnectedReductive G)
    (hsetup : IsSiegelAlgebraicSetup F G T i ν T₀ j) (s : characterLattice T → ℝ) :
    ∃ y : Torus, ∀ β ∈ Δ, logNormHom F T₀ y.val (j ≫ β) = s β := by
  classical
  obtain ⟨hi, hν, -, -, -, -, -, ⟨D, d, t₀, hd, ht₀max, ht₀⟩, -⟩ := id hsetup
  have hT₀ : IsSplitTorus T₀.toGrp := ht₀max.1.1
  let fam : StandardParabolicFamily F G :=
    StandardParabolicFamily.ofMaximalSplitTorus hG i hi ν hν
  let : Fintype (simpleRelativeRoots fam.i fam.ν) :=
    (hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν).fintype
  obtain ⟨r, hOff, hPos, -, -⟩ := fam.exists_siegelFundamentalRays j hsetup
  let h : simpleRelativeRoots fam.i fam.ν → ℝ :=
    fun α => characterLog F T₀.toGrp (r α).val (j ≫ α.val)
  let ℓf : GroupScheme.rationalCharacters T₀.toGrp → ℝ := fun χ =>
    ∑ α : simpleRelativeRoots fam.i fam.ν,
      (s (α.val : characterLattice T) / h α) * characterLog F T₀.toGrp (r α).val χ
  let ℓ : RealCharacterDual F T₀.toGrp := AddMonoidHom.mk' ℓf (fun χ ψ => by
    have hadd : ∀ α : simpleRelativeRoots fam.i fam.ν,
        characterLog F T₀.toGrp (r α).val (χ + ψ) =
          characterLog F T₀.toGrp (r α).val χ + characterLog F T₀.toGrp (r α).val ψ :=
      fun α => AddMonoidHom.map_add _ χ ψ
    simp only [ℓf, hadd, mul_add, Finset.sum_add_distrib])
  obtain ⟨y, hy, hyℓ⟩ := PositiveRealTorus.exists_characterLog_eq hT₀ ℓ
  refine ⟨⟨y, hy⟩, fun β hβ => ?_⟩
  change characterLog F T₀.toGrp y (j ≫ β) = s β
  rw [hyℓ]
  let β' : simpleRelativeRoots fam.i fam.ν := ⟨β, hβ⟩
  change ℓf (j ≫ β) = s β
  simp only [ℓf]
  rw [Finset.sum_eq_single β']
  · have hpos : 0 < h β' := hPos β'
    change s β / h β' * h β' = s β
    field_simp
  · intro α _ hαβ
    exact mul_eq_zero_of_right _ (hOff α β' (Ne.symm hαβ))
  · intro h'
    exact absurd (Finset.mem_univ β') h'


/-- `log |χ(·)|` is additive on the positive torus. -/
theorem logNormHom_mul (x y : Lie.AffinePoints T₀.toGrp (Adeles F))
    (χ : characterLattice T₀) :
    logNormHom F T₀ (x * y) χ = logNormHom F T₀ x χ + logNormHom F T₀ y χ := by
  change Real.log ((normCharacter F T₀ χ (x * y) : ℝ≥0) : ℝ) =
    Real.log ((normCharacter F T₀ χ x : ℝ≥0) : ℝ) + Real.log ((normCharacter F T₀ χ y : ℝ≥0) : ℝ)
  rw [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul]
  · exact (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))).ne'
  · exact (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))).ne'

/-- `log |χ(1)| = 0`. -/
theorem logNormHom_one (χ : characterLattice T₀) :
    logNormHom F T₀ (1 : Lie.AffinePoints T₀.toGrp (Adeles F)) χ = 0 := by
  change Real.log ((normCharacter F T₀ χ 1 : ℝ≥0) : ℝ) = 0
  rw [map_one, Units.val_one, NNReal.coe_one, Real.log_one]

/-- `log |χ(x^n)| = n log |χ(x)|`. -/
theorem logNormHom_pow (x : Lie.AffinePoints T₀.toGrp (Adeles F)) (n : ℕ)
    (χ : characterLattice T₀) :
    logNormHom F T₀ (x ^ n) χ = n * logNormHom F T₀ x χ := by
  induction n with
  | zero => rw [pow_zero, logNormHom_one, Nat.cast_zero, zero_mul]
  | succ n ih => rw [pow_succ, logNormHom_mul, ih, Nat.cast_succ]; ring

/-- `log |χ(x⁻¹)| = −log |χ(x)|`. -/
theorem logNormHom_inv (x : Lie.AffinePoints T₀.toGrp (Adeles F)) (χ : characterLattice T₀) :
    logNormHom F T₀ x⁻¹ χ = -logNormHom F T₀ x χ := by
  have h := logNormHom_mul x⁻¹ x χ
  rw [inv_mul_cancel, logNormHom_one] at h
  linarith

/-- The coercion `ℝ≥0 → ℝ` commutes with finite products. -/
theorem coe_finprod_nnreal {X : Sort*} (f : X → ℝ≥0) :
    ((∏ᶠ a, f a : ℝ≥0) : ℝ) = ∏ᶠ a, (f a : ℝ) := by
  simpa using MonoidHom.map_finprod_of_injective (NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom
    NNReal.coe_injective f

/-- The Siegel modulus is the exponential of a linear form in the simple-root logarithms with
positive integral coefficients. -/
theorem exists_siegelModulus_eq_exp (hsetup : IsSiegelAlgebraicSetup F G T i ν T₀ j)
    [Fintype Δ] :
    ∃ e : Δ → ℕ, ∀ b : Torus, siegelModulus F G T i ν T₀ j b =
      Real.exp (∑ α : Δ, (e α : ℝ) * logNormHom F T₀ b.val (j ≫ (α : characterLattice T))) := by
  obtain ⟨hi, -⟩ := id hsetup
  obtain ⟨e, -, he⟩ := AdelicSiegelFactors.exists_simpleRoot_exponents (G := G) i ν j
    hi.isSplitSubtorus.1
  refine ⟨e, fun b => ?_⟩
  have h := congrArg (fun r : ℝ≥0 => (r : ℝ)) (he b.val)
  simp only [NNReal.coe_prod, NNReal.coe_pow] at h
  have hsm : siegelModulus F G T i ν T₀ j b = ∏ α : Δ,
      ((normCharacter F T₀ (j ≫ (α : characterLattice T)) b.val : ℝ≥0) : ℝ) ^ e α := by
    rw [siegelModulus, ← h, coe_finprod_nnreal]
    refine finprod_congr fun β => ?_
    rw [coe_finprod_nnreal]
    refine finprod_congr fun _ => ?_
    rw [NNReal.coe_pow]
  rw [hsm, Real.exp_sum]
  refine Finset.prod_congr rfl fun α _ => ?_
  have hpos : (0 : ℝ) < ((normCharacter F T₀ (j ≫ (α : characterLattice T)) b.val : ℝ≥0) : ℝ) :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
  rw [Real.exp_nat_mul]
  change _ = Real.exp (Real.log _) ^ e α
  rw [Real.exp_log hpos]

/-- The logarithmic height of `a(y) ω` grows at most linearly in a bound for the simple-root
logarithms of `y`, uniformly for `ω` in a compact set. -/
theorem exists_adelicLogHeight_le (hG : IsConnectedReductive G)
    (hsetup : IsSiegelAlgebraicSetup F G T i ν T₀ j) {N : ℕ}
    (rho : MatrixRepresentation G (Fin N)) {Ω : Set (AdelicGroupPoints F G)} (hΩ : IsCompact Ω) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (y : Torus) (R : ℝ), 0 ≤ R →
      (∀ β ∈ Δ, |logNormHom F T₀ y.val (j ≫ β)| ≤ R) →
      ∀ ω ∈ Ω, adelicLogHeight F G rho (aG y * ω) ≤ c * (1 + R) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have : Subsingleton (AdelicGL F 0) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
    refine ⟨adelicLogHeight F G rho 1, ?_, fun y R hR _ ω _ => ?_⟩
    · have := Real.log_nonneg (le_max_left 1 (adelicSourceNorm F G rho 1))
      unfold adelicLogHeight
      linarith
    · have he : adelicLogHeight F G rho (aG y * ω) = adelicLogHeight F G rho 1 := by
        unfold adelicLogHeight adelicSourceNorm
        rw [Subsingleton.elim (adelicMatrix F G rho (aG y * ω)) (adelicMatrix F G rho 1)]
      rw [he]
      have h1 : 0 ≤ adelicLogHeight F G rho 1 := by
        have := Real.log_nonneg (le_max_left 1 (adelicSourceNorm F G rho 1))
        unfold adelicLogHeight
        linarith
      nlinarith
  · obtain ⟨-, -, -, -, -, -, -, ⟨D, d, t₀, hd, ht₀max, ht₀⟩, -⟩ := id hsetup
    have hT₀ : IsSplitTorus T₀.toGrp := ht₀max.1.1
    have hS := AdelicSiegelFactors.ratSpan_restrict_simpleRelativeRoots_eq_top
      relativeRootNegation relativeCharacterRootComplement hG hsetup
    obtain ⟨C, r, hC1, hr0, hCb⟩ := adelicPositiveTorusLogHeightBound
      (CommGroupScheme.groupHom j ≫ i) rho _ hT₀ hS hN
    obtain ⟨H, hH⟩ := (hΩ.image (continuous_adelicHeight F G rho hN)).bddAbove
    set HΩ : ℝ := max 1 H with hHΩ
    have hHΩ1 : 1 ≤ HΩ := le_max_left _ _
    refine ⟨1 + Real.log C + Real.log HΩ + r, ?_, fun y R hR hy ω hω => ?_⟩
    · have := Real.log_nonneg hC1
      have := Real.log_nonneg hHΩ1
      linarith
    have hyC : adelicHeight F G rho (aG y) ≤ C * Real.exp (r * R) := by
      refine hCb y R hR ?_
      rintro χ ⟨β, hβ, rfl⟩
      exact hy β hβ
    have hωH : adelicHeight F G rho ω ≤ HΩ := (hH ⟨ω, hω, rfl⟩).trans (le_max_right _ _)
    have hprod : adelicHeight F G rho (aG y * ω) ≤ C * Real.exp (r * R) * HΩ :=
      (adelicHeight_mul_le F G rho hN _ _).trans
        (mul_le_mul hyC hωH (zero_le_one.trans (one_le_adelicHeight F G rho hN ω))
          (by positivity))
    have hsrc : max 1 (adelicSourceNorm F G rho (aG y * ω)) ≤
        adelicHeight F G rho (aG y * ω) := by
      refine max_le (one_le_adelicHeight F G rho hN _) ?_
      rw [adelicHeight_eq_scalar_mul_sourceNorm]
      have hs := adelicSourceNorm_pos F G rho hN (aG y * ω)
      have hN1 : (1 : ℝ) ≤ (N : ℝ) ^ (∑ v : NumberField.InfinitePlace F, v.mult) :=
        one_le_pow₀ (by exact_mod_cast hN)
      nlinarith
    have hlog : Real.log (max 1 (adelicSourceNorm F G rho (aG y * ω))) ≤
        Real.log C + r * R + Real.log HΩ := by
      have h1 : Real.log (max 1 (adelicSourceNorm F G rho (aG y * ω))) ≤
          Real.log (C * Real.exp (r * R) * HΩ) :=
        Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (hsrc.trans hprod)
      have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC1
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
        (by positivity), Real.log_exp] at h1
      linarith
    unfold adelicLogHeight
    have := Real.log_nonneg hC1
    have := Real.log_nonneg hHΩ1
    nlinarith


/-- `√(e^a) = e^{a/2}`. -/
theorem sqrt_exp (a : ℝ) : Real.sqrt (Real.exp a) = Real.exp (a / 2) := by
  have h : Real.exp a = Real.exp (a / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]
    ring_nf
  rw [h, Real.sqrt_sq (Real.exp_pos _).le]

/-- Polynomials are dominated by exponentials: `(1 + R)^m ≤ e^{m a (1 + R)} / a^m` for
`a > 0` and `R ≥ 0`. -/
theorem one_add_pow_le_exp {a : ℝ} (ha : 0 < a) (m : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    (1 + R) ^ m ≤ Real.exp (m * a * (1 + R)) / a ^ m := by
  have h1 : a * (1 + R) ≤ Real.exp (a * (1 + R)) := by
    have := Real.add_one_le_exp (a * (1 + R))
    linarith
  have h2 : 1 + R ≤ Real.exp (a * (1 + R)) / a := by
    rw [le_div_iff₀ ha]
    linarith
  calc (1 + R) ^ m ≤ (Real.exp (a * (1 + R)) / a) ^ m :=
        pow_le_pow_left₀ (by linarith) h2 m
    _ = Real.exp (m * a * (1 + R)) / a ^ m := by
        rw [div_pow, ← Real.exp_nat_mul]
        ring_nf

/-- **Exponential decay on cones from cone shift equations** (the argument of Delorme 2023,
proofs of Lemmas 5.1 and 5.2, with Lapid's Lemma 3 replaced by a difference equation along one
translation). Let `J ⊆ Δ` omit the simple root `α₀`, let `δ, ε > 0` and let `t' ≤ min(t, 1)`.
There is `B'` such that every function `f` on `G(𝔸)` with
* `‖f(z g)‖ = ‖f(g)‖` for `z ∈ A_G`,
* `‖f(b ω)‖ ≤ B δ(b)^{1/2} σ(b ω)^m` for `b` in the weak chamber of threshold `t'` and
  `ω ∈ Ω`,
* cone shift equations of order `m` and rate `ε` along `J` on the cone of aperture `δ`,

satisfies `‖f(z b ω)‖ ≤ B' δ(b)^{1/2} e^{−(εδ/4) R}` for `z ∈ A_G`, `b` in the weak chamber of
threshold `t`, `ω ∈ Ω` and every `R` with `|log |β(b)|| ≤ R` for all `β ∈ Δ` and
`δ R ≤ log |α(b)|` for all `α ∈ Δ \ J`. -/
theorem exists_coneBound (hG : IsConnectedReductive G)
    (hsetup : IsSiegelAlgebraicSetup F G T i ν T₀ j) {N : ℕ}
    (rho : MatrixRepresentation G (Fin N))
    {J : Set (characterLattice T)} (hJ : J ⊆ Δ) {α₀ : characterLattice T}
    (hα₀ : α₀ ∈ Δ) (hα₀J : α₀ ∉ J) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (m : ℕ) (B : ℝ)
    {t t' : ℝ≥0ˣ} (htt' : t' ≤ t) (ht'1 : t' ≤ 1)
    {Ω : Set (AdelicGroupPoints F G)} (hΩ : IsCompact Ω) :
    ∃ B' : ℝ, ∀ f : AdelicGroupPoints F G → ℂ,
      (∀ z ∈ RestrictionSplitCentre.canonicalSubgroup F G, ∀ g, ‖f (z * g)‖ = ‖f g‖) →
      (∀ b ∈ weakSimpleRootChamber F T₀ T j G i ν t', ∀ ω ∈ Ω,
        ‖f (aG b * ω)‖ ≤ B * Real.sqrt (siegelModulus F G T i ν T₀ j b) *
          adelicLogHeight F G rho (aG b * ω) ^ m) →
      HasConeShiftEquations F G T i ν T₀ j J δ ε m f →
      ∀ z ∈ RestrictionSplitCentre.canonicalSubgroup F G,
      ∀ b ∈ weakSimpleRootChamber F T₀ T j G i ν t, ∀ ω ∈ Ω, ∀ R : ℝ,
        (∀ β ∈ Δ, |logNormHom F T₀ b.val (j ≫ β)| ≤ R) →
        (∀ α ∈ Δ, α ∉ J → δ * R ≤ logNormHom F T₀ b.val (j ≫ α)) →
        ‖f (z * aG b * ω)‖ ≤ B' * Real.sqrt (siegelModulus F G T i ν T₀ j b) *
          Real.exp (-(ε * δ / 4 * R)) := by
  classical
  obtain ⟨hi, -⟩ := id hsetup
  let : Fintype Δ := (hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν).fintype
  obtain ⟨e, he⟩ := exists_siegelModulus_eq_exp hsetup
  obtain ⟨c, hc0, hc⟩ := exists_adelicLogHeight_le hG hsetup rho hΩ
  set N₀ : ℕ := 2 * m + 1 with hN₀
  set Nr : ℝ := (N₀ : ℝ) with hNr
  have hNr0 : 0 < Nr := by rw [hNr]; positivity
  have hNrm : 2 * (m : ℝ) + 1 = Nr := by rw [hNr, hN₀]; push_cast; ring
  set κc : ℝ := ε * δ / (4 * ((m : ℝ) + 1)) with hκcdef
  have hκc : 0 < κc := by positivity
  have hmκc : (m : ℝ) * κc ≤ ε * δ / 4 := by
    rw [hκcdef, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_pos hε hδ]
  set Bp : ℝ := max B 0 with hBp
  have hBp0 : 0 ≤ Bp := le_max_right _ _
  refine ⟨3 ^ m * (Nr + 1) ^ m * (Bp * c ^ m * Real.exp (ε * δ / 4) / κc ^ m), ?_⟩
  intro f hcent hpoly hshift z hz b hb ω hω R hR hRJ
  rw [mul_assoc, hcent z hz]
  -- the linear form giving the modulus
  set Lm : Torus → ℝ := fun x =>
    ∑ α : Δ, (e α : ℝ) * logNormHom F T₀ x.val (j ≫ (α : characterLattice T)) with hLm
  have hsq : ∀ x : Torus, Real.sqrt (siegelModulus F G T i ν T₀ j x) = Real.exp (Lm x / 2) :=
    fun x => by rw [he x, sqrt_exp]
  set ℓ : characterLattice T → ℝ := fun β => logNormHom F T₀ b.val (j ≫ β) with hℓ
  have hR0 : 0 ≤ R := (abs_nonneg _).trans (hR α₀ hα₀)
  have hℓ₀ : δ * R ≤ ℓ α₀ := hRJ α₀ hα₀ hα₀J
  have hℓ₀0 : 0 ≤ ℓ α₀ := le_trans (by positivity) hℓ₀
  -- the translation point `y`
  obtain ⟨y, hy⟩ := exists_logNormHom_eq hG hsetup
    (fun β => if β ∈ J then 0 else ℓ β / Nr)
  set b₀ : Torus := (y ^ N₀)⁻¹ * b with hb₀
  have hJy : ∀ β ∈ J, logNormHom F T₀ y.val (j ≫ β) = 0 := fun β hβ => by
    rw [hy β (hJ hβ)]
    simp only [hβ, ↓reduceIte]
  have hαy : ∀ α ∈ Δ, α ∉ J → logNormHom F T₀ y.val (j ≫ α) = ℓ α / Nr :=
    fun α hα hαJ => by
      rw [hy α hα]
      simp only [hαJ, ↓reduceIte]
  have hlogq : ∀ (q : ℕ) (χ : characterLattice T₀),
      logNormHom F T₀ (y ^ q * b₀).val χ =
        logNormHom F T₀ b.val χ + ((q : ℝ) - Nr) * logNormHom F T₀ y.val χ := by
    intro q χ
    simp only [hb₀, Subgroup.coe_mul, SubgroupClass.coe_pow, InvMemClass.coe_inv,
      logNormHom_mul, logNormHom_pow, logNormHom_inv]
    rw [hNr]
    ring
  have hLq : ∀ q : ℕ, Lm (y ^ q * b₀) = Lm b + ((q : ℝ) - Nr) * Lm y := by
    intro q
    simp only [hLm, hlogq, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    ring
  -- the shift equation along `y`
  obtain ⟨w, hw, hsol⟩ := hshift y hJy
    (fun α hα hαJ => by
      rw [hαy α hα hαJ]
      exact div_nonneg (le_trans (by positivity) (hRJ α hα hαJ)) hNr0.le)
    (fun α hα hαJ α' hα' hα'J => by
      rw [hαy α hα hαJ, hαy α' hα' hα'J]
      have h1 : ℓ α' ≤ R := (le_abs_self _).trans (hR α' hα')
      have h2 := hRJ α hα hαJ
      rw [mul_div_assoc']
      exact div_le_div_of_nonneg_right (by nlinarith) hNr0.le)
  set κ : ℝ := Real.exp (Lm y / 2 - ε * (ℓ α₀ / Nr)) with hκ
  have hκ0 : 0 < κ := Real.exp_pos _
  have hwκ : ∀ k, ‖w k‖ ≤ κ := by
    intro k
    have := hw k α₀ hα₀ hα₀J
    rwa [hsq y, hαy α₀ hα₀ hα₀J, ← Real.exp_add, ← sub_eq_add_neg] at this
  set P : ℝ := (c * (1 + R)) ^ m with hP
  have hP0 : 0 ≤ P := by positivity
  set M : ℝ := Real.exp (ε * m * ℓ α₀ / Nr) * Bp * Real.exp ((Lm b - Nr * Lm y) / 2) * P
    with hM
  have hM0 : 0 ≤ M := by positivity
  have hstart : ∀ q < m, ‖f (aG y ^ q * (aG b₀ * ω))‖ ≤ κ ^ q * M := by
    intro q hq
    have hpt : aG y ^ q * (aG b₀ * ω) = aG (y ^ q * b₀) * ω := by
      simp only [b₀, map_mul, map_pow, map_inv, mul_assoc]
    rw [hpt]
    have hqN : (q : ℝ) ≤ Nr := by
      rw [← hNrm]; have : (q : ℝ) < m := by exact_mod_cast hq
      linarith
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have hcoord : ∀ β ∈ Δ, logNormHom F T₀ (y ^ q * b₀).val (j ≫ β) =
        if β ∈ J then ℓ β else ℓ β * q / Nr := by
      intro β hβ
      rw [hlogq, hy β hβ]
      split_ifs
      · rw [mul_zero, add_zero]
      · field_simp
        ring
    have hmem : y ^ q * b₀ ∈ weakSimpleRootChamber F T₀ T j G i ν t' := by
      refine (mem_weakSimpleRootChamber_iff_log F T₀ T j G i ν t' _).mpr fun χ hχ => ?_
      change Real.log ((t' : ℝ≥0) : ℝ) ≤ logNormHom F T₀ (y ^ q * b₀).val (j ≫ χ)
      rw [hcoord χ hχ]
      have ht'0 : (0 : ℝ) < ((t' : ℝ≥0) : ℝ) := by exact_mod_cast (Units.ne_zero t').bot_lt
      split_ifs with hχJ
      · have hbχ := (mem_weakSimpleRootChamber_iff_log F T₀ T j G i ν t b).mp hb χ hχ
        have hlt : Real.log ((t' : ℝ≥0) : ℝ) ≤ Real.log ((t : ℝ≥0) : ℝ) :=
          Real.log_le_log ht'0 (by exact_mod_cast Units.val_le_val.mpr htt')
        exact hlt.trans hbχ
      · have hlog0 : Real.log ((t' : ℝ≥0) : ℝ) ≤ 0 :=
          Real.log_nonpos ht'0.le (by exact_mod_cast Units.val_le_val.mpr ht'1)
        have hℓχ : 0 ≤ ℓ χ := le_trans (by positivity) (hRJ χ hχ hχJ)
        exact hlog0.trans (div_nonneg (mul_nonneg hℓχ hq0) hNr0.le)
    have hbox : ∀ β ∈ Δ, |logNormHom F T₀ (y ^ q * b₀).val (j ≫ β)| ≤ R := by
      intro β hβ
      rw [hcoord β hβ]
      split_ifs with hβJ
      · exact hR β hβ
      · have hℓβ : 0 ≤ ℓ β := le_trans (by positivity) (hRJ β hβ hβJ)
        have h1 : ℓ β ≤ R := (le_abs_self _).trans (hR β hβ)
        rw [abs_of_nonneg (div_nonneg (mul_nonneg hℓβ hq0) hNr0.le), div_le_iff₀ hNr0]
        nlinarith
    have hσ := hc (y ^ q * b₀) R hR0 hbox ω hω
    have hσ0 : 0 ≤ adelicLogHeight F G rho (aG (y ^ q * b₀) * ω) := by
      unfold adelicLogHeight
      have := Real.log_nonneg (le_max_left 1 (adelicSourceNorm F G rho (aG (y ^ q * b₀) * ω)))
      linarith
    have h1 := hpoly (y ^ q * b₀) hmem ω hω
    rw [hsq, hLq] at h1
    have h2 : ‖f (aG (y ^ q * b₀) * ω)‖ ≤
        Bp * Real.exp ((Lm b + ((q : ℝ) - Nr) * Lm y) / 2) * P := by
      refine h1.trans ?_
      gcongr
      · exact le_max_left _ _
      · exact pow_le_pow_left₀ hσ0 hσ m
    refine h2.trans ?_
    have hexp : Real.exp ((Lm b + ((q : ℝ) - Nr) * Lm y) / 2) ≤
        κ ^ q * Real.exp (ε * m * ℓ α₀ / Nr) * Real.exp ((Lm b - Nr * Lm y) / 2) := by
      rw [hκ, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hm : (q : ℝ) ≤ m := by exact_mod_cast hq.le
      have : ε * (q * (ℓ α₀ / Nr)) ≤ ε * m * ℓ α₀ / Nr := by
        rw [show ε * m * ℓ α₀ / Nr = ε * (m * (ℓ α₀ / Nr)) by ring]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hm (div_nonneg hℓ₀0 hNr0.le)) hε.le
      nlinarith
    calc Bp * Real.exp ((Lm b + ((q : ℝ) - Nr) * Lm y) / 2) * P
        ≤ Bp * (κ ^ q * Real.exp (ε * m * ℓ α₀ / Nr) * Real.exp ((Lm b - Nr * Lm y) / 2)) * P := by
          gcongr
      _ = κ ^ q * M := by rw [hM]; ring
  have key := Langlands.Analysis.norm_le_of_translationSolution (aG y) w hκ0 hwκ f
    (fun g => hsol g) (aG b₀ * ω) hM0 hstart N₀
  have hpt : aG y ^ N₀ * (aG b₀ * ω) = aG b * ω := by
    rw [← mul_assoc, ← map_pow, ← map_mul, hb₀, mul_inv_cancel_left]
  rw [hpt] at key
  refine key.trans ?_
  -- the final arithmetic
  have hκN : κ ^ N₀ * M = Real.exp (Lm b / 2 - ε * ℓ α₀ + ε * m * ℓ α₀ / Nr) * Bp * P := by
    rw [hκ, hM, ← Real.exp_nat_mul]
    have : Real.exp (↑N₀ * (Lm y / 2 - ε * (ℓ α₀ / Nr))) *
        (Real.exp (ε * ↑m * ℓ α₀ / Nr) * Bp * Real.exp ((Lm b - Nr * Lm y) / 2) * P) =
        Real.exp (↑N₀ * (Lm y / 2 - ε * (ℓ α₀ / Nr)) + ε * ↑m * ℓ α₀ / Nr +
          (Lm b - Nr * Lm y) / 2) * Bp * P := by
      rw [Real.exp_add, Real.exp_add]
      ring
    rw [this]
    congr 3
    rw [← hNr]
    field_simp
    ring
  have hexp1 : Lm b / 2 - ε * ℓ α₀ + ε * m * ℓ α₀ / Nr ≤ Lm b / 2 - ε * δ / 2 * R := by
    have h1 : ε * m * ℓ α₀ / Nr ≤ ε * ℓ α₀ / 2 := by
      rw [div_le_div_iff₀ hNr0 (by norm_num)]
      have : 0 ≤ ε * ℓ α₀ := mul_nonneg hε.le hℓ₀0
      nlinarith
    have h2 : ε * δ / 2 * R ≤ ε * ℓ α₀ / 2 := by
      have := mul_le_mul_of_nonneg_left hℓ₀ hε.le
      nlinarith
    linarith
  have hPle : P ≤ c ^ m * (Real.exp (ε * δ / 4) * Real.exp (ε * δ / 4 * R) / κc ^ m) := by
    rw [hP, mul_pow]
    gcongr
    calc (1 + R) ^ m ≤ Real.exp (m * κc * (1 + R)) / κc ^ m := one_add_pow_le_exp hκc m hR0
      _ ≤ Real.exp (ε * δ / 4 * (1 + R)) / κc ^ m := by
          gcongr
      _ = Real.exp (ε * δ / 4) * Real.exp (ε * δ / 4 * R) / κc ^ m := by
          rw [← Real.exp_add]
          ring_nf
  rw [hsq b]
  have hcast : ((N₀ : ℕ) : ℝ) = Nr := rfl
  rw [hcast, mul_assoc (3 ^ m * (Nr + 1) ^ m), hκN]
  calc 3 ^ m * (Nr + 1) ^ m *
        (Real.exp (Lm b / 2 - ε * ℓ α₀ + ε * m * ℓ α₀ / Nr) * Bp * P)
      ≤ 3 ^ m * (Nr + 1) ^ m * (Real.exp (Lm b / 2 - ε * δ / 2 * R) * Bp *
          (c ^ m * (Real.exp (ε * δ / 4) * Real.exp (ε * δ / 4 * R) / κc ^ m))) := by
        gcongr
    _ = 3 ^ m * (Nr + 1) ^ m * (Bp * c ^ m * Real.exp (ε * δ / 4) / κc ^ m) *
          Real.exp (Lm b / 2) * Real.exp (-(ε * δ / 4 * R)) := by
        have : Real.exp (Lm b / 2 - ε * δ / 2 * R) * Real.exp (ε * δ / 4 * R) =
            Real.exp (Lm b / 2) * Real.exp (-(ε * δ / 4 * R)) := by
          rw [← Real.exp_add, ← Real.exp_add]
          ring_nf
        calc _ = 3 ^ m * (Nr + 1) ^ m * (Bp * c ^ m * Real.exp (ε * δ / 4) / κc ^ m) *
              (Real.exp (Lm b / 2 - ε * δ / 2 * R) * Real.exp (ε * δ / 4 * R)) := by ring
          _ = _ := by rw [this]; ring

end Langlands.Global.ConeShiftDecay
