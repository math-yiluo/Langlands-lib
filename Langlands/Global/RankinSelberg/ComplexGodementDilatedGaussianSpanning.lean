import Langlands.Global.RankinSelberg.CompactFiniteUniformSpan
import Langlands.Global.RankinSelberg.ComplexGodementCompactSpanning
import Langlands.Global.RankinSelberg.ComplexGodementUniformApproximation

/-! # Gaussian-polynomial Godement sections span in the convergence region -/

noncomputable section

open MeasureTheory MvPolynomial
open scoped Matrix.Norms.Operator SchwartzMap Langlands.Archimedean.ComplexDuality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodement

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open ComplexGeneralLinearHaarDensity (complexGeneralLinearHaar)
open ComplexGodementGaussianPolynomial
  (Coordinates gaussianPolynomial exists_gaussianPolynomial_mul_unitary)
open ComplexJacquet (compactFiniteUniformSpan linearForm_eq_finitelyManyEvaluations)

local instance dilatedGaussianSpanningGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear n ℂ) := borel _
local instance dilatedGaussianSpanningGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear n ℂ) := ⟨rfl⟩

variable {m : ℕ}
local notation "H" => Langlands.GeneralLinear m ℂ
local notation "G" => Langlands.GeneralLinear (m + 1) ℂ
local notation "Kc" => unitaryCompact ℂ (m + 1)
local notation "Mat" => Matrix (Fin m) (Fin (m + 1)) ℂ
local notation "Polynomials" => MvPolynomial (Coordinates m (m + 1)) ℂ
local notation "ν" => complexGeneralLinearHaar m
local notation "Smaller" => fun ds => kFiniteFunctions (complexStandardModule m ds) (unitaryCompact ℂ m)
local notation "Larger" => fun d ds => kFiniteFunctions (complexStandardModule (m + 1) (d :: ds)) Kc

private def dilatedGauss (z : ℂˣ) (p : Polynomials) : 𝓢(Mat, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((ContinuousLinearEquiv.smulLeft (R₁ := ℂ) (M₁ := Mat) z).restrictScalars ℝ)
    (gaussianPolynomial p)

private theorem dilatedGauss_apply (z : ℂˣ) (p : Polynomials) (X : Mat) :
    dilatedGauss z p X = gaussianPolynomial p ((z : ℂ) • X) := rfl

private def gaussianLinear (z : ℂˣ) : Polynomials →ₗ[ℂ] 𝓢(Mat, ℂ) where
  toFun := dilatedGauss z
  map_add' p q := by ext X; simp [dilatedGauss_apply, add_mul]
  map_smul' c p := by ext X; simp [dilatedGauss_apply, MvPolynomial.smul_eq_C_mul, mul_assoc]

private def restrictCompact : (G → ℂ) →ₗ[ℂ] (Kc → ℂ) :=
  LinearMap.pi fun k : Kc => LinearMap.proj k.val

private def godementSchwartzLinear (d : ComplexCharacterData) (f : H → ℂ)
    (hI : ∀ (Φ : 𝓢(Mat, ℂ)) (g : G), Integrable (godementSectionIntegrand d Φ f g) ν) :
    𝓢(Mat, ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun Φ := godementSection ν d Φ f
  map_add' Φ Ψ := by
    funext g
    have h : godementSectionIntegrand d (Φ + Ψ) f g =
        godementSectionIntegrand d Φ f g + godementSectionIntegrand d Ψ f g := by
      funext x
      simp [godementSectionIntegrand, add_mul]
    simp only [godementSection, h, Pi.add_apply, integral_add (hI Φ g) (hI Ψ g), mul_add]
  map_smul' c Φ := by
    funext g
    have h : godementSectionIntegrand d (c • Φ) f g =
        fun x => c * godementSectionIntegrand d Φ f g x := by
      funext x
      simp [godementSectionIntegrand, smul_eq_mul, mul_assoc]
    simp only [godementSection, h, integral_const_mul, RingHom.id_apply, Pi.smul_apply,
      smul_eq_mul, mul_left_comm]

private def rightShift (k : Kc) : (Kc → ℂ) →ₗ[ℂ] (Kc → ℂ) :=
  LinearMap.funLeft ℂ ℂ (fun x => x * k)

private def compactFiniteContinuous (m : ℕ) : Submodule ℂ (unitaryCompact ℂ (m + 1) → ℂ) where
  carrier := {f | Continuous f ∧ FiniteDimensional ℂ (Submodule.span ℂ
    (Set.range fun k : unitaryCompact ℂ (m + 1) => fun x => f (x * k)))}
  zero_mem' := ⟨continuous_const, by
    apply Submodule.finiteDimensional_of_le (S₂ := ⊥)
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact Submodule.zero_mem _⟩
  add_mem' := by
    rintro f g ⟨hf, hF⟩ ⟨hg, hG⟩
    let K := unitaryCompact ℂ (m + 1)
    let F₁ := Submodule.span ℂ (Set.range fun k : K => fun x => f (x * k))
    let G₁ := Submodule.span ℂ (Set.range fun k : K => fun x => g (x * k))
    let : FiniteDimensional ℂ F₁ := hF
    let : FiniteDimensional ℂ G₁ := hG
    refine ⟨hf.add hg, Submodule.finiteDimensional_of_le (S₂ := F₁ ⊔ G₁) (Submodule.span_le.mpr ?_)⟩
    rintro _ ⟨k, rfl⟩
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨k, rfl⟩) (Submodule.subset_span ⟨k, rfl⟩)
  smul_mem' := by
    rintro c f ⟨hf, hF⟩
    let K := unitaryCompact ℂ (m + 1)
    let F := Submodule.span ℂ (Set.range fun k : K => fun x => f (x * k))
    let : FiniteDimensional ℂ F := hF
    refine ⟨hf.const_smul c, Submodule.finiteDimensional_of_le (S₂ := F) (Submodule.span_le.mpr ?_)⟩
    rintro _ ⟨k, rfl⟩
    exact F.smul_mem c (Submodule.subset_span ⟨k, rfl⟩)

private theorem gaussianSection_regular (d : ComplexCharacterData) (f : H → ℂ)
    (hI : ∀ (Φ : 𝓢(Mat, ℂ)) (g : G), Integrable (godementSectionIntegrand d Φ f g) ν)
    (z : ℂˣ) (p : Polynomials) :
    restrictCompact (godementSection ν d (dilatedGauss z p) f) ∈ compactFiniteContinuous m := by
  let P := restrictTotalDegree (Coordinates m (m + 1)) ℂ p.totalDegree
  let L := (gaussianLinear z).comp P.subtype
  let V := L.range
  choose q hq hq' using fun k : Kc => exists_gaussianPolynomial_mul_unitary p k
  let v (k : Kc) : V := ⟨dilatedGauss z (q k), ⟨⟨q k, (mem_restrictTotalDegree _ _ _).mpr (hq k)⟩, rfl⟩⟩
  have htranslate (k : Kc) (X : Mat) : (v k).val X = dilatedGauss z p (X * k.val.val) := by
    simpa only [v, dilatedGauss_apply, Matrix.smul_mul] using (hq' k ((z : ℂ) • X)).symm
  let T := (godementSchwartzLinear d f hI).comp V.subtype
  let b (k : Kc) := characterWeight d ((m : ℂ) / 2) (determinant k.val)
  let Z := restrictCompact (godementSection ν d (dilatedGauss z p) f)
  have hEq (k x : Kc) : Z (x * k) = b k * T (v k) x.val := by
    have htest : translateTest k.val (dilatedGauss z p) = ((v k).val : Mat → ℂ) :=
      funext fun X => (htranslate k X).symm
    simpa only [Z, restrictCompact, LinearMap.pi_apply, LinearMap.proj_apply,
      Subgroup.coe_mul, b, T, LinearMap.comp_apply, Submodule.subtype_apply, godementSchwartzLinear,
      LinearMap.coe_mk, AddHom.coe_mk, htest] using
      godementSection_right_mul ν d (dilatedGauss z p) f x.val k.val
  let : FiniteDimensional ℂ V := inferInstance
  let ρ : V →ₗ[ℂ] (Mat → ℂ) :=
    { toFun Φ := Φ.val
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have hρ : Function.Injective ρ := by
    intro p₁ p₂ h
    apply Subtype.ext
    ext X
    exact congrFun h X
  let ℓ := (LinearMap.proj (1 : G)).comp T
  obtain ⟨a, ha⟩ := linearForm_eq_finitelyManyEvaluations ρ hρ ℓ
  have hEval (k : Kc) : T (v k) (1 : G) =
      ∑ X ∈ a.support, a X * dilatedGauss z p (X * k.val.val) := by
    simpa only [ℓ, LinearMap.comp_apply, LinearMap.proj_apply, ρ, LinearMap.coe_mk,
      AddHom.coe_mk, htranslate] using ha (v k)
  have hC : Continuous Z := by
    have hb : Continuous b := (continuous_characterWeight d _).comp
      (determinantContinuous.continuous.comp continuous_subtype_val)
    have hZ : Z = fun k => b k * ∑ X ∈ a.support, a X * dilatedGauss z p (X * k.val.val) := by
      funext k
      simpa only [one_mul, Subgroup.coe_one, hEval] using hEq k 1
    rw [hZ]
    exact hb.mul (continuous_finsetSum _ fun X _ => continuous_const.mul
      ((dilatedGauss z p).continuous.comp
        (continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val))))
  refine ⟨hC, Submodule.finiteDimensional_of_le (S₂ := (restrictCompact.comp T).range)
    (Submodule.span_le.mpr ?_)⟩
  rintro _ ⟨k, rfl⟩
  refine ⟨b k • v k, ?_⟩
  rw [map_smul]
  funext x
  exact (hEq k x).symm

/-- Dilated Gaussian-polynomial Godement sections of compact-finite smaller standard vectors. -/
def dilatedGaussianGodementSections (d : ComplexCharacterData) (ds : List ComplexCharacterData) : Set (G → ℂ) :=
  {F | ∃ (z : ℂˣ) (p : Polynomials) (f : Smaller ds), F = godementSection ν d (dilatedGauss z p) f.val}

private def approximable (S : Submodule ℂ (Kc → ℂ)) : Submodule ℂ (Kc → ℂ) where
  carrier := {f | ∀ ε : ℝ, 0 < ε → ∃ g ∈ S, ∀ x, ‖f x - g x‖ ≤ ε}
  zero_mem' := fun ε hε => ⟨0, S.zero_mem, fun x => by simpa using hε.le⟩
  add_mem' := by
    intro f g hf hg ε hε
    obtain ⟨u, hu, hfu⟩ := hf (ε / 2) (by positivity)
    obtain ⟨v, hv, hgv⟩ := hg (ε / 2) (by positivity)
    refine ⟨u + v, S.add_mem hu hv, fun x => ?_⟩
    rw [Pi.add_apply, Pi.add_apply, show f x + g x - (u x + v x) = (f x - u x) + (g x - v x) by ring]
    exact (norm_add_le _ _).trans ((add_le_add (hfu x) (hgv x)).trans (by linarith))
  smul_mem' := by
    intro c f hf ε hε
    have hc : 0 < ‖c‖ + 1 := by positivity
    obtain ⟨g, hg, he⟩ := hf (ε / (‖c‖ + 1)) (div_pos hε hc)
    refine ⟨c • g, S.smul_mem c hg, fun x => ?_⟩
    rw [Pi.smul_apply, Pi.smul_apply, ← smul_sub, norm_smul]
    calc
      _ ≤ ‖c‖ * (ε / (‖c‖ + 1)) := mul_le_mul_of_nonneg_left (he x) (norm_nonneg _)
      _ = (‖c‖ / (‖c‖ + 1)) * ε := by ring
      _ ≤ ε := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right ((div_le_one hc).mpr (by linarith)) hε.le

/-- In a right half-plane of the added exponent, all larger compact-finite standard
vectors are spanned by the dilated Gaussian-polynomial Godement sections. -/
def ComplexGodementDilatedGaussianSpanningStatement : Prop :=
  0 < m → ∀ es : Fin m → ComplexCharacterData,
    ∃ M : ℕ, ∀ d : ComplexCharacterData,
      (m : ℝ) + M ≤ (d.exponent + ((m : ℂ) + 1) / 2).re →
      Larger d (List.ofFn es) ≤ Submodule.span ℂ (dilatedGaussianGodementSections d (List.ofFn es))

theorem complexGodementDilatedGaussianSpanning : ComplexGodementDilatedGaussianSpanningStatement (m := m) := by
  intro hm es
  let ds := List.ofFn es
  obtain ⟨M, hM⟩ := complexGodementStandardConvergence m hm ds List.length_ofFn
  obtain ⟨N, hN⟩ := complexGodementUniformApproximation hm ds List.length_ofFn
  refine ⟨max M N, fun d hd F hF => ?_⟩
  have hdM : (m : ℝ) + M ≤ (d.exponent + ((m : ℂ) + 1) / 2).re := by
    have h : (M : ℝ) ≤ ((max M N : ℕ) : ℝ) := by exact_mod_cast le_max_left M N
    exact (add_le_add le_rfl h).trans hd
  have hdN : (m : ℝ) + N ≤ (d.exponent + ((m : ℂ) + 1) / 2).re := by
    have h : (N : ℝ) ≤ ((max M N : ℕ) : ℝ) := by exact_mod_cast le_max_right M N
    exact (add_le_add le_rfl h).trans hd
  let A := Submodule.span ℂ (dilatedGaussianGodementSections (m := m) d ds)
  let S := A.map (restrictCompact (m := m))
  have hS' : S = Submodule.span ℂ (restrictCompact '' dilatedGaussianGodementSections d ds) :=
    Submodule.map_span _ _
  have hSreg : S ≤ compactFiniteContinuous m := by
    rw [hS']
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨z, p, f, rfl⟩, rfl⟩
    exact gaussianSection_regular d f.val (fun Φ g => hM d Φ f.val f.2.1 hdM g) z p
  have hShift (k : Kc) : S ≤ S.comap (rightShift k) := by
    conv_lhs => rw [hS']
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨z, p, f, rfl⟩, rfl⟩
    obtain ⟨q, _, hq⟩ := exists_gaussianPolynomial_mul_unitary p k
    have testEq : translateTest k.val (dilatedGauss z p) = (dilatedGauss z q : Mat → ℂ) := by
      funext X
      simpa only [translateTest, dilatedGauss_apply, Matrix.smul_mul] using hq ((z : ℂ) • X)
    let b := characterWeight d ((m : ℂ) / 2) (determinant k.val)
    have he : rightShift k (restrictCompact (godementSection ν d (dilatedGauss z p) f.val)) =
        b • restrictCompact (godementSection ν d (dilatedGauss z q) f.val) := by
      funext x
      simpa only [rightShift, LinearMap.funLeft_apply, restrictCompact, LinearMap.pi_apply,
        LinearMap.proj_apply, Subgroup.coe_mul, b, Pi.smul_apply, smul_eq_mul, testEq] using
        godementSection_right_mul ν d (dilatedGauss z p) f.val x.val k.val
    change rightShift k (restrictCompact (godementSection ν d (dilatedGauss z p) f.val)) ∈ S
    rw [he, hS']
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨z, q, f, rfl⟩, rfl⟩)
  have hFfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : Kc =>
      Whittaker.rightTranslation ℂ G k.val F)) := (mem_kFiniteVectors_iff _ _ _).mp hF.2
  have hFfin' : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : Kc =>
      fun x : Kc => restrictCompact F (x * k))) := by
    let U := Submodule.span ℂ (Set.range fun k : Kc => Whittaker.rightTranslation ℂ G k.val F)
    let : FiniteDimensional ℂ U := hFfin
    refine Submodule.finiteDimensional_of_le (S₂ := U.map restrictCompact) (Submodule.span_le.mpr ?_)
    rintro _ ⟨k, rfl⟩
    exact Submodule.mem_map.mpr ⟨_, Submodule.subset_span (Set.mem_range_self k), rfl⟩
  have hFapprox : restrictCompact F ∈ approximable S := by
    have hle : Submodule.span ℂ (compactGodementSections ν d ds) ≤
        (approximable S).comap restrictCompact := by
      apply Submodule.span_le.mpr
      rintro _ ⟨Φ, f, hΦc, _, _, rfl⟩
      intro ε hε
      obtain ⟨l, z, p, hBound⟩ := hN d f.val f.2.1 hdN Φ hΦc ε hε
      let g := ∑ j, restrictCompact (godementSection ν d (dilatedGauss (z j) (p j)) f.val)
      have hg : g ∈ S := by
        rw [hS']
        exact Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨_, ⟨z j, p j, f, rfl⟩, rfl⟩
      have hTest (j : Fin l) : (dilatedGauss (z j) (p j) : Mat → ℂ) =
          fun X => gaussianPolynomial (p j) ((z j : ℂ) • X) :=
        funext (dilatedGauss_apply (z j) (p j))
      exact ⟨g, hg, fun x => by
        simpa only [g, Finset.sum_apply, restrictCompact, LinearMap.pi_apply, LinearMap.proj_apply,
          hTest] using hBound x⟩
    apply hle
    rw [complexGodementCompactSpanning ν d es]
    exact hF
  let : CompactSpace Kc := ComplexDuality.compactSpace_unitaryCompact (m + 1)
  have hSmem : restrictCompact F ∈ S :=
    compactFiniteUniformSpan (ComplexDuality.unitaryHaar _) S (fun g hg => (hSreg hg).1)
      (fun g hg k => hShift k hg) (fun g hg => (hSreg hg).2) (restrictCompact F)
      (hF.1.1.continuous.comp continuous_subtype_val) hFfin' hFapprox
  obtain ⟨F', hF', hEq⟩ := Submodule.mem_map.mp hSmem
  have hc (F₀ : G → ℂ) (hF₀ : F₀ ∈ A) (a : Fin (m + 1) → ℂˣ)
      (u : Langlands.GeneralLinear.upperUnipotent (m + 1) ℂ) (g : G) :
      F₀ (Iwasawa.diagonalUnits a * u.val * g) =
        principalSeriesCharacter ℂ (m + 1) (complexPositionCharacter (d :: ds)) a * F₀ g := by
    induction hF₀ using Submodule.span_induction with
    | mem V hV =>
        obtain ⟨z, p, f, rfl⟩ := hV
        exact godementSection_covariant ν d ds (dilatedGauss z p) f.2.1 a u g
    | zero => simp
    | add x y _ _ hx hy => simp only [Pi.add_apply, hx, hy, mul_add]
    | smul c x _ hx => simp only [Pi.smul_apply, smul_eq_mul, hx, mul_left_comm]
  have he : F' = F := by
    funext g
    obtain ⟨a, u, k, hk, rfl⟩ :=
      ComplexDuality.exists_diagonalUnits_mul_upperUnipotent_mul_unitary g
    rw [hc F' hF', hF.1.2 a u k]
    exact congrArg (_ * ·) (congrFun hEq ⟨k, hk⟩)
  exact he ▸ hF'

end Langlands.Global.RankinSelbergGlobal.ComplexGodement
