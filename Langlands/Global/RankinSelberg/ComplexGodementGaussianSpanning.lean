import Langlands.Global.RankinSelberg.CompactPairingSpanning
import Langlands.Global.RankinSelberg.ComplexGodementCompactSpanning
import Langlands.Global.RankinSelberg.ComplexGodementGaussianPairing

/-! # Spanning the complex standard module by polynomial Gaussian Godement sections -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap Langlands.Archimedean.ComplexDuality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodement

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.Archimedean.ComplexDuality (unitaryHaar
  exists_diagonalUnits_mul_upperUnipotent_mul_unitary)
open Langlands.Archimedean.ComplexGramFormula (phaseUnit)
open Langlands.Archimedean.ComplexPrincipalSeriesExtension (phaseMatrix phaseMatrix_val)
open Langlands.Archimedean.FiniteTranslationSpan (rightSpan)
open Langlands.Archimedean.ComplexGeneralLinearHaarDensity (complexGeneralLinearHaar)
open Langlands.Whittaker (rightTranslation)
open ComplexGodementGaussianPolynomial (Coordinates gaussianPolynomial
  finiteDimensional_translateTest_gaussianPolynomial)
open ComplexJacquet (compactPairingSpanning)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel

variable {r : ℕ}

local notation "m" => (r + 1 : ℕ)
local notation "H" => Langlands.GeneralLinear (r + 1) ℂ
local notation "G" => Langlands.GeneralLinear (r + 1 + 1) ℂ
local notation "U" => unitaryCompact ℂ (r + 1 + 1)
local notation "KU" => Matrix.unitaryGroup (Fin (r + 1 + 1)) ℂ
local notation "Rect" => Matrix (Fin (r + 1)) (Fin (r + 1 + 1)) ℂ
local notation "Poly" => MvPolynomial (Coordinates (r + 1) (r + 1 + 1)) ℂ
local notation "Larger" => fun d ds => kFiniteFunctions
  (complexStandardModule (r + 1 + 1) (d :: ds)) (unitaryCompact ℂ (r + 1 + 1))
local notation "Smaller" => fun ds => kFiniteFunctions
  (complexStandardModule (r + 1) ds) (unitaryCompact ℂ (r + 1))

private def restrictUnitary : (G → ℂ) →ₗ[ℂ] (U → ℂ) :=
  LinearMap.pi fun k => LinearMap.proj (R := ℂ) k.val

private def schwartzFunctions : Submodule ℂ (Rect → ℂ) :=
  LinearMap.range
    ({ toFun Φ := Φ
       map_add' _ _ := rfl
       map_smul' _ _ := rfl } : 𝓢(Rect, ℂ) →ₗ[ℂ] (Rect → ℂ))

private def sectionLinear (ν : Measure H) (d : ComplexCharacterData) (f : H → ℂ)
    (hconv : ∀ (Φ : 𝓢(Rect, ℂ)) g, Integrable (godementSectionIntegrand d Φ f g) ν) :
    schwartzFunctions (r := r) →ₗ[ℂ] (G → ℂ) where
  toFun Φ := godementSection ν d Φ.val f
  map_add' Φ Ψ := by
    funext g
    obtain ⟨φ, hφ⟩ := Φ.2
    obtain ⟨ψ, hψ⟩ := Ψ.2
    have hΦ : Integrable (godementSectionIntegrand d Φ.val f g) ν := hφ ▸ hconv φ g
    have hΨ : Integrable (godementSectionIntegrand d Ψ.val f g) ν := hψ ▸ hconv ψ g
    simp only [godementSection, Submodule.coe_add, Pi.add_apply]
    have h : godementSectionIntegrand d (Φ.val + Ψ.val) f g =
        godementSectionIntegrand d Φ.val f g + godementSectionIntegrand d Ψ.val f g := by
      funext x
      simp only [godementSectionIntegrand, Pi.add_apply, add_mul]
    rw [h]
    simp only [Pi.add_apply, integral_add hΦ hΨ, mul_add]
  map_smul' c Φ := by
    funext g
    simp only [godementSection, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    have h : godementSectionIntegrand d (c • Φ.val) f g =
        fun x => c * godementSectionIntegrand d Φ.val f g x := by
      funext x
      simp only [godementSectionIntegrand, Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [h, integral_const_mul, mul_left_comm]

private abbrev schwartzTestOrbit (Φ : 𝓢(Rect, ℂ)) : Submodule ℂ (Rect → ℂ) :=
  Submodule.span ℂ (Set.range fun k : U => translateTest k.val Φ)

private theorem schwartzTestOrbit_le (Φ : 𝓢(Rect, ℂ)) : schwartzTestOrbit Φ ≤ schwartzFunctions := by
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  let e : Rect ≃L[ℝ] Rect :=
    ({ toFun X := X * k.val.val
       invFun X := X * k.val⁻¹.val
       left_inv X := by simp [Matrix.mul_assoc]
       right_inv X := by simp [Matrix.mul_assoc]
       map_add' X Y := Matrix.add_mul X Y _
       map_smul' c X := Matrix.smul_mul c X _ } : Rect ≃ₗ[ℝ] Rect).toContinuousLinearEquiv
  exact ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e Φ, rfl⟩

private theorem schwartzSection_continuous_unitary (ν : Measure H)
    (d : ComplexCharacterData) (f : H → ℂ) (Φ : 𝓢(Rect, ℂ))
    (hfinite : FiniteDimensional ℂ (schwartzTestOrbit Φ))
    (hconv : ∀ (Ψ : 𝓢(Rect, ℂ)) g, Integrable (godementSectionIntegrand d Ψ f g) ν) :
    Continuous (fun k : U => godementSection ν d Φ f k.val) := by
  let V := schwartzTestOrbit Φ
  let : FiniteDimensional ℂ V := hfinite
  let T := (sectionLinear ν d f hconv).comp (Submodule.inclusion (schwartzTestOrbit_le Φ))
  let L : V →ₗ[ℂ] ℂ := (LinearMap.proj 1).comp T
  obtain ⟨j, x, c, hL⟩ := InductionStages.exists_eval_sum V L
  let v (k : U) : V := ⟨translateTest k.val Φ, Submodule.subset_span ⟨k, rfl⟩⟩
  have h (k : U) : godementSection ν d Φ f k.val =
      characterWeight d ((m : ℂ) / 2) (determinant k.val) *
        ∑ i : Fin j, c i * Φ (x i * k.val.val) := by
    have hk := godementSection_right_mul ν d Φ f 1 k.val
    rw [one_mul] at hk
    refine hk.trans (congrArg (fun z => characterWeight d ((m : ℂ) / 2) (determinant k.val) * z) ?_)
    exact hL (v k)
  simp_rw [h]
  refine ((continuous_characterWeight d _).comp (determinantContinuous.continuous.comp
    continuous_subtype_val)).mul (continuous_finsetSum _ fun i _ => continuous_const.mul ?_)
  exact Φ.continuous.comp
    (continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val))

private theorem schwartzSection_finiteOrbit (ν : Measure H)
    (d : ComplexCharacterData) (f : H → ℂ) (Φ : 𝓢(Rect, ℂ))
    (hfinite : FiniteDimensional ℂ (schwartzTestOrbit Φ))
    (hconv : ∀ (Ψ : 𝓢(Rect, ℂ)) g, Integrable (godementSectionIntegrand d Ψ f g) ν) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : U =>
      rightTranslation ℂ G k.val (godementSection ν d Φ f))) := by
  let V := schwartzTestOrbit Φ
  let : FiniteDimensional ℂ V := hfinite
  let T := (sectionLinear ν d f hconv).comp (Submodule.inclusion (schwartzTestOrbit_le Φ))
  refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range T) (Submodule.span_le.mpr ?_)
  rintro _ ⟨k, rfl⟩
  let Ψ : V := ⟨translateTest k.val Φ, Submodule.subset_span ⟨k, rfl⟩⟩
  let c := characterWeight d ((m : ℂ) / 2) (determinant k.val)
  refine ⟨c • Ψ, ?_⟩
  rw [map_smul]
  funext g
  exact (godementSection_right_mul ν d Φ f g k.val).symm

set_option maxHeartbeats 500000 in
private theorem mem_standard_of_compact_covariance (d : ComplexCharacterData)
    (ds : List ComplexCharacterData) (F : G → ℂ)
    (hC : Continuous fun k : U => F k.val)
    (hOrb : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : U =>
      rightTranslation ℂ G k.val F)))
    (hCov : ∀ (a : Fin (m + 1) → ℂˣ) (u : GeneralLinear.upperUnipotent (m + 1) ℂ) (g : G),
      F (Iwasawa.diagonalUnits a * u.val * g) =
        principalSeriesCharacter ℂ (m + 1) (complexPositionCharacter (d :: ds)) a * F g) :
    F ∈ Larger d ds := by
  let θ (k : KU) : U := ⟨Unitary.toUnits k, k.2⟩
  let φ (k : KU) : ℂ := F (Unitary.toUnits k)
  have hθ : Continuous θ := continuous_unitary_toUnits.subtype_mk fun k => k.2
  have hφ : Continuous φ := hC.comp hθ
  have hphase (a : Fin (m + 1) → ℂˣ) (k : KU) :
      φ (phaseMatrix a * k) =
        principalSeriesCharacter ℂ (m + 1) (complexPositionCharacter (d :: ds))
          (fun i => phaseUnit (a i)) * φ k := by
    have hp : Unitary.toUnits (phaseMatrix a) = Iwasawa.diagonalUnits (fun i => phaseUnit (a i)) := by
      apply Units.ext
      change (phaseMatrix a).val = _
      rw [phaseMatrix_val]
      rfl
    change F (Unitary.toUnits (phaseMatrix a * k)) = _ * F (Unitary.toUnits k)
    rw [map_mul, hp]
    have hc := hCov (fun i => phaseUnit (a i)) 1 (Unitary.toUnits k)
    simpa only [Subgroup.coe_one, mul_one] using hc
  let V := Submodule.span ℂ (Set.range fun k : U => rightTranslation ℂ G k.val F)
  let : FiniteDimensional ℂ V := hOrb
  let ρ : (G → ℂ) →ₗ[ℂ] (KU → ℂ) := LinearMap.pi fun k => LinearMap.proj (R := ℂ) (Unitary.toUnits k)
  have hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : KU => fun x => φ (x * k))) := by
    apply Submodule.finiteDimensional_of_le (S₂ := V.map ρ)
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    refine ⟨rightTranslation ℂ G (θ k).val F, Submodule.subset_span ⟨θ k, rfl⟩, ?_⟩
    funext x
    change F (Unitary.toUnits x * Unitary.toUnits k) = F (Unitary.toUnits (x * k))
    rw [map_mul]
  obtain ⟨F', hF', hF'U⟩ := complexPrincipalSeriesExtension (m + 1) (d :: ds) φ hφ hfin hphase
  have heq : F' = F := by
    funext g
    obtain ⟨a, u, k, hk, rfl⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitary g
    let k' : KU := ⟨k.val, hk⟩
    have hk' : F' k = F k := by
      have h := hF'U k'
      change F' (Unitary.toUnits k') = F (Unitary.toUnits k') at h
      rw [show Unitary.toUnits k' = k from Units.ext rfl] at h
      exact h
    rw [hF'.1.2 a u k, hCov, hk']
  rw [← heq]
  exact hF'

/-- An absolutely convergent Godement section of a right unitary-finite Schwartz test
belongs to the compact-finite standard module. -/
theorem schwartzSection_standard (ν : Measure H) [ν.IsMulRightInvariant]
    (d : ComplexCharacterData) (ds : List ComplexCharacterData) (f : H → ℂ)
    (hf : f ∈ complexStandardModule m ds) (Φ : 𝓢(Rect, ℂ))
    (hfinite : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : U => translateTest k.val Φ)))
    (hconv : ∀ (Ψ : 𝓢(Rect, ℂ)) g, Integrable (godementSectionIntegrand d Ψ f g) ν) :
    godementSection ν d Φ f ∈ Larger d ds :=
  mem_standard_of_compact_covariance d ds _
    (schwartzSection_continuous_unitary ν d f Φ hfinite hconv)
    (schwartzSection_finiteOrbit ν d f Φ hfinite hconv)
    (godementSection_covariant ν d ds Φ hf)

private theorem gaussianSection_standard (ν : Measure H) [ν.IsMulRightInvariant]
    (d : ComplexCharacterData) (ds : List ComplexCharacterData) (f : H → ℂ)
    (hf : f ∈ complexStandardModule m ds) (P : Poly)
    (hconv : ∀ (Φ : 𝓢(Rect, ℂ)) g, Integrable (godementSectionIntegrand d Φ f g) ν) :
    godementSection ν d (gaussianPolynomial P) f ∈ Larger d ds :=
  schwartzSection_standard ν d ds f hf (gaussianPolynomial P)
    (finiteDimensional_translateTest_gaussianPolynomial P) hconv

/-- At fixed angular weights, Godement sections formed with the same right unitary-finite
Schwartz test have their compact restrictions in one finite-dimensional subspace. -/
theorem finiteDimensional_schwartzSection_profiles {P : Type*} (ν : Measure H)
    (d : P → ComplexCharacterData) (f : P → H → ℂ) (θ : KU → ℂ)
    (hθ : ∀ p k, characterWeight (d p) ((m : ℂ) / 2) (determinant (Unitary.toUnits k)) = θ k)
    (Φ : 𝓢(Rect, ℂ))
    (hfinite : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : U => translateTest k.val Φ)))
    (hconv : ∀ p (Ψ : 𝓢(Rect, ℂ)) g, Integrable (godementSectionIntegrand (d p) Ψ (f p) g) ν) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun (p : P) (k : KU) =>
      godementSection ν (d p) Φ (f p) (Unitary.toUnits k))) := by
  classical
  let V := schwartzTestOrbit Φ
  let : FiniteDimensional ℂ V := hfinite
  let b := Module.finBasis ℂ V
  let u (k : KU) : V := ⟨translateTest (Unitary.toUnits k) Φ,
    Submodule.subset_span ⟨⟨Unitary.toUnits k, k.2⟩, rfl⟩⟩
  let h (i : Fin (Module.finrank ℂ V)) (k : KU) := θ k * b.repr (u k) i
  have hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range h)) :=
    FiniteDimensional.span_of_finite _ (Set.finite_range _)
  apply Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range h))
  apply Submodule.span_le.mpr
  rintro _ ⟨p, rfl⟩
  let T := (sectionLinear ν (d p) (f p) (hconv p)).comp (Submodule.inclusion (schwartzTestOrbit_le Φ))
  let L : V →ₗ[ℂ] ℂ := (LinearMap.proj (1 : G)).comp T
  have hEq : (fun k : KU => godementSection ν (d p) Φ (f p) (Unitary.toUnits k)) =
      ∑ i : Fin (Module.finrank ℂ V), L (b i) • h i := by
    funext k
    have hR := godementSection_right_mul ν (d p) Φ (f p) 1 (Unitary.toUnits k)
    rw [one_mul, hθ p k] at hR
    change _ = θ k * L (u k) at hR
    rw [hR, ← b.sum_repr (u k), map_sum, Finset.mul_sum, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    change θ k * (b.repr (u k) i * L (b i)) = L (b i) * (θ k * b.repr (u k) i)
    ring
  change (fun k : KU => godementSection ν (d p) Φ (f p) (Unitary.toUnits k)) ∈
    Submodule.span ℂ (Set.range h)
  rw [hEq]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Godement sections of polynomial Gaussian tests with compact-finite smaller inputs. -/
def gaussianGodementSections (ν : Measure H) (d : ComplexCharacterData) (ds : List ComplexCharacterData) :
    Set (G → ℂ) :=
  Set.range fun x : Poly × Smaller ds => godementSection ν d (gaussianPolynomial x.1) x.2.val

/-- Under a sufficient bound on the real part of the adjoining exponent,
polynomial Gaussian Godement sections span the whole compact-finite standard module. -/
def ComplexGodementGaussianSpanningStatement : Prop :=
  ∀ (ν : Measure H) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] (es : Fin m → ComplexCharacterData),
    ∃ M : ℕ, ∀ d : ComplexCharacterData,
      (m : ℝ) + M ≤ (d.exponent + (((m : ℂ) + 1) / 2)).re →
      Submodule.span ℂ (gaussianGodementSections ν d (List.ofFn es)) = Larger d (List.ofFn es)

set_option maxHeartbeats 700000 in
theorem complexGodementGaussianSpanning : ComplexGodementGaussianSpanningStatement (r := r) := by
  intro ν hν hνr es
  let eH := Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) m
  let : LocallyCompactSpace H := eH.locallyCompactSpace
  let : SecondCountableTopology H := eH.secondCountableTopology
  let ds := List.ofFn es
  have hlen : ds.length = m := List.length_ofFn
  obtain ⟨M₁, hM₁⟩ := complexGodementStandardConvergence m (Nat.succ_pos r) ds hlen
  obtain ⟨M₂, hM₂⟩ := complexGodementGaussianPairing (r := r) ν ds hlen
  refine ⟨max M₁ M₂, fun d hd => ?_⟩
  have hm₁ : (M₁ : ℝ) ≤ ((max M₁ M₂ : ℕ) : ℝ) := by exact_mod_cast le_max_left M₁ M₂
  have hm₂ : (M₂ : ℝ) ≤ ((max M₁ M₂ : ℕ) : ℝ) := by exact_mod_cast le_max_right M₁ M₂
  have hd₁ : (m : ℝ) + M₁ ≤ (d.exponent + (((m : ℂ) + 1) / 2)).re :=
    (add_le_add (le_refl (m : ℝ)) hm₁).trans hd
  have hd₂ : (m : ℝ) + M₂ ≤ (d.exponent + (((m : ℂ) + 1) / 2)).re :=
    (add_le_add (le_refl (m : ℝ)) hm₂).trans hd
  have hconv {f : H → ℂ} (hf : f ∈ complexStandardModule m ds) (Φ : 𝓢(Rect, ℂ)) (g : G) :
      Integrable (godementSectionIntegrand d Φ f g) ν := by
    rw [Measure.isMulLeftInvariant_eq_smul ν (complexGeneralLinearHaar m)]
    exact (hM₁ d Φ f hf hd₁ g).smul_measure_nnreal
  let A := Submodule.span ℂ (gaussianGodementSections ν d ds)
  have hA : A ≤ Larger d ds := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨P, f⟩, rfl⟩
    exact gaussianSection_standard ν d ds f.val f.2.1 P (hconv f.2.1)
  refine le_antisymm hA ?_
  change Larger d (List.ofFn es) ≤ A
  rw [← complexGodementCompactSpanning ν d es]
  apply Submodule.span_le.mpr
  rintro _ ⟨Φ, f, hc, hfull, hΦfin, rfl⟩
  let F := godementSection ν d Φ f.val
  have hF : F ∈ Larger d ds :=
    complexGodementKFinite m ν d ds Φ (Φ.smooth ⊤) hc hfull hΦfin f.val f.2.1
  let ρ := restrictUnitary (r := r)
  let S := Set.range fun P : Poly => ρ (godementSection ν d (gaussianPolynomial P) f.val)
  let μ := unitaryHaar (m + 1)
  have hfin (v : Larger d ds) : FiniteDimensional ℂ (rightSpan (ρ v.val)) := by
    let V := Submodule.span ℂ (Set.range fun k : U => rightTranslation ℂ G k.val v.val)
    let : FiniteDimensional ℂ V := (mem_kFiniteVectors_iff _ _ _).mp v.2.2
    refine Submodule.finiteDimensional_of_le (S₂ := V.map ρ) (Submodule.span_le.mpr ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨rightTranslation ℂ G k.val v.val, Submodule.subset_span ⟨k, rfl⟩, rfl⟩
  have hS (g : U → ℂ) (hg : g ∈ S) :
      FiniteDimensional ℂ (rightSpan g) ∧ rightSpan g ≤ Submodule.span ℂ S := by
    obtain ⟨P, rfl⟩ := hg
    refine ⟨hfin ⟨_, gaussianSection_standard ν d ds f.val f.2.1 P (hconv f.2.1)⟩, ?_⟩
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    obtain ⟨Q, hQ⟩ := exists_rightTranslate_gaussianPolynomial P k
    have hQ' : translateTest k.val (gaussianPolynomial P) = (gaussianPolynomial Q : Rect → ℂ) :=
      funext hQ
    let c := characterWeight d ((m : ℂ) / 2) (determinant k.val)
    have he : rightTranslation ℂ U k (ρ (godementSection ν d (gaussianPolynomial P) f.val)) =
        c • ρ (godementSection ν d (gaussianPolynomial Q) f.val) := by
      funext x
      change godementSection ν d (gaussianPolynomial P) f.val (x.val * k.val) =
        c * godementSection ν d (gaussianPolynomial Q) f.val x.val
      rw [godementSection_right_mul, hQ']
    change rightTranslation ℂ U k (ρ (godementSection ν d (gaussianPolynomial P) f.val)) ∈
      Submodule.span ℂ S
    rw [he]
    exact (Submodule.span ℂ S).smul_mem c (Submodule.subset_span ⟨Q, rfl⟩)
  have hPair (w : U → ℂ) (hw : Continuous w) := hM₂ d f.val f.2.1 hd₂ μ w hw
  have hρF : ρ F ∈ Submodule.span ℂ S := by
    refine compactPairingSpanning U μ (ρ F) S (hF.1.1.continuous.comp continuous_subtype_val)
      (hfin ⟨F, hF⟩) hS ?_ ?_
    · rintro g ⟨P, rfl⟩ w hw
      exact (hPair w hw).1 P
    · intro w hw h0
      exact (hPair w hw).2 (fun P => h0 _ ⟨P, rfl⟩) Φ hc
  have hSA : Submodule.span ℂ S ≤ A.map ρ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨P, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨(P, f), rfl⟩, rfl⟩
  obtain ⟨F', hF'A, hF'⟩ := hSA hρF
  have he : F' = F := ComplexPrincipalSeriesExtension.eq_of_eqOn_unitary (hA hF'A).1 hF.1
    (fun k hk => congrFun hF' (⟨k, hk⟩ : U))
  change F ∈ A
  exact he ▸ hF'A

end Langlands.Global.RankinSelbergGlobal.ComplexGodement
