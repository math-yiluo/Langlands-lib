import Langlands.Global.RankinSelberg.ComplexCompactProfileFamily
import Langlands.Global.RankinSelberg.ComplexGodementCompactSeparation
import Langlands.Global.RankinSelberg.ComplexGodementKFinite
import Langlands.Representation.Archimedean.FiniteTranslationSpan

/-! # A fixed finite-dimensional span of complex Godement compact profiles -/

noncomputable section

open MeasureTheory Set
open scoped Classical ContDiff Manifold Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodement

open Langlands.Archimedean (characterOfParams complexStandardModule complexPositionCharacter
  unitaryCompact rightTranslation_mem_kFiniteFunctions_principalSeries)
open Langlands.Archimedean.ComplexGramFormula (phaseUnit)
open Langlands.Archimedean.ComplexMaximalParabolicIntegration (normSqC normSqC_det_unitary)
open Langlands.Archimedean.ComplexPrincipalSeriesExtension (extensionLinear phaseMatrix eq_of_eqOn_unitary)
open Langlands.Archimedean.FiniteTranslationSpan (coefficient coefficient_mem rightOn rightSpan twoSidedSpan
  mem_twoSidedSpan translate_mem_twoSidedSpan finiteDimensional_twoSidedSpan)
open Langlands.GeneralLinear (determinant)
open Langlands.Whittaker (rightTranslation)
open ComplexCompactProfileFamily (characterList IsCompactProfile standardSection standardSection_mem
  standardSection_unitary compactRestriction compactRestriction_isCompactProfile standardSection_compactRestriction)

variable {m : ℕ}
local notation "G" => Langlands.GeneralLinear (m + 1) ℂ
local notation "H" => Langlands.GeneralLinear m ℂ
local notation "U" => Matrix.unitaryGroup (Fin (m + 1)) ℂ
local notation "U₀" => Matrix.unitaryGroup (Fin m) ℂ
local notation "P" => Fin (m + 1) → ℂ
local notation "L" => Fin (m + 1) → ℤ
local notation "Rect" => Matrix (Fin m) (Fin (m + 1)) ℂ
local instance finiteProfilesGLMeasurable (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℂ) := borel _
local instance finiteProfilesGLBorel (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℂ) := ⟨rfl⟩

private def phaseSpace (l : L) : Submodule ℂ (U → ℂ) where
  carrier := {f | ∀ (a : Fin (m + 1) → ℂˣ) (k : U),
    f (phaseMatrix a * k) = (∏ i, ((phaseUnit (a i) : ℂˣ) : ℂ) ^ l i) * f k}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg a k
    simp only [Pi.add_apply, hf a k, hg a k, mul_add]
  smul_mem' := by
    intro c f hf a k
    simp only [Pi.smul_apply, smul_eq_mul, hf a k]
    ring

private theorem mem_phaseSpace {l : L} {f : U → ℂ} (hf : IsCompactProfile l f) : f ∈ phaseSpace l := hf.2.2

private theorem continuous_of_mem_twoSidedSpan {f v : U → ℂ} (hf : Continuous f) (hv : v ∈ twoSidedSpan f) :
    Continuous v := by
  unfold twoSidedSpan at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    rcases hv with ⟨⟨x, y⟩, rfl⟩
    exact hf.comp ((continuous_const.mul continuous_id).mul continuous_const)
  | zero => exact continuous_const
  | add f g _ _ hf hg => exact hf.add hg
  | smul c f _ hf => exact hf.const_smul c

private abbrev Profiles (l : L) (V : Submodule ℂ (U → ℂ)) := V ⊓ phaseSpace l

private theorem right_phase (l : L) (k : U) {f : U → ℂ} (hf : f ∈ phaseSpace l) :
    rightTranslation ℂ U k f ∈ phaseSpace l := by
  intro a x
  change f (phaseMatrix a * x * k) = _ * f (x * k)
  rw [mul_assoc]
  exact hf a (x * k)

private theorem admissible {l : L} {V : Submodule ℂ (U → ℂ)} [FiniteDimensional ℂ V]
    (hVc : ∀ v : V, Continuous v.val)
    (hVr : ∀ k (v : V), rightTranslation ℂ U k v.val ∈ V) (v : Profiles l V) :
    IsCompactProfile l v.val := by
  refine ⟨hVc ⟨v.val, v.2.1⟩, ?_, v.2.2⟩
  apply Submodule.finiteDimensional_of_le (S₂ := V)
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  exact hVr k ⟨v.val, v.2.1⟩

/-- The angular weights retained in the smaller inducing representation. -/
def smallerWeights (l : L) : Fin m → ℤ := fun i => l i.succ

/-- The radial exponents retained in the smaller inducing representation. -/
def smallerExponents (p : P) : Fin m → ℂ := fun i => p i.succ

/-- The leading inducing character of the larger upper-Borel module. -/
def addedCharacter (l : L) (p : P) := characterOfParams (l 0) (p 0)

/-- The inducing characters of the smaller upper-Borel module. -/
def retainedCharacters (l : L) (p : P) := characterList (smallerWeights l) (smallerExponents p)

theorem characterList_cons (l : L) (p : P) : characterList l p = addedCharacter l p :: retainedCharacters l p := by
  unfold characterList retainedCharacters
  rw [List.ofFn_succ]
  rfl

private abbrev Cutoff := {χ : 𝓢(Rect, ℂ) // IsGodementCofactorCutoff χ}

/-- Admissible compact profiles of the smaller representation at the retained angular weights. -/
abbrev SmallerProfile (l : L) := {v : U₀ → ℂ // IsCompactProfile (smallerWeights l) v}

/-- The smaller standard section at the retained radial exponents. -/
def smallerSection {l : L} (p : P) (v : SmallerProfile l) : H → ℂ :=
  standardSection (smallerExponents p) v.val

private theorem smallerSection_continuous {l : L} (p : P) (v : SmallerProfile l) :
    Continuous (smallerSection p v) := (standardSection_mem v.2 (smallerExponents p)).1.1.continuous

private theorem largerSection_mem {l : L} {v : U → ℂ} (hv : IsCompactProfile l v) (p : P) :
    standardSection p v ∈ complexStandardModule (m + 1) (addedCharacter l p :: retainedCharacters l p) := by
  rw [← characterList_cons]
  exact (standardSection_mem hv p).1

private def standardSectionLinear (p : P) : (U → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun := standardSection p
  map_add' f g := (extensionLinear _).map_add f g
  map_smul' c f := (extensionLinear _).map_smul c f

private theorem right_standardSection {l : L} {v : U → ℂ} (hv : IsCompactProfile l v)
    (p : P) (k : U) (hkv : IsCompactProfile l (rightTranslation ℂ U k v)) :
    rightTranslation ℂ G (Unitary.toUnits k) (standardSection p v) =
      standardSection p (rightTranslation ℂ U k v) := by
  have hk : Unitary.toUnits k ∈ unitaryCompact ℂ (m + 1) := k.2
  have htr := rightTranslation_mem_kFiniteFunctions_principalSeries
    (complexPositionCharacter (characterList l p)) (unitaryCompact ℂ (m + 1)) (standardSection_mem hv p) hk
  refine eq_of_eqOn_unitary htr.1 (standardSection_mem hkv p).1 fun g hg => ?_
  let x : U := ⟨g.val, hg⟩
  have hx : Unitary.toUnits x = g := Units.ext rfl
  rw [← hx]
  change standardSection p v (Unitary.toUnits x * Unitary.toUnits k) = _
  rw [← map_mul, standardSection_unitary, standardSection_unitary]
  rfl

private theorem weight_at_unitary (l : L) (p q : P) (k : unitaryCompact ℂ (m + 1)) :
    characterWeight (addedCharacter l p) ((m : ℂ) / 2) (determinant k.val) =
      ((addedCharacter l q).character (determinant k.val) : ℂ) := by
  let z := determinant k.val
  have hN : normSqC (z : ℂ) = 1 := normSqC_det_unitary k
  have hs : ‖(z : ℂ)‖ ^ 2 = 1 := by
    change ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) = 1 at hN
    exact_mod_cast hN
  have hn : ‖(z : ℂ)‖ = 1 := by
    simpa only [Real.sqrt_sq (norm_nonneg (z : ℂ)), Real.sqrt_one] using congrArg Real.sqrt hs
  change ((addedCharacter l p).character z : ℂ) * normSqC (z : ℂ) ^ ((m : ℂ) / 2) =
    ((addedCharacter l q).character z : ℂ)
  rw [hN, Complex.one_cpow, mul_one, (addedCharacter l p).character_eq, (addedCharacter l q).character_eq, hn]
  simp [addedCharacter]

private def cofactorSchwartz {l : L} (q : P) (χ : Cutoff (m := m)) {v : U → ℂ}
    (hv : IsCompactProfile l v) : 𝓢(Rect, ℂ) :=
  let h := χ.2.cofactorTest_regular (addedCharacter l q) (retainedCharacters l q) (largerSection_mem hv q)
  h.2.1.toSchwartzMap h.1

private def cofactorEval {l : L} {A : Submodule ℂ (U → ℂ)} (hA : ∀ v : A, IsCompactProfile l v.val)
    (ν : Measure H) [IsLocallyFiniteMeasure ν] (p q : P) (χ : Cutoff (m := m)) (f : SmallerProfile l) :
    Module.Dual ℂ A := by
  let T := (cofactorTest χ.val).comp ((standardSectionLinear q).comp A.subtype)
  let T' := T.codRestrict (godementTests m) fun v => by
    obtain ⟨hc, hs, hf⟩ := χ.2.cofactorTest_regular (addedCharacter l q) (retainedCharacters l q) (largerSection_mem (hA v) q)
    exact ⟨hc.continuous, hs, hf⟩
  exact (LinearMap.proj (R := ℂ) (1 : G)).comp ((godementSectionLinear ν (addedCharacter l p)
    (smallerSection_continuous p f)).comp T')

private theorem cofactorEval_apply {l : L} {A : Submodule ℂ (U → ℂ)} (hA : ∀ v : A, IsCompactProfile l v.val)
    (ν : Measure H) [IsLocallyFiniteMeasure ν] (p q : P) (χ : Cutoff (m := m)) (f : SmallerProfile l) (v : A) :
    cofactorEval hA ν p q χ f v =
      godementSection ν (addedCharacter l p) (cofactorTest χ.val (standardSection q v.val)) (smallerSection p f) 1 := rfl

private theorem compactRestriction_cofactor {l : L} {A : Submodule ℂ (U → ℂ)}
    (hA : ∀ v : A, IsCompactProfile l v.val) (hr : ∀ k (v : A), rightTranslation ℂ U k v.val ∈ A)
    (ν : Measure H) [IsLocallyFiniteMeasure ν] (p q : P) (χ : Cutoff (m := m)) (f : SmallerProfile l) (v : A) :
    compactRestriction (godementSection ν (addedCharacter l p) (cofactorTest χ.val (standardSection q v.val))
      (smallerSection p f)) = coefficient A hr v (cofactorEval hA ν p q χ f) := by
  funext k
  let k' : unitaryCompact ℂ (m + 1) := ⟨Unitary.toUnits k, k.2⟩
  let F := standardSection q v.val
  let Φ := cofactorTest χ.val F
  let f₀ := smallerSection p f
  let c : ℂ := (addedCharacter l q).character (determinant k'.val)
  change godementSection ν (addedCharacter l p) Φ f₀ k'.val = cofactorEval hA ν p q χ f (rightOn A hr k v)
  rw [cofactorEval_apply]
  have htr := right_standardSection (hA v) q k (hA (rightOn A hr k v))
  change rightTranslation ℂ G k'.val F = standardSection q (rightOn A hr k v).val at htr
  rw [← htr]
  have hint : godementSectionIntegrand (addedCharacter l p) (cofactorTest χ.val (rightTranslation ℂ G k'.val F)) f₀ 1 =
      fun h => c * godementSectionIntegrand (addedCharacter l p) (translateTest k'.val Φ) f₀ 1 h := by
    funext h
    rw [godementSectionIntegrand, cofactorTest_right_mul χ.val χ.2.2.2.2
      (addedCharacter l q) (retainedCharacters l q) F (largerSection_mem (hA v) q)]
    rw [godementSectionIntegrand, translateTest, mul_assoc, mul_assoc, mul_assoc]
  have hs := godementSection_right_mul ν (addedCharacter l p) Φ f₀ 1 k'.val
  rw [one_mul, weight_at_unitary l p q k'] at hs
  rw [hs]
  change c * godementSection ν (addedCharacter l p) (translateTest k'.val Φ) f₀ 1 =
    godementSection ν (addedCharacter l p) (cofactorTest χ.val (rightTranslation ℂ G k'.val F)) f₀ 1
  simp only [godementSection, hint, integral_const_mul, map_one, one_mul]

variable (m) in
/-- A fixed family of compact full-row-rank tests and smaller profiles spans the same finite
space of larger compact profiles at every radial parameter. -/
def ComplexGodementFiniteProfilesStatement : Prop :=
  ∀ (ν : Measure (Langlands.GeneralLinear m ℂ)) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
    (l : Fin (m + 1) → ℤ) (φ : Matrix.unitaryGroup (Fin (m + 1)) ℂ → ℂ), IsCompactProfile l φ →
    ∃ A : Submodule ℂ (Matrix.unitaryGroup (Fin (m + 1)) ℂ → ℂ),
      FiniteDimensional ℂ A ∧ φ ∈ A ∧ (∀ v : A, IsCompactProfile l v.val) ∧
      ∃ (J : Type) (Φ : J → 𝓢(Matrix (Fin m) (Fin (m + 1)) ℂ, ℂ))
        (f : J → SmallerProfile l),
        (∀ j, HasCompactSupport (Φ j) ∧ (∀ X ∈ tsupport (Φ j), HasFullRowRank X) ∧
          FiniteDimensional ℂ (Submodule.span ℂ (range fun k : unitaryCompact ℂ (m + 1) =>
            translateTest k.val (Φ j)))) ∧
        ∀ p : Fin (m + 1) → ℂ,
          Submodule.span ℂ (range fun j => compactRestriction
            (godementSection ν (addedCharacter l p) (Φ j) (smallerSection p (f j)))) = A

set_option maxHeartbeats 900000 in
theorem complexGodementFiniteProfiles : ComplexGodementFiniteProfilesStatement m := by
  intro ν hν hright l φ hφ
  let V := twoSidedSpan φ
  have : FiniteDimensional ℂ (rightSpan φ) := hφ.2.1
  have hV : FiniteDimensional ℂ V := finiteDimensional_twoSidedSpan φ
  have hVc (v : V) : Continuous v.val := continuous_of_mem_twoSidedSpan hφ.1 v.2
  have hVr (k : U) (v : V) : rightTranslation ℂ U k v.val ∈ V := by
    change (fun x : U => v.val (x * k)) ∈ twoSidedSpan φ
    simpa only [one_mul] using translate_mem_twoSidedSpan v.2 1 k
  have hVl (k : U) (v : V) : (fun x => v.val (k * x)) ∈ V := by
    simpa only [mul_one] using translate_mem_twoSidedSpan v.2 k 1
  let A := Profiles l V
  have hAV : A ≤ V := inf_le_left
  have hAfin : FiniteDimensional ℂ A := Submodule.finiteDimensional_of_le hAV
  have hA (v : A) : IsCompactProfile l v.val := admissible hVc hVr v
  have hAr (k : U) (v : A) : rightTranslation ℂ U k v.val ∈ A :=
    ⟨hVr k ⟨v.val, v.2.1⟩, right_phase l k v.2.2⟩
  let J := P × A × Cutoff (m := m) × SmallerProfile l
  let Φ (j : J) : 𝓢(Rect, ℂ) := cofactorSchwartz j.1 j.2.2.1 (hA j.2.1)
  let f (j : J) : SmallerProfile l := j.2.2.2
  have htest (j : J) :
      HasCompactSupport (Φ j) ∧ (∀ X ∈ tsupport (Φ j), HasFullRowRank X) ∧
      FiniteDimensional ℂ (Submodule.span ℂ (range fun k : unitaryCompact ℂ (m + 1) =>
        translateTest k.val (Φ j))) := by
    rcases j with ⟨q, v, χ, f₀⟩
    let T := standardSection q v.val
    have hT := largerSection_mem (hA v) q
    obtain ⟨_, hcs, hfull⟩ := χ.2.cofactorTest_regular (addedCharacter l q) (retainedCharacters l q) hT
    exact ⟨hcs, hfull, finiteDimensional_cofactorTest_rightOrbit χ.val χ.2.2.2.2
      (addedCharacter l q) (retainedCharacters l q) T hT (standardSection_mem (hA v) q).2⟩
  refine ⟨A, hAfin, ⟨mem_twoSidedSpan φ, mem_phaseSpace hφ⟩, hA, J, Φ, f, htest, fun p => ?_⟩
  let S := Submodule.span ℂ (range fun j => compactRestriction
    (godementSection ν (addedCharacter l p) (Φ j) (smallerSection p (f j))))
  change S = A
  refine le_antisymm ?_ ?_
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨q, v, χ, f₀⟩, rfl⟩
    let j : J := (q, v, χ, f₀)
    let g := godementSection ν (addedCharacter l p) (Φ j) (smallerSection p f₀)
    change compactRestriction g ∈ A
    have hg : g ∈ Automorphic.complexStandardKFinite (m + 1) (characterList l p) := by
      rw [characterList_cons]
      exact complexGodementKFinite m ν (addedCharacter l p) (retainedCharacters l p) (Φ j) ((Φ j).smooth ⊤)
        (htest j).1 (htest j).2.1 (htest j).2.2 (smallerSection p f₀)
        (standardSection_mem f₀.2 (smallerExponents p)).1
    refine ⟨?_, mem_phaseSpace (compactRestriction_isCompactProfile hg)⟩
    let inc : A →ₗ[ℂ] V := Submodule.inclusion hAV
    have hinj : Function.Injective inc := fun x y h => Subtype.ext (congrArg (fun z : V => z.val) h)
    obtain ⟨π, hπ⟩ := inc.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hinj)
    let ℓ := cofactorEval hA ν p q χ f₀
    have hcoeff : coefficient A hAr v ℓ = coefficient V hVr (inc v) (ℓ.comp π) := by
      funext k
      change ℓ (rightOn A hAr k v) = ℓ (π (rightOn V hVr k (inc v)))
      have h := LinearMap.congr_fun hπ (rightOn A hAr k v)
      change π (rightOn V hVr k (inc v)) = rightOn A hAr k v at h
      rw [h]
    change compactRestriction (godementSection ν (addedCharacter l p) (cofactorTest χ.val (standardSection q v.val))
      (smallerSection p f₀)) ∈ V
    rw [compactRestriction_cofactor hA hAr, show cofactorEval hA ν p q χ f₀ = ℓ by rfl, hcoeff]
    exact coefficient_mem hVr hVl _ _
  · intro ψ hψ
    let v : A := ⟨ψ, hψ⟩
    let e : Module.Dual ℂ A := (LinearMap.proj (R := ℂ) (1 : U)).comp A.subtype
    let B := Submodule.span ℂ (range fun j : Cutoff (m := m) × SmallerProfile l =>
      cofactorEval hA ν p p j.1 j.2)
    have he : e ∈ B := by
      rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := B), Submodule.mem_dualAnnihilator]
      intro w hw
      by_contra hne
      let es : Fin m → Langlands.LocalFactor.Archimedean.ComplexCharacterData :=
        fun i => characterOfParams ((smallerWeights l) i) ((smallerExponents p) i)
      let F := standardSection p w.val
      have hF : F ∈ Automorphic.complexStandardKFinite (m + 1) (addedCharacter l p :: List.ofFn es) := by
        rw [← show retainedCharacters l p = List.ofFn es by rfl, ← characterList_cons]
        exact standardSection_mem (hA w) p
      have hFone : F 1 ≠ 0 := by
        change w.val 1 ≠ 0 at hne
        change standardSection p w.val 1 ≠ 0
        rw [← show Unitary.toUnits (1 : U) = 1 from map_one _, standardSection_unitary]
        exact hne
      obtain ⟨χ, f₀, hχ, hf₀, hpos⟩ := complexGodementCompactSeparation ν (addedCharacter l p) es F hF hFone
      have hf₀' : f₀ ∈ Automorphic.complexStandardKFinite m
          (characterList (smallerWeights l) (smallerExponents p)) := hf₀
      let f' : SmallerProfile l := ⟨compactRestriction f₀, compactRestriction_isCompactProfile hf₀'⟩
      let χ' : Cutoff (m := m) := ⟨χ, hχ⟩
      have hE : smallerSection p f' = f₀ := standardSection_compactRestriction hf₀'
      have hzero := (Submodule.mem_dualCoannihilator w).mp hw (cofactorEval hA ν p p χ' f')
        (Submodule.subset_span ⟨(χ', f'), rfl⟩)
      rw [cofactorEval_apply, hE] at hzero
      change godementSection ν (addedCharacter l p) (cofactorTest χ F) f₀ 1 = 0 at hzero
      rw [hzero, Complex.zero_re] at hpos
      exact lt_irrefl _ hpos
    have hB : B ≤ S.comap (coefficient A hAr v) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨χ, f₀⟩, rfl⟩
      change coefficient A hAr v (cofactorEval hA ν p p χ f₀) ∈ S
      rw [← compactRestriction_cofactor hA hAr]
      exact Submodule.subset_span ⟨(p, v, χ, f₀), rfl⟩
    have hEval : coefficient A hAr v e = ψ := by
      funext k
      change ψ (1 * k) = ψ k
      rw [one_mul]
    have hv := hB he
    change coefficient A hAr v e ∈ S at hv
    rwa [hEval] at hv

end Langlands.Global.RankinSelbergGlobal.ComplexGodement
