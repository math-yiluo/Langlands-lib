import Langlands.Global.RankinSelberg.ComplexGodementCompactSeparation
import Langlands.Global.RankinSelberg.ComplexGodementKFinite
import Langlands.Representation.Archimedean.ComplexPrincipalSeriesExtension
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Compact Schwartz Godement sections span the complex standard module -/

noncomputable section

open MeasureTheory Matrix Set
open scoped ContDiff Manifold Matrix.Norms.Operator SchwartzMap

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodement

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.Archimedean.ComplexMaximalParabolicIntegration (normSqC normSqC_det_unitary)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}
local notation "H" => Langlands.GeneralLinear n ℂ
local notation "G" => Langlands.GeneralLinear (n + 1) ℂ
local notation "K" => unitaryCompact ℂ (n + 1)
local notation "Rect" => Matrix (Fin n) (Fin (n + 1)) ℂ
local notation "Larger" => fun (d : ComplexCharacterData) (ds : List ComplexCharacterData) =>
  kFiniteFunctions (complexStandardModule (n + 1) (d :: ds)) K
local notation "Smaller" => fun (ds : List ComplexCharacterData) =>
  kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)

local instance compactSpanningGLMeasure (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℂ) := borel _
local instance compactSpanningGLBorel (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℂ) := ⟨rfl⟩

/-- The Godement sections whose input on the smaller factor is a compact-finite standard vector
and whose rectangular test is compact-finite and smoothly supported in the full-row-rank locus. -/
def compactGodementSections (ν : Measure H) (d : ComplexCharacterData) (ds : List ComplexCharacterData) :
    Set (G → ℂ) :=
  {F | ∃ (Φ : 𝓢(Rect, ℂ)) (f₀ : Smaller ds), HasCompactSupport Φ ∧
    (∀ X ∈ tsupport Φ, HasFullRowRank X) ∧
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => translateTest k.val Φ)) ∧
    F = godementSection ν d Φ f₀.val}

private theorem compactGodementSections_subset (ν : Measure H) [IsLocallyFiniteMeasure ν]
    [ν.IsMulRightInvariant] (d : ComplexCharacterData) (ds : List ComplexCharacterData) :
    compactGodementSections ν d ds ⊆ Larger d ds := by
  rintro F ⟨Φ, f₀, hΦc, hfull, hfin, rfl⟩
  exact complexGodementKFinite n ν d ds Φ (Φ.smooth ⊤) hΦc hfull hfin f₀.val f₀.2.1

private def cofactorTestLinear (d : ComplexCharacterData) (ds : List ComplexCharacterData)
    (χ : 𝓢(Rect, ℂ)) (hχ : IsGodementCofactorCutoff χ) : Larger d ds →ₗ[ℂ] godementTests n :=
  ((cofactorTest χ).comp (Larger d ds).subtype).codRestrict (godementTests n) fun f => by
    obtain ⟨hc, hcs, hf⟩ := hχ.cofactorTest_regular d ds f.2.1
    exact ⟨hc.continuous, hcs, hf⟩

private def cofactorSectionLinear (ν : Measure H) [IsLocallyFiniteMeasure ν]
    (d : ComplexCharacterData) (ds : List ComplexCharacterData) (χ : 𝓢(Rect, ℂ))
    (hχ : IsGodementCofactorCutoff χ) (f₀ : Smaller ds) : Larger d ds →ₗ[ℂ] (G → ℂ) :=
  (godementSectionLinear ν d f₀.2.1.1.continuous).comp (cofactorTestLinear d ds χ hχ)

private theorem cofactorSection_mem (ν : Measure H) (d : ComplexCharacterData) (ds : List ComplexCharacterData)
    (χ : 𝓢(Rect, ℂ)) (hχ : IsGodementCofactorCutoff χ) (f₀ : Smaller ds) (f : Larger d ds) :
    godementSection ν d (cofactorTest χ f.val) f₀.val ∈ compactGodementSections ν d ds := by
  obtain ⟨Φ, hΦ, hc, hfull, _⟩ := complexGodementCofactorTest χ hχ.1 hχ.2.1 hχ.2.2.2 d ds f.val f.2.1
  refine ⟨Φ, f₀, hc, hfull, ?_, ?_⟩
  · rw [hΦ]
    exact finiteDimensional_cofactorTest_rightOrbit χ hχ.2.2.2 d ds f.val f.2.1 f.2.2
  · rw [hΦ]

private theorem cofactorSection_translate_at_one (ν : Measure H) (d : ComplexCharacterData)
    (ds : List ComplexCharacterData) (χ : 𝓢(Rect, ℂ)) (hχ : IsGodementCofactorCutoff χ)
    (f₀ : H → ℂ) {f : G → ℂ} (hf : f ∈ complexStandardModule (n + 1) (d :: ds)) (k : K) :
    godementSection ν d (cofactorTest χ (Whittaker.rightTranslation ℂ G k.val f)) f₀ 1 =
      godementSection ν d (cofactorTest χ f) f₀ k.val := by
  let c : ℂ := d.character (determinant k.val)
  have hw : characterWeight d ((n : ℂ) / 2) (determinant k.val) = c := by
    change c * (normSqC (determinant k.val : ℂ)) ^ ((n : ℂ) / 2) = c
    have hN : normSqC (determinant k.val : ℂ) = 1 := normSqC_det_unitary k
    rw [hN, Complex.one_cpow, mul_one]
  have hi : godementSectionIntegrand d (cofactorTest χ (Whittaker.rightTranslation ℂ G k.val f)) f₀ 1 =
      fun h => c * godementSectionIntegrand d (translateTest k.val (cofactorTest χ f)) f₀ 1 h := by
    funext h
    rw [godementSectionIntegrand, cofactorTest_right_mul χ hχ.2.2.2 d ds f hf]
    rw [godementSectionIntegrand, translateTest, mul_assoc, mul_assoc, mul_assoc]
  have hs := godementSection_right_mul ν d (cofactorTest χ f) f₀ 1 k.val
  rw [one_mul, hw] at hs
  rw [hs]
  simp only [godementSection, hi, integral_const_mul, map_one, one_mul]

private def restrictUnitary : (G → ℂ) →ₗ[ℂ] (K → ℂ) :=
  LinearMap.pi (fun k : K => LinearMap.proj (R := ℂ) k.val)

/-- The compact Schwartz Godement sections span the compact-finite part of the upper-Borel
standard module obtained by prepending the distinguished character. -/
def ComplexGodementCompactSpanningStatement : Prop :=
  ∀ (ν : Measure H) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
    (d : ComplexCharacterData) (es : Fin n → ComplexCharacterData),
    Submodule.span ℂ (compactGodementSections ν d (List.ofFn es)) = Larger d (List.ofFn es)

theorem complexGodementCompactSpanning : ComplexGodementCompactSpanningStatement (n := n) := by
  intro ν hν hνr d es
  let ds := List.ofFn es
  let S := Submodule.span ℂ (compactGodementSections ν d ds)
  have hS : S ≤ Larger d ds := Submodule.span_le.mpr (compactGodementSections_subset ν d ds)
  refine le_antisymm hS ?_
  intro f hf
  let V := Submodule.span ℂ (Set.range fun k : K => Whittaker.rightTranslation ℂ G k.val f)
  let : FiniteDimensional ℂ V := (mem_kFiniteVectors_iff _ _ _).mp hf.2
  have hV : V ≤ Larger d ds := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact rightTranslation_mem_kFiniteFunctions_principalSeries (complexPositionCharacter (d :: ds)) K hf k.2
  let e : (G → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj (R := ℂ) (1 : G)
  let e₁ : Module.Dual ℂ V := e.comp V.subtype
  let J := {χ : 𝓢(Rect, ℂ) // IsGodementCofactorCutoff χ} × Smaller ds
  let P (j : J) : Larger d ds →ₗ[ℂ] (G → ℂ) := cofactorSectionLinear ν d ds j.1.val j.1.2 j.2
  let evalSection (j : J) : Module.Dual ℂ V := e.comp ((P j).comp (Submodule.inclusion hV))
  let A := Submodule.span ℂ (Set.range evalSection)
  have he₁ : e₁ ∈ A := by
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := A), Submodule.mem_dualAnnihilator]
    intro v hv
    by_contra hn
    have hv1 : v.val 1 ≠ 0 := hn
    obtain ⟨χ, f₀, hχ, hf₀, hpos⟩ := complexGodementCompactSeparation ν d es v.val (hV v.2) hv1
    let j : J := (⟨χ, hχ⟩, ⟨f₀, hf₀⟩)
    have hzero := (Submodule.mem_dualCoannihilator v).mp hv (evalSection j)
      (Submodule.subset_span (Set.mem_range_self j))
    change godementSection ν d (cofactorTest χ v.val) f₀ 1 = 0 at hzero
    rw [hzero, Complex.zero_re] at hpos
    exact lt_irrefl _ hpos
  let vf (k : K) : V := ⟨Whittaker.rightTranslation ℂ G k.val f, Submodule.subset_span (Set.mem_range_self k)⟩
  let T : Module.Dual ℂ V →ₗ[ℂ] (K → ℂ) := LinearMap.pi (fun k => Module.Dual.eval ℂ V (vf k))
  let R := restrictUnitary (n := n)
  have hTe : T e₁ = R f := by
    funext k
    change f (1 * k.val) = f k.val
    rw [one_mul]
  have hTA : A ≤ (S.map R).comap T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    refine ⟨P j ⟨f, hf⟩, ?_, ?_⟩
    · apply Submodule.subset_span
      exact cofactorSection_mem ν d ds j.1.val j.1.2 j.2 ⟨f, hf⟩
    · funext k
      change godementSection ν d (cofactorTest j.1.val f) j.2.val k.val =
        godementSection ν d (cofactorTest j.1.val (Whittaker.rightTranslation ℂ G k.val f)) j.2.val 1
      exact (cofactorSection_translate_at_one ν d ds j.1.val j.1.2 j.2.val hf.1 k).symm
  have hRf : R f ∈ S.map R := hTe ▸ hTA he₁
  obtain ⟨F, hFS, hFR⟩ := hRf
  have hef : F = f := ComplexPrincipalSeriesExtension.eq_of_eqOn_unitary (hS hFS).1 hf.1
    (fun k hk => congrFun hFR (⟨k, hk⟩ : K))
  exact hef ▸ hFS

end Langlands.Global.RankinSelbergGlobal.ComplexGodement
