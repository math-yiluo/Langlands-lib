import Langlands.Global.RankinSelberg.ComplexSquareConvolutionSpan
import Langlands.Representation.Archimedean.ComplexStandardPermutationProof

/-! # Square Gaussian convolution generation for arbitrary inducing lists -/

noncomputable section

open MeasureTheory Set
open scoped Matrix.Norms.Operator SchwartzMap TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal Langlands.Archimedean Langlands.Automorphic Langlands.GeneralLinear
open Langlands.LocalFactor.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] archimedeanEquationComplexGLMeasurable archimedeanEquationComplexGLBorel

variable {r : ℕ}
local notation "n" => (r + 1 : ℕ)
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "U" => Matrix.unitaryGroup (Fin n) ℂ
local notation "X" => Matrix (Fin n) (Fin n) ℂ
local notation "KF[" ds "]" => complexStandardKFinite n ds

/-- Precomposing a Whittaker intertwiner with a standard-module intertwiner is again a
Whittaker intertwiner for the same character. -/
theorem IsComplexWhittakerIntertwiner.comp_standard {ds es : List ComplexCharacterData} {a : ℂˣ}
    {B : KF[ds] →ₗ[ℂ] (G → ℂ)} (hB : IsComplexWhittakerIntertwiner r ds a B)
    {T : KF[es] →ₗ[ℂ] KF[ds]}
    (hT : IsComplexStandardIntertwining n (complexStandardRep n ds) (complexStandardLie n ds) es T) :
    IsComplexWhittakerIntertwiner r es a (B.comp T) := by
  refine ⟨fun f => hB.1 (T f), fun f => hB.2.1 (T f), fun f => hB.2.2.1 (T f), ?_, ?_⟩
  · intro k f f' hf'
    let k₀ : U := ⟨k.val.val, k.2⟩
    have hk : Unitary.toUnits k₀ = k.val := Units.ext rfl
    have he : complexStandardRep n es k₀ f = f' := by
      apply Subtype.ext
      change Whittaker.rightTranslation ℂ G (Unitary.toUnits k₀) f = f'.val
      rw [hk, hf']
    change B (T f') = _
    rw [← he, hT.map_rep]
    apply hB.2.2.2.1 k (T f) (complexStandardRep n ds k₀ (T f))
    change Whittaker.rightTranslation ℂ G (Unitary.toUnits k₀) (T f) = _
    rw [hk]
  · intro Y f f' hf'
    have hLie (cs : List ComplexCharacterData) (v : KF[cs]) :
        (complexStandardLie n cs (1 ⊗ₜ[ℝ] Y) v).val = rightDerivative (matrixModel ℂ n) Y v := by
      rw [complexStandardLie, principalSeriesLie, kFiniteLie_one_tmul_apply_coe]
    have he : complexStandardLie n es (1 ⊗ₜ[ℝ] Y) f = f' := Subtype.ext ((hLie es f).trans hf'.symm)
    change B (T f') = _
    rw [← he, hT.map_lie]
    exact hB.2.2.2.2 Y (T f) (complexStandardLie n ds (1 ⊗ₜ[ℝ] Y) (T f)) (hLie ds (T f))

namespace ComplexJacquet

private theorem irreducible_of_standard_bijection {ds es : List ComplexCharacterData}
    (hirr : IsIrreducibleGKModule (complexStandardRep n ds) (complexStandardLie n ds))
    {T : KF[es] →ₗ[ℂ] KF[ds]} (hT₀ : Function.Bijective T)
    (hT : IsComplexStandardIntertwining n (complexStandardRep n ds) (complexStandardLie n ds) es T) :
    IsIrreducibleGKModule (complexStandardRep n es) (complexStandardLie n es) := by
  let : Nontrivial KF[ds] := hirr.1
  refine ⟨hT₀.2.nontrivial, fun W hK hL => ?_⟩
  have hW : W.map T = ⊥ ∨ W.map T = ⊤ := by
    apply hirr.2
    · intro k v hv
      rcases hv with ⟨w, hw, rfl⟩
      exact ⟨complexStandardRep n es k w, hK k w hw, hT.map_rep k w⟩
    · intro Y v hv
      rcases hv with ⟨w, hw, rfl⟩
      exact ⟨complexStandardLie n es Y w, hL Y w hw, hT.map_lie Y w⟩
  have hinj := Submodule.map_injective_of_injective hT₀.1
  have htop : (⊤ : Submodule ℂ KF[es]).map T = ⊤ := by
    rw [Submodule.map_top, LinearMap.range_eq_top.mpr hT₀.2]
  rcases hW with h | h
  · exact Or.inl (hinj (h.trans (Submodule.map_bot T).symm))
  · exact Or.inr (hinj (h.trans htop.symm))

private theorem exists_weight_order (e : Fin n → ComplexCharacterData) :
    ∃ e' : Fin n → ComplexCharacterData, (List.ofFn e').Perm (List.ofFn e) ∧
      Monotone fun j => (e' j).weight := by
  let R (x y : ComplexCharacterData) := decide (x.weight ≤ y.weight)
  let es := (List.ofFn e).mergeSort R
  have hp : es.Perm (List.ofFn e) := List.mergeSort_perm _ _
  have hn : es.length = n := hp.length_eq.trans List.length_ofFn
  have h := List.pairwise_mergeSort (le := R)
    (fun a b c hab hbc => by
      simp only [R, decide_eq_true_eq] at hab hbc ⊢
      exact hab.trans hbc)
    (fun a b => by
      simp only [R, Bool.or_eq_true, decide_eq_true_eq]
      exact le_total _ _) (List.ofFn e)
  have hm : es.Pairwise (fun x y : ComplexCharacterData => x.weight ≤ y.weight) :=
    h.imp fun ht => by simpa [R] using ht
  let e' (j : Fin n) := es.get (Fin.cast hn.symm j)
  have he' : List.ofFn e' = es := (List.ofFn_congr hn es.get).symm.trans (List.ofFn_get es)
  refine ⟨e', he'.symm ▸ hp, fun i j hij => ?_⟩
  rw [← he', List.pairwise_ofFn] at hm
  rcases lt_or_eq_of_le hij with hlt | rfl
  · exact hm hlt
  · exact le_rfl

/-- At each spectral point the normalized square Gaussian convolutions span the compact-finite
standard module for the supplied inducing list, in its given order. -/
def ComplexSquareConvolutionGenerationStatement : Prop :=
  ∀ (μ : Measure G) [μ.IsHaarMeasure] (d : ComplexCharacterData) (e : Fin n → ComplexCharacterData),
    IsIrreducibleGKModule (complexStandardRep n (List.ofFn e)) (complexStandardLie n (List.ofFn e)) →
    ∀ (a : ℂˣ) (B : KF[List.ofFn e] →ₗ[ℂ] (G → ℂ)),
      IsComplexWhittakerIntertwiner r (List.ofFn e) a B → B ≠ 0 →
      ∀ s₀ : ℂ, squareConvolutionSpan μ d e B s₀ = ⊤

set_option maxHeartbeats 900000 in
theorem complexSquareConvolutionGeneration : ComplexSquareConvolutionGenerationStatement (r := r) := by
  intro μ hμ d e hirr a B hB hB₀ s₀
  obtain ⟨e', hperm, horder⟩ := exists_weight_order e
  obtain ⟨T, hT₀, hT⟩ := complexStandardPermutation n (List.ofFn e) (List.ofFn e') List.length_ofFn hperm hirr
  have hirr' := irreducible_of_standard_bijection hirr hT₀ hT
  let B' := B.comp T
  have hB' : IsComplexWhittakerIntertwiner r (List.ofFn e') a B' := hB.comp_standard hT
  have hB'₀ : B' ≠ 0 := by
    intro hz
    apply hB₀
    refine LinearMap.ext fun v => ?_
    obtain ⟨w, rfl⟩ := hT₀.2 v
    exact LinearMap.congr_fun hz w
  have hS := complexSquareConvolutionSpan μ d e' horder hirr' a B' hB' hB'₀ s₀
  let S := squareConvolutionSpan μ d e B s₀
  let S' := squareConvolutionSpan μ d e' B' s₀
  have hm : S'.map T ≤ S := by
    apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨Φ, P, f, F, hΦ, hF, rfl⟩
    let V (s : ℂ) := T (F s)
    have hV : HasSquareConvolutionTrace μ d e B Φ (T f) V := by
      obtain ⟨l, p, v, hv⟩ := hF.1
      obtain ⟨σ, hσ⟩ := hF.2
      refine ⟨⟨l, p, T ∘ v, fun s => ?_⟩, σ, fun s hs x => ?_⟩
      · change T (F s) = _
        rw [hv s, map_sum]
        simp only [map_smul, Function.comp_apply]
      · have hL := complexPairLFactor_perm (List.Perm.refl [d]) hperm
        simpa only [B', LinearMap.comp_apply, hL, V] using hσ s hs x
    exact mem_squareConvolutionSpan hΦ hV
  change S' = ⊤ at hS
  rw [hS, Submodule.map_top, LinearMap.range_eq_top.mpr hT₀.2] at hm
  exact eq_top_iff.mpr hm

end ComplexJacquet
end Langlands.Global.RankinSelbergGlobal
