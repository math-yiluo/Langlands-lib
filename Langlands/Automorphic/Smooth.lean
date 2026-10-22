import Langlands.Automorphic.Ambient
import Langlands.Global.ArchimedeanGL
import Langlands.Representation.Smooth.SmoothPart.Definitions
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Smooth adelic rational functions

Slice-wise smoothness follows Borel--Jacquet section 4.1. A common open finite
stabilizer is a separate, stronger condition, not part of that definition.
-/

noncomputable section

universe u

namespace Langlands.Global.AdelicGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

theorem pair_mul (a c : InfiniteAdelicGL K n) (b d : FiniteAdelicGL K n) :
    pair K n a b * pair K n c d = pair K n (a * c) (b * d) := by
  apply (split K n).injective
  change (infinite K n _, finite K n _) = (infinite K n _, finite K n _)
  simp only [map_mul, infinite_pair, finite_pair]

theorem pair_mul_right (a : InfiniteAdelicGL K n) (b : FiniteAdelicGL K n)
    (g : AdelicGL K n) :
    pair K n a b * g = pair K n (a * infinite K n g) (b * finite K n g) := by
  conv_lhs => rw [← pair_projections K n g]
  exact pair_mul K n _ _ _ _

@[simp]
theorem ofFinite_eq_pair (b : FiniteAdelicGL K n) :
    ofFinite K n b = pair K n 1 b := rfl

@[simp]
theorem ofInfinite_eq_pair (a : InfiniteAdelicGL K n) :
    ofInfinite K n a = pair K n a 1 := rfl

theorem finite_conjugation (g : AdelicGL K n) (b : FiniteAdelicGL K n) :
    g⁻¹ * ofFinite K n b * g =
      ofFinite K n ((finite K n g)⁻¹ * b * finite K n g) := by
  apply (split K n).injective
  change (infinite K n _, finite K n _) = (infinite K n _, finite K n _)
  simp only [map_mul, map_inv, ofFinite_eq_pair, infinite_pair, finite_pair,
    mul_one, inv_mul_cancel, inv_one]

end Langlands.Global.AdelicGL

namespace Langlands.Automorphic

open Langlands.Global NumberField ContinuousRationalFunctions

set_option backward.isDefEq.respectTransparency false

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Restriction to the infinite factor at a fixed finite adelic matrix. -/
def infiniteSlice (b : FiniteAdelicGL K n) :
    ContinuousRationalFunctions K n →ₗ[ℂ] (InfiniteAdelicGL K n → ℂ) where
  toFun f a := evaluate K n f (AdelicGL.pair K n a b)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The real-smooth infinite slices form a subrepresentation of actual right translation. -/
def infiniteSmoothSubrepresentation : Subrepresentation (continuousRightAction K n) where
  toSubmodule := ⨅ b : FiniteAdelicGL K n,
    (ArchimedeanGL.smoothFunctions K n).comap (infiniteSlice K n b)
  apply_mem_toSubmodule g f hf := by
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hf ⊢
    intro b
    let s : ArchimedeanGL.SmoothFunctions K n :=
      ⟨infiniteSlice K n (b * AdelicGL.finite K n g) f, hf _⟩
    have h := (ArchimedeanGL.smoothRightAction K n (AdelicGL.infinite K n g) s).property
    change (fun a => evaluate K n f (AdelicGL.pair K n
      (a * AdelicGL.infinite K n g) (b * AdelicGL.finite K n g))) ∈
      ArchimedeanGL.smoothFunctions K n at h
    change (fun a => evaluate K n f (AdelicGL.pair K n a b * g)) ∈
      ArchimedeanGL.smoothFunctions K n
    simpa only [AdelicGL.pair_mul_right] using h

/-- Local constancy in each finite slice, without a uniform finite stabilizer. -/
def finiteLocallyConstantSubrepresentation :
    Subrepresentation (continuousRightAction K n) where
  toSubmodule :=
    { carrier := {f | ∀ a : InfiniteAdelicGL K n,
        IsLocallyConstant (fun b => evaluate K n f (AdelicGL.pair K n a b))}
      zero_mem' := fun _ => IsLocallyConstant.const 0
      add_mem' hf hg a := (hf a).add (hg a)
      smul_mem' c f hf a := (hf a).comp (fun z => c * z) }
  apply_mem_toSubmodule g f hf := by
    intro a
    have h := (hf (a * AdelicGL.infinite K n g)).comp_continuous
      (show Continuous (fun b : FiniteAdelicGL K n => b * AdelicGL.finite K n g)
        from continuous_id.mul continuous_const)
    simpa only [Function.comp_def, evaluate_rightAction, AdelicGL.pair_mul_right] using h

/-- Actual continuous, rational-invariant, slice-wise smooth adelic functions. -/
def smoothSubrepresentation : Subrepresentation (continuousRightAction K n) :=
  infiniteSmoothSubrepresentation K n ⊓ finiteLocallyConstantSubrepresentation K n

abbrev SmoothRationalFunctions := (smoothSubrepresentation K n).toSubmodule

/-- Right translation on the smooth ambient space; no automorphic finiteness is imposed. -/
def smoothRightAction :
    Representation ℂ (AdelicGL K n) (SmoothRationalFunctions K n) :=
  (smoothSubrepresentation K n).toRepresentation

/-- The smooth functions remain faithfully realized in the continuous ambient space. -/
def smoothInclusion :
    (smoothRightAction K n).IntertwiningMap (continuousRightAction K n) where
  toLinearMap := (smoothSubrepresentation K n).toSubmodule.subtype
  isIntertwining' _ := by ext; rfl

@[simp]
theorem evaluate_smoothRightAction (g x : AdelicGL K n) (f : SmoothRationalFunctions K n) :
    evaluate K n (smoothRightAction K n g f).val x = evaluate K n f.val (x * g) := rfl

/-- The finite adelic right action on the continuous ambient space. -/
def finiteRightAction :
    Representation ℂ (FiniteAdelicGL K n) (ContinuousRationalFunctions K n) :=
  (continuousRightAction K n).comp (AdelicGL.ofFinite K n).toMonoidHom

/-- Vectors with a common open finite stabilizer, stable under the full adelic action. -/
def finiteSmoothSubrepresentation : Subrepresentation (continuousRightAction K n) where
  toSubmodule := Langlands.smoothVectors (R := ℂ) (G := FiniteAdelicGL K n)
    (V := ContinuousRationalFunctions K n) (finiteRightAction K n)
  apply_mem_toSubmodule g f hf := by
    obtain ⟨L, hL⟩ := hf
    let cg : FiniteAdelicGL K n →* FiniteAdelicGL K n :=
      (MulAut.conj (AdelicGL.finite K n g)⁻¹).toMonoidHom
    have hcg : Continuous cg := IsTopologicalGroup.continuous_conj _
    refine ⟨L.comap cg hcg, ?_⟩
    intro l
    apply ((continuousRightAction K n).inv_apply_eq_iff (g := g)).mp
    have hl := hL ⟨cg l.val, l.property⟩
    change continuousRightAction K n (AdelicGL.ofFinite K n (cg l.val)) f = f at hl
    change continuousRightAction K n g⁻¹
      (continuousRightAction K n (AdelicGL.ofFinite K n l.val)
        (continuousRightAction K n g f)) = f
    change continuousRightAction K n (AdelicGL.ofFinite K n
      ((AdelicGL.finite K n g)⁻¹ * l.val * ((AdelicGL.finite K n g)⁻¹)⁻¹)) f = f at hl
    rw [inv_inv] at hl
    have hfull : continuousRightAction K n
        (g⁻¹ * AdelicGL.ofFinite K n l.val * g) f = f := by
      rw [AdelicGL.finite_conjugation]
      exact hl
    simpa only [map_mul, Module.End.mul_apply] using hfull

/-- An open finite stabilizer gives local constancy of each finite slice. -/
theorem finiteSmooth_le_finiteLocallyConstant :
    finiteSmoothSubrepresentation K n ≤ finiteLocallyConstantSubrepresentation K n := by
  intro f hf a
  obtain ⟨L, hL⟩ := hf
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro b
  refine ⟨(fun d : FiniteAdelicGL K n => b⁻¹ * d) ⁻¹' (L : Set _),
    L.isOpen.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · change b⁻¹ * b ∈ L
    simp
  · intro d hd
    have h := congrArg (fun f => evaluate K n f (AdelicGL.pair K n a b))
      (hL ⟨b⁻¹ * d, hd⟩)
    change evaluate K n f (AdelicGL.pair K n a b * AdelicGL.ofFinite K n (b⁻¹ * d)) =
      evaluate K n f (AdelicGL.pair K n a b) at h
    simpa only [AdelicGL.ofFinite_eq_pair, AdelicGL.pair_mul, mul_one,
      mul_inv_cancel_left] using h

/-- Real-smooth functions having a common open finite stabilizer. -/
def finiteSmoothRationalSubrepresentation :
    Subrepresentation (continuousRightAction K n) :=
  infiniteSmoothSubrepresentation K n ⊓ finiteSmoothSubrepresentation K n

abbrev FiniteSmoothRationalFunctions :=
  (finiteSmoothRationalSubrepresentation K n).toSubmodule

theorem finiteSmoothRational_le_smooth :
    finiteSmoothRationalSubrepresentation K n ≤ smoothSubrepresentation K n :=
  inf_le_inf_left _ (finiteSmooth_le_finiteLocallyConstant K n)

def finiteSmoothRightAction :
    Representation ℂ (AdelicGL K n) (FiniteSmoothRationalFunctions K n) :=
  (finiteSmoothRationalSubrepresentation K n).toRepresentation

/-- The stronger common-stabilizer space includes equivariantly in the smooth space. -/
def finiteSmoothInclusion :
    (finiteSmoothRightAction K n).IntertwiningMap (smoothRightAction K n) where
  toLinearMap :=
    (finiteSmoothRationalSubrepresentation K n).toSubmodule.inclusion
      (finiteSmoothRational_le_smooth K n)
  isIntertwining' _ := by ext; rfl

/-- Compact finite level implies the separate open-stabilizer condition. -/
theorem hasFiniteLevel_mem_finiteSmooth (f : ContinuousRationalFunctions K n)
    (hf : HasFiniteLevel K n f) : f ∈ finiteSmoothSubrepresentation K n := by
  obtain ⟨L, ho, _, hf⟩ := hf
  exact ⟨⟨L, ho⟩, hf⟩

/-- Given an actual compact open subgroup, an open stabilizer can be shrunk to
compact finite level. Existence of that subgroup is not hidden in this lemma. -/
theorem finiteSmooth_hasFiniteLevel
    (C : OpenSubgroup (FiniteAdelicGL K n))
    (hC : IsCompact (C : Set (FiniteAdelicGL K n)))
    (f : ContinuousRationalFunctions K n) (hf : f ∈ finiteSmoothSubrepresentation K n) :
    HasFiniteLevel K n f := by
  obtain ⟨L, hL⟩ := hf
  refine ⟨(C ⊓ L).toSubgroup, (C ⊓ L).isOpen, ?_, ?_⟩
  · exact hC.inter_right L.isClosed
  · intro l
    exact hL ⟨l.val, l.property.2⟩

/-- Smooth rational functions with the specified actual idele-class character. -/
def smoothCentralCharacterSubrepresentation
    (χ : IdeleClassGroup (𝓞 K) K →ₜ* ℂˣ) :
    Subrepresentation (continuousRightAction K n) :=
  smoothSubrepresentation K n ⊓ centralCharacterSubrepresentation K n χ

end Langlands.Automorphic
