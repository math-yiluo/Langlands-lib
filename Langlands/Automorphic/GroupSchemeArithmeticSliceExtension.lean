import Langlands.Automorphic.GroupSchemeDifferential
import Langlands.Automorphic.GroupSchemeFiniteLevelSlices

/-! # Extension from one arithmetic slice of the finite adelic quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global AdelicGroupPoints InfiniteAdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  (L : OpenSubgroup (FiniteAdelicGroupPoints F G)) (b : FiniteAdelicGroupPoints F G)

private abbrev rationalInfiniteProjection : RationalGroupPoints F G →*
    InfiniteAdelicGroupPoints F G :=
  (infinite F G).toMonoidHom.comp (rational F G)

private abbrev rationalFiniteProjection : RationalGroupPoints F G →*
    FiniteAdelicGroupPoints F G :=
  (finite F G).toMonoidHom.comp (rational F G)

local notation "r∞" => rationalInfiniteProjection F G
local notation "rf" => rationalFiniteProjection F G

/-- Plot-smooth functions fixed on the left by the arithmetic subgroup of the slice at `b`. -/
def arithmeticSliceFunctions : Submodule ℂ (InfinitePlotSmoothFunctions F G) :=
  ⨅ q : {q : RationalGroupPoints F G // b⁻¹ * rf q * b ∈ L.toSubgroup},
    LinearMap.ker (plotSmoothLeftTranslation F G (r∞ q.val) - LinearMap.id)

theorem mem_arithmeticSliceFunctions (f : InfinitePlotSmoothFunctions F G) :
    f ∈ arithmeticSliceFunctions F G L b ↔
      ∀ q : RationalGroupPoints F G, b⁻¹ * rf q * b ∈ L.toSubgroup →
        ∀ x, f.val (r∞ q * x) = f.val x := by
  simp only [arithmeticSliceFunctions, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  constructor
  · intro h q hq x
    exact congrArg (fun g : InfinitePlotSmoothFunctions F G => g.val x) (h ⟨q, hq⟩)
  · intro h q
    apply Subtype.ext
    funext x
    exact h q.val q.property x

private def sliceRep (c : FiniteAdelicGroupPoints F G) (q : RationalGroupPoints F G) : Prop :=
  (rf q * b)⁻¹ * c ∈ L.toSubgroup

private theorem sliceRep_right (c : FiniteAdelicGroupPoints F G)
    (q : RationalGroupPoints F G) (l : L) :
    sliceRep F G L b (c * l.val) q ↔ sliceRep F G L b c q := by
  simp only [sliceRep, ← mul_assoc]
  constructor
  · intro h
    simpa only [mul_assoc, mul_inv_cancel, mul_one] using L.mul_mem h (L.inv_mem l.property)
  · exact fun h => L.mul_mem h l.property

private theorem sliceRep_left (c : FiniteAdelicGroupPoints F G)
    (q gamma : RationalGroupPoints F G) :
    sliceRep F G L b (rf gamma * c) (gamma * q) ↔ sliceRep F G L b c q := by
  unfold sliceRep
  rw [map_mul, mul_assoc, mul_inv_rev, mul_assoc, inv_mul_cancel_left]

private theorem same_slice_value (f : arithmeticSliceFunctions F G L b)
    {c : FiniteAdelicGroupPoints F G} {q p : RationalGroupPoints F G}
    (hq : sliceRep F G L b c q) (hp : sliceRep F G L b c p) (x : InfiniteAdelicGroupPoints F G) :
    f.val.val ((r∞ q)⁻¹ * x) = f.val.val ((r∞ p)⁻¹ * x) := by
  have hlevel : b⁻¹ * rf (q⁻¹ * p) * b ∈ L.toSubgroup := by
    have h := L.mul_mem hq (L.inv_mem hp)
    simp only [map_mul, map_inv]
    convert h using 1
    group
  have h := (mem_arithmeticSliceFunctions F G L b f.val).mp f.property
    (q⁻¹ * p) hlevel ((r∞ p)⁻¹ * x)
  simpa only [map_mul, map_inv, mul_assoc, mul_inv_cancel_left] using h

private def extendSlice (c : FiniteAdelicGroupPoints F G) :
    arithmeticSliceFunctions F G L b →ₗ[ℂ] InfinitePlotSmoothFunctions F G := by
  classical
  exact if h : ∃ q, sliceRep F G L b c q then
    (plotSmoothLeftTranslation F G (r∞ h.choose)⁻¹).comp (arithmeticSliceFunctions F G L b).subtype
    else 0

private theorem extendSlice_of_rep (f : arithmeticSliceFunctions F G L b)
    {c : FiniteAdelicGroupPoints F G} {q : RationalGroupPoints F G}
    (hq : sliceRep F G L b c q) :
    extendSlice F G L b c f = plotSmoothLeftTranslation F G (r∞ q)⁻¹ f.val := by
  classical
  have h : ∃ q, sliceRep F G L b c q := ⟨q, hq⟩
  unfold extendSlice
  rw [dite_eq_left h]
  apply Subtype.ext
  funext x
  exact same_slice_value F G L b f h.choose_spec hq x

private theorem extendSlice_of_no_rep (f : arithmeticSliceFunctions F G L b)
    {c : FiniteAdelicGroupPoints F G} (hc : ¬∃ q, sliceRep F G L b c q) :
    extendSlice F G L b c f = 0 := by
  classical
  simp [extendSlice, hc]

/-- Extend a smooth arithmetic function by zero off the rational orbit of the finite coset `b L`.
At `c = r_f(q) b l`, the slice is left pullback by `r_∞(q)⁻¹`. -/
def extendArithmeticPlotSmoothSlices :
    arithmeticSliceFunctions F G L b →ₗ[ℂ] FiniteLevelPlotSmoothSliceFamilies F G L :=
  (LinearMap.pi (extendSlice F G L b)).codRestrict _ fun f => by
    constructor
    · intro c l
      change extendSlice F G L b (c * l.val) f = extendSlice F G L b c f
      by_cases hc : ∃ q, sliceRep F G L b c q
      · obtain ⟨q, hq⟩ := hc
        rw [extendSlice_of_rep F G L b f ((sliceRep_right F G L b c q l).mpr hq),
          extendSlice_of_rep F G L b f hq]
      · have hcl : ¬∃ q, sliceRep F G L b (c * l.val) q :=
          fun ⟨q, hq⟩ => hc ⟨q, (sliceRep_right F G L b c q l).mp hq⟩
        rw [extendSlice_of_no_rep F G L b f hcl, extendSlice_of_no_rep F G L b f hc]
    · intro gamma c x
      change (extendSlice F G L b (rf gamma * c) f).val (r∞ gamma * x) =
        (extendSlice F G L b c f).val x
      by_cases hc : ∃ q, sliceRep F G L b c q
      · obtain ⟨q, hq⟩ := hc
        rw [extendSlice_of_rep F G L b f ((sliceRep_left F G L b c q gamma).mpr hq),
          extendSlice_of_rep F G L b f hq, plotSmoothLeftTranslation_apply,
          plotSmoothLeftTranslation_apply, map_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
      · have hgc : ¬∃ p, sliceRep F G L b (rf gamma * c) p := by
          rintro ⟨p, hp⟩
          apply hc
          refine ⟨gamma⁻¹ * p, (sliceRep_left F G L b c (gamma⁻¹ * p) gamma).mp ?_⟩
          simpa only [mul_inv_cancel_left] using hp
        rw [extendSlice_of_no_rep F G L b f hgc, extendSlice_of_no_rep F G L b f hc]
        rfl

/-- Realize the extension as an actual finite-level smooth function on the rational quotient. -/
def extendArithmeticPlotSmooth {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
    arithmeticSliceFunctions F G L b →ₗ[ℂ] FinitePlotSmoothRationalFunctions F G :=
  (reconstructFinitePlotSmoothSlices F G hsmooth L).comp (extendArithmeticPlotSmoothSlices F G L b)

/-- The extended family is the original function at the chosen representative. -/
@[simp]
theorem extendArithmeticPlotSmoothSlices_apply_base (f : arithmeticSliceFunctions F G L b) :
    (extendArithmeticPlotSmoothSlices F G L b f).val b = f.val := by
  change extendSlice F G L b b f = f.val
  have h : sliceRep F G L b b 1 := by simp only [sliceRep, map_one, one_mul, inv_mul_cancel, L.one_mem]
  rw [extendSlice_of_rep F G L b f h, map_one, inv_one]
  apply Subtype.ext
  funext x
  exact congrArg f.val.val (one_mul x)

@[simp]
theorem finitePlotSmoothSlice_extendArithmeticPlotSmooth {d : ℕ}
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (f : arithmeticSliceFunctions F G L b) :
    finitePlotSmoothSlice F G b (extendArithmeticPlotSmooth F G L b hsmooth f) = f.val := by
  rw [extendArithmeticPlotSmooth, LinearMap.comp_apply, finitePlotSmoothSlice_reconstruct,
    extendArithmeticPlotSmoothSlices_apply_base]

/-- Each slice of the extension is zero or an actual left translate of the input. -/
theorem finitePlotSmoothSlice_extendArithmeticPlotSmooth_eq_zero_or {d : ℕ}
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (f : arithmeticSliceFunctions F G L b)
    (c : FiniteAdelicGroupPoints F G) :
    finitePlotSmoothSlice F G c (extendArithmeticPlotSmooth F G L b hsmooth f) = 0 ∨
    ∃ a : InfiniteAdelicGroupPoints F G,
      finitePlotSmoothSlice F G c (extendArithmeticPlotSmooth F G L b hsmooth f) =
        plotSmoothLeftTranslation F G a f.val := by
  rw [extendArithmeticPlotSmooth, LinearMap.comp_apply, finitePlotSmoothSlice_reconstruct]
  change extendSlice F G L b c f = 0 ∨
    ∃ a, extendSlice F G L b c f = plotSmoothLeftTranslation F G a f.val
  by_cases hc : ∃ q, sliceRep F G L b c q
  · obtain ⟨q, hq⟩ := hc
    exact Or.inr ⟨(r∞ q)⁻¹, extendSlice_of_rep F G L b f hq⟩
  · exact Or.inl (extendSlice_of_no_rep F G L b f hc)

/-- The original finite open level fixes the extended function. -/
theorem evaluate_extendArithmeticPlotSmooth_mul_ofFinite {d : ℕ}
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (f : arithmeticSliceFunctions F G L b)
    (l : L) (x : AdelicGroupPoints F G) :
    evaluate F G (extendArithmeticPlotSmooth F G L b hsmooth f).val (x * ofFinite F G l.val) =
      evaluate F G (extendArithmeticPlotSmooth F G L b hsmooth f).val x := by
  let s := extendArithmeticPlotSmoothSlices F G L b f
  change evaluatePlotSmoothSlices F G s.val (x * ofFinite F G l.val) =
    evaluatePlotSmoothSlices F G s.val x
  simp only [evaluatePlotSmoothSlices, map_mul, finite_ofFinite, infinite_ofFinite, mul_one]
  rw [s.property.1 _ l]

/-- Restricting an extended function to the same slice recovers its input. -/
theorem extendArithmeticPlotSmooth_injective {d : ℕ}
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
    Function.Injective (extendArithmeticPlotSmooth F G L b hsmooth) := by
  intro f g h
  apply Subtype.ext
  simpa only [finitePlotSmoothSlice_extendArithmeticPlotSmooth] using
    congrArg (finitePlotSmoothSlice F G b) h

end Langlands.Automorphic.GroupSchemeFunctions
