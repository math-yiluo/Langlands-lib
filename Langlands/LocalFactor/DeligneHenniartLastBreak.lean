import Langlands.LocalFactor.CommonClosureIrreducibleReduction
import Langlands.LocalFactor.DeligneHenniartRefinedBrauer
import Langlands.LocalFactor.DeligneHenniartRelativeWitness
import Langlands.LocalFactor.DeligneHenniartExactCoset
import Langlands.LocalFactor.Ramification.Herbrand.LastGroupProof
import Langlands.LocalFactor.Ramification.Herbrand.WeilInertiaProof

/-!
# The last upper group of an irreducible wild representation

Deligne--Henniart 1981, 4.5: for an irreducible continuous representation `A` of `W_F`
with last break `α > 0`, the upper group `W^α` acts through commuting operators without
nonzero fixed vectors, and `W^s` acts trivially for `s > α`. Brauer induction relative to
this group (2.3, in the form of `weilAbelianNormalBrauer_kernel`) then writes the class of
`A`, restricted to the base Weil subgroup, as a combination of inductions of characters
that are nontrivial on `W^α` and trivial on every `W^s` with `s > α`.
-/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.NonabelianSystem.DeligneHenniart

open CommonClosure VirtualRepresentation Weil.Local
open VirtualRepresentation.LocalWeil.Ramification Ramification.HerbrandBridge Ramification.Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

section LastBreak

variable (A : FiniteRepresentation.{0, uF, max uF uV} ℂ (localWeilGroup F))

/-- An element whose projection lies in the closed right limit `G^{a+}` acts trivially,
when every upper group of index above `a ≥ 0` acts trivially. -/
theorem representation_eq_one_of_mem_rightLimit (hA : A.IsContinuous) {a : ℝ} (ha : 0 ≤ a)
    (htriv : ∀ s, a < s → IsTrivialAt F A s) {c : localWeilGroup F}
    (hc : localProjection F c ∈ absoluteUpperRightLimit F a) :
    A.representation c = 1 := by
  set e := localInertiaEquiv F
  have hker : IsOpen (A.representation.ker : Set (localWeilGroup F)) :=
    ((localWeilContinuity.{uF, max uF uV} F A).2.2.2.1).mp hA
  let K₀ : Subgroup (localInertia F) := A.representation.ker.comap (localInertia F).subtype
  have hK₀ : IsOpen (K₀ : Set (localInertia F)) := hker.preimage continuous_subtype_val
  let H₀ : Subgroup (F.absoluteInertia F.canonicalTopologicalData) :=
    K₀.comap e.symm.toMulEquiv.toMonoidHom
  have hH₀ : IsOpen (H₀ : Set (F.absoluteInertia F.canonicalTopologicalData)) :=
    hK₀.preimage e.symm.continuous
  let H : Subgroup (Field.absoluteGaloisGroup F.Carrier) :=
    H₀.map (F.absoluteInertia F.canonicalTopologicalData).subtype
  have hH : IsClosed (H : Set (Field.absoluteGaloisGroup F.Carrier)) := by
    change IsClosed (((↑) : F.absoluteInertia F.canonicalTopologicalData →
      Field.absoluteGaloisGroup F.Carrier) '' (H₀ : Set _))
    exact (H₀.isClosed_of_isOpen hH₀).trans (F.absoluteInertia_isClosed _)
  have hle : (⨆ (w : ℝ) (_ : a < w), absoluteUpperRamificationGroup F w) ≤ H := by
    refine iSup₂_le fun w hw σ hσ => ?_
    have hσ0 : σ ∈ F.absoluteInertia F.canonicalTopologicalData := by
      rw [← absoluteUpperCanonicalInertia F]
      exact absoluteUpperRamificationGroup_antitone F (ha.trans hw.le) hσ
    refine ⟨⟨σ, hσ0⟩, ?_, rfl⟩
    change A.representation ((e.symm ⟨σ, hσ0⟩ : localInertia F) : localWeilGroup F) = 1
    apply htriv w hw
    change localProjection F _ ∈ absoluteUpperRamificationGroup F w
    rw [← localInertiaEquiv_apply, ContinuousMulEquiv.apply_symm_apply]
    exact hσ
  have hcH : localProjection F c ∈ H :=
    Subgroup.topologicalClosure_minimal _ hle hH hc
  obtain ⟨σ, hσ, hσc⟩ := Subgroup.mem_map.mp hcH
  have hσ' : A.representation ((e.symm σ : localInertia F) : localWeilGroup F) = 1 := hσ
  have heq : ((e.symm σ : localInertia F) : localWeilGroup F) = c := by
    apply localProjection_injective F
    rw [← localInertiaEquiv_apply, ContinuousMulEquiv.apply_symm_apply]
    exact hσc
  rw [← heq]
  exact hσ'

/-- Above the last break every upper group acts trivially. -/
theorem isTrivialAt_of_lastBreak_lt (hA : A.IsContinuous) (hα : 0 < lastBreak F A) {s : ℝ}
    (hs : lastBreak F A < s) : IsTrivialAt F A s :=
  (lastBreak_lt_iff_isTrivialAt F A hA (hα.trans hs)).mp hs

/-- The last upper group acts through commuting operators (DH81 4.5, from the
commutator estimate `(W^α, W^α) ⊆ W^{α+}`). -/
theorem commute_on_lastBreak (hA : A.IsContinuous) (hα : 0 < lastBreak F A)
    {x y : localWeilGroup F} (hx : x ∈ upperGroup F (lastBreak F A))
    (hy : y ∈ upperGroup F (lastBreak F A)) :
    A.representation x * A.representation y = A.representation y * A.representation x := by
  have hc := representation_eq_one_of_mem_rightLimit F A hA hα.le
    (fun s hs => isTrivialAt_of_lastBreak_lt F A hA hα hs)
    (localProjection_commutator_mem_closedRightLimit F hα hx hy)
  have hsplit : x * y = (y * x) * ((y * x)⁻¹ * (x * y)) := by group
  rw [← map_mul, ← map_mul, hsplit, map_mul _ (y * x), hc, mul_one]

/-- An irreducible representation has no nonzero vector fixed by its last upper group. -/
theorem fixed_eq_zero_of_lastBreak (hA : A.IsContinuous) (hi : A.IsIrreducible)
    (hα : 0 < lastBreak F A) (v : A)
    (hv : ∀ w ∈ upperGroup F (lastBreak F A), A.representation w v = v) : v = 0 := by
  rcases upperFixedSpace_eq_bot_or_eq_top F A hi (lastBreak F A) with h | h
  · have hmem : v ∈ upperFixedSpace F A (lastBreak F A) := (mem_upperFixedSpace F A _ v).mpr hv
    rw [h] at hmem
    exact (Submodule.mem_bot ℂ).mp hmem
  · have := (lastBreak_lt_iff_isTrivialAt F A hA hα).mpr
      ((upperFixedSpace_eq_top_iff F A _).mp h)
    exact absurd this (lt_irrefl _)

end LastBreak

/-! ## Transport to the base Weil subgroup -/

theorem baseWeilInclusion_surjective :
    Function.Surjective (baseWeilInclusion F) := fun w =>
  ⟨⟨w, mem_baseWeil F w⟩, rfl⟩

/-- The part of the base Weil group above the index `α`: the union of the upper groups of
index `s > α`. -/
def baseUpperAbove (α : ℝ) : Subgroup (weilSubgroup F (baseExtension F)) :=
  ⨆ (s : ℝ) (_ : α < s), baseUpperGroup F s

theorem baseUpperAbove_le_inertia {α : ℝ} (hα : 0 ≤ α) :
    baseUpperAbove F α ≤ CommonClosureWeilDeligne.inertia F (baseExtension F) :=
  iSup₂_le fun _ hs => baseUpperGroup_le_inertia F (absoluteUpperInertia F _) (hα.trans hs.le)

/-- DH81 4.5, the Brauer step: a basis class of positive label `α` realizes at the base
field in the span of inductions `Ind_{W_L}^{W_F} η` with `W^α ⊆ W_L`, `η` nontrivial on
`W^α` and trivial on `W^s ∩ W_L` for every `s > α`. -/
theorem realizeAtBase_generator_mem_kernelSpan (b : LocalWeil.Basis.{uF, max uF uV} F)
    (hb : 0 < breakLabel F b) :
    realizeAtBase.{uF, uV} F (generator b) ∈
      Submodule.span ℤ (kernelInductionGenerators.{uF, uV} F (baseExtension F)
        (baseUpperGroup F (breakLabel F b)) (baseUpperAbove F (breakLabel F b))) := by
  obtain ⟨n, c, hc⟩ := b
  induction c using Quotient.inductionOn with
  | h A =>
    have hα : 0 < lastBreak F A.val := hb
    have hc' : A.val.rank = (n : ℕ) := hc
    have hgen : generator
        (⟨n, ⟨Quotient.mk _ A, hc⟩⟩ : LocalWeil.Basis.{uF, max uF uV} F) =
        LocalWeil.ofRepresentation A.val A.property.1 A.property.2 n hc' := rfl
    have hlab : breakLabel F (⟨n, ⟨Quotient.mk _ A, hc⟩⟩ : LocalWeil.Basis.{uF, max uF uV} F) =
        lastBreak F A.val := rfl
    rw [hgen, hlab]
    unfold realizeAtBase
    rw [LinearMap.comp_apply, LocalWeil.realizeExact_ofRepresentation]
    unfold ExactGrothendieckGroup.continuousRestrict
    rw [ExactGrothendieckGroup.restrict_ofRepresentation]
    set α := lastBreak F A.val
    let B := FiniteRepresentation.restrict (baseWeilInclusion F).toMonoidHom A.val
    have hBc : B.IsContinuous := FiniteRepresentation.isContinuous_restrict
      (baseWeilInclusion F).toMonoidHom (baseWeilInclusion F).continuous A.property.1
    have hBi : B.IsIrreducible := FiniteRepresentation.isIrreducible_restrict_of_surjective
      (baseWeilInclusion F).toMonoidHom (baseWeilInclusion_surjective F) A.val A.property.2
    exact weilAbelianNormalBrauer_kernel F (baseExtension F) (baseUpperGroup F α)
      (baseUpperAbove F α) (baseUpperGroup_normal F α)
      (baseUpperGroup_le_inertia F (absoluteUpperInertia F _) hα.le)
      (baseUpperAbove_le_inertia F hα.le) B hBc hBi
      (fun x hx y hy => commute_on_lastBreak F A.val A.property.1 hα hx hy)
      (fun v hv => fixed_eq_zero_of_lastBreak F A.val A.property.1 A.property.2 hα v
        (fun w hw => hv ⟨w, mem_baseWeil F w⟩ hw))
      (fun k hk => by
        refine (iSup₂_le (fun s hs g hg => ?_) : baseUpperAbove F α ≤ B.representation.ker) hk
        exact isTrivialAt_of_lastBreak_lt F A.val A.property.1 hα hs _ hg)

end Langlands.LocalFactor.NonabelianSystem.DeligneHenniart
