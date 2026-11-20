import Langlands.Global.AdelicBlockScalarSectionActions
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Smooth compact slices of realized scalar adelic sections

For a compact-finite vector, smooth ambient extensions of scalar evaluations give
smooth local expansions of its normalized compact slices in finitely many actual
Levi coefficients.
-/

noncomputable section

open scoped BigOperators Classical ContDiff Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1050000
set_option synthInstance.maxHeartbeats 85000

universe u uX

namespace Langlands.Global.AdelicBlockScalarSections

open Langlands.Automorphic Langlands.GeneralLinear AdelicBlockParabolic PrimitiveAdelicHeight

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
  (S : ∀ i : Fin B.length, OperatorRealization F (B.size i))

local notation "A" => ArchimedeanMatrix F n
local notation "K" => standardCompact F n
local notation "KI" => standardInfiniteCompact F n
local notation "KF" => FiniteAdelicGL.standardIntegral F n
local notation "M" => FullLevi F B

/-- Pair the actual infinite and finite compact components. -/
def compactPair (k : KI) (l : KF) : K :=
  ⟨AdelicGL.pair F n k.val l.val, (mem_standardCompact_iff F n _).mpr
    ⟨by rw [AdelicGL.infinite_pair]; exact k.property,
      by rw [AdelicGL.finite_pair]; exact l.property⟩⟩

@[simp] theorem compactPair_val (k : KI) (l : KF) :
    (compactPair F k l).val = AdelicGL.pair F n k.val l.val := rfl

private theorem compactPair_mul_infiniteCompactInclusion (k h : KI) (l : KF) :
    compactPair F k l * infiniteCompactInclusion F h = compactPair F (k * h) l := by
  apply Subtype.ext
  apply (AdelicGL.split F n).injective
  apply Prod.ext
  · change AdelicGL.infinite F n
      (AdelicGL.pair F n k.val l.val * AdelicGL.ofInfinite F n h.val) =
        AdelicGL.infinite F n (AdelicGL.pair F n (k.val * h.val) l.val)
    rw [AdelicGL.ofInfinite_eq_pair, map_mul]
    simp only [AdelicGL.infinite_pair]
  · change AdelicGL.finite F n
      (AdelicGL.pair F n k.val l.val * AdelicGL.ofInfinite F n h.val) =
        AdelicGL.finite F n (AdelicGL.pair F n (k.val * h.val) l.val)
    rw [AdelicGL.ofInfinite_eq_pair, map_mul]
    simp only [AdelicGL.finite_pair, mul_one]

/-- The ambient mixed matrix of an actual infinite compact point. -/
def compactMatrix (k : KI) : A := (archimedeanGLCoordinates F n k.val).val

/-- At every infinite compact point, the scalar evaluations of normalized compact slices
are locally restrictions of smooth functions in the ambient mixed matrix coordinates. -/
def HasSmoothCompactSlices (f : RealizedSections F B S) : Prop :=
  ∀ (k : KI) (l : KF) (m : M), ∃ φ : A → ℂ, ContDiffAt ℝ ∞ φ (compactMatrix F k) ∧
    ∀ᶠ x in 𝓝 (compactMatrix F k), ∀ h : KI, compactMatrix F h = x →
      φ x = normalizedSlice F B f.val (compactPair F h l) m

private theorem span_evaluation_eq_top {X : Type uX} (W : Submodule ℂ (X → ℂ))
    [FiniteDimensional ℂ W] :
    Submodule.span ℂ (Set.range fun x : X => (LinearMap.proj x).comp W.subtype) = ⊤ := by
  let E : Submodule ℂ (Module.Dual ℂ W) :=
    Submodule.span ℂ (Set.range fun x : X => (LinearMap.proj x).comp W.subtype)
  have : FiniteDimensional ℂ (Module.Dual ℂ W) := Subspace.instModuleDualFiniteDimensional
  have : FiniteDimensional ℂ E := FiniteDimensional.finiteDimensional_submodule E
  have hco : E.dualCoannihilator = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    rw [Submodule.mem_dualCoannihilator] at hw
    apply Subtype.ext
    funext x
    exact hw _ (Submodule.subset_span ⟨x, rfl⟩)
  have h := Subspace.dualCoannihilator_dualAnnihilator_eq (W := E)
  rw [hco, Submodule.dualAnnihilator_bot] at h
  exact h.symm

private theorem exists_smooth_dualExtension (W : Submodule ℂ (M → ℂ))
    [FiniteDimensional ℂ W] (w : KI → W) (k : KI) (f : RealizedSections F B S)
    (hf : HasSmoothCompactSlices F B S f) (l : KF)
    (hw : ∀ h : KI, (w h).val = normalizedSlice F B f.val (compactPair F h l))
    (L : Module.Dual ℂ W) :
    ∃ φ : A → ℂ, ContDiffAt ℝ ∞ φ (compactMatrix F k) ∧
      ∀ᶠ x in 𝓝 (compactMatrix F k), ∀ h : KI, compactMatrix F h = x → φ x = L (w h) := by
  have hL : L ∈ Submodule.span ℂ (Set.range fun m : M => (LinearMap.proj m).comp W.subtype) :=
    (span_evaluation_eq_top W).symm ▸ Submodule.mem_top
  induction hL using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨m, rfl⟩ := hφ
    obtain ⟨ψ, hs, he⟩ := hf k l m
    refine ⟨ψ, hs, he.mono ?_⟩
    intro x hx h hh
    change ψ x = (w h).val m
    rw [hw]
    exact hx h hh
  | zero =>
    exact ⟨0, contDiffAt_const, Filter.Eventually.of_forall fun _ _ _ => rfl⟩
  | add L J _ _ hL hJ =>
    obtain ⟨φ, hφ, hφe⟩ := hL
    obtain ⟨ψ, hψ, hψe⟩ := hJ
    refine ⟨φ + ψ, hφ.add hψ, ?_⟩
    filter_upwards [hφe, hψe] with x hx hy h hh
    exact congrArg₂ (· + ·) (hx h hh) (hy h hh)
  | smul c L _ hL =>
    obtain ⟨φ, hφ, hφe⟩ := hL
    refine ⟨c • φ, hφ.const_smul c, hφe.mono ?_⟩
    intro x hx h hh
    exact congrArg (c • ·) (hx h hh)

local instance : AddCommGroup (FiniteSmoothRealizedSections F B S) := Submodule.addCommGroup _

private def sliceMap (k : K) : FiniteSmoothRealizedSections F B S →ₗ[ℂ] (M → ℂ) :=
  (LinearMap.proj k).comp ((CompactSections F B (coefficientValues F B S)).subtype.comp
    ((restrict F B (coefficientValues F B S)).comp (FiniteSmoothRealizedSections F B S).subtype))

/-- A smooth normalized compact slice of a compact-finite section has a local expansion
in a fixed finite family of actual realized Levi coefficients. -/
theorem exists_smoothCompactSlice_expansion (f : CompactFiniteRealizedSections F B S)
    (hf : HasSmoothCompactSlices F B S f.val.val) (k : KI) (l : KF) :
    ∃ (r : ℕ) (c : Fin r → coefficientValues F B S) (φ : Fin r → A → ℂ),
      (∀ j, ContDiffAt ℝ ∞ (φ j) (compactMatrix F k)) ∧
      ∀ᶠ x in 𝓝 (compactMatrix F k), ∀ h : KI, compactMatrix F h = x →
        normalizedSlice F B f.val.val.val (compactPair F h l) = ∑ j, φ j x • (c j).val := by
  let ρ := finiteSmoothCompactAction F B S
  let V : Submodule ℂ (FiniteSmoothRealizedSections F B S) := FiniteVectors.orbitSpan ρ f.val
  let : FiniteDimensional ℂ V := f.property
  let L := (sliceMap F B S (compactPair F 1 l)).comp V.subtype
  let W : Submodule ℂ (M → ℂ) := LinearMap.range L
  let : FiniteDimensional ℂ W := Module.Finite.of_surjective L.rangeRestrict L.surjective_rangeRestrict
  let w (h : KI) : W := L.rangeRestrict ⟨ρ h f.val, FiniteVectors.action_mem_orbitSpan ρ h f.val⟩
  have hw (h : KI) : (w h).val = normalizedSlice F B f.val.val.val (compactPair F h l) := by
    funext m
    change normalizedSlice F B (RealizedSections.infiniteCompactAction F B S h f.val.val).val
      (compactPair F 1 l) m = _
    rw [show compactPair F h l = compactPair F 1 l * infiniteCompactInclusion F h by
      rw [compactPair_mul_infiniteCompactInclusion, one_mul]]
    simp only [normalizedSlice, RealizedSections.infiniteCompactAction_apply, Subgroup.coe_mul,
      mul_assoc]
    rfl
  have hmem (v : W) : v.val ∈ coefficientValues F B S := by
    obtain ⟨t, ht⟩ := v.property
    rw [← ht]
    exact t.val.val.property.2 _
  let e := Module.finBasis ℂ W
  let c (j : Fin (Module.finrank ℂ W)) : coefficientValues F B S := ⟨(e j).val, hmem (e j)⟩
  choose φ hφ hφe using fun j =>
    exists_smooth_dualExtension F B S W w k f.val.val hf l hw (e.coord j)
  refine ⟨_, c, φ, hφ, ?_⟩
  filter_upwards [Filter.eventually_all.mpr hφe] with x hx h hh
  rw [← hw]
  have he := congrArg (fun v : W => v.val) (e.sum_repr (w h))
  change (∑ j, e.repr (w h) j • (e j)).val = (w h).val at he
  rw [← he]
  change W.subtype (∑ j, e.repr (w h) j • e j) = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => by
    rw [map_smul, hx j h hh]
    rfl

end Langlands.Global.AdelicBlockScalarSections
