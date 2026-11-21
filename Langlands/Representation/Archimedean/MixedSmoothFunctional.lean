import Langlands.Representation.Archimedean.MixedSmoothVectors

/-! # Gluing compatible smooth functionals across finite levels -/

noncomputable section
set_option autoImplicit false

open scoped Manifold ContDiff

namespace Langlands.Archimedean.MixedSmooth

open Langlands.HarishChandraSchwartz SmoothInvariantSubspace

universe uA uG uL uE

variable {A : Type uA} [NormedAddCommGroup A] [NormedSpace ℝ A]
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace A G]
  {L : Type uL} [Group L] [TopologicalSpace L] [LocallyCompactSpace L]
  [NonarchimedeanGroup L]
  {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  (σ : L →* (E →L[ℂ] E)) (π : G →* (E →L[ℂ] E))
  (hcomm : ∀ g l x, π g (σ l x) = σ l (π g x))

local notation "I" => 𝓘(ℝ, A)
local notation "V∞" => Langlands.Archimedean.smoothVectors I π
local notation "V" => Vectors (A := A) σ π hcomm
local notation "K" => CompactOpenSubgroup L

/-- Agreement of two evaluations at every common fixed vector. -/
def CompatibleLevels (f : K → V∞ →ₗ[ℂ] ℂ) : Prop :=
  ∀ (J J' : K) (w : V∞), w.val ∈ fixedSubspace σ J.toSubgroup →
    w.val ∈ fixedSubspace σ J'.toSubgroup → f J w = f J' w

variable (f : CompactOpenSubgroup L → Langlands.Archimedean.smoothVectors 𝓘(ℝ, A) π →ₗ[ℂ] ℂ)
  (hf : CompatibleLevels (A := A) σ π f)

private def levelValue (w : V) : ℂ :=
  f (Classical.choose (exists_compactLevel σ π hcomm w)) w.val

include hf in
private theorem levelValue_eq (w : V) (J : K) (hw : w.val.val ∈ fixedSubspace σ J.toSubgroup) :
    levelValue σ π hcomm f w = f J w.val :=
  hf _ J w.val (Classical.choose_spec (exists_compactLevel σ π hcomm w)) hw

/-- Glue compatible evaluations to one linear functional on the mixed
smooth space, using a common compact open level for addition. -/
def glueFunctional : V →ₗ[ℂ] ℂ where
  toFun := levelValue σ π hcomm f
  map_add' v w := by
    obtain ⟨J, hJ⟩ := exists_compactLevel σ π hcomm v
    obtain ⟨J', hJ'⟩ := exists_compactLevel σ π hcomm w
    let B := J.inf J'
    have hv : v.val.val ∈ fixedSubspace σ B.toSubgroup :=
      fun k => hJ ⟨k.val, CompactOpenSubgroup.inf_le_left J J' k.property⟩
    have hw : w.val.val ∈ fixedSubspace σ B.toSubgroup :=
      fun k => hJ' ⟨k.val, CompactOpenSubgroup.inf_le_right J J' k.property⟩
    have hadd : (v + w).val.val ∈ fixedSubspace σ B.toSubgroup :=
      (fixedSubspace σ B.toSubgroup).add_mem hv hw
    rw [levelValue_eq σ π hcomm f hf (v + w) B hadd,
      levelValue_eq σ π hcomm f hf v B hv, levelValue_eq σ π hcomm f hf w B hw]
    exact map_add (f B) v.val w.val
  map_smul' c v := by
    obtain ⟨J, hJ⟩ := exists_compactLevel σ π hcomm v
    have hcv : (c • v).val.val ∈ fixedSubspace σ J.toSubgroup :=
      (fixedSubspace σ J.toSubgroup).smul_mem c hJ
    change levelValue σ π hcomm f (c • v) = c • levelValue σ π hcomm f v
    rw [levelValue_eq σ π hcomm f hf (c • v) J hcv, levelValue_eq σ π hcomm f hf v J hJ]
    exact map_smul (f J) c v.val

/-- The glued evaluation is exactly the given evaluation at every level
fixing the vector. -/
theorem glueFunctional_eq_of_fixed (w : V) (J : K) (hw : w.val.val ∈ fixedSubspace σ J.toSubgroup) :
    glueFunctional σ π hcomm f hf w = f J w.val :=
  levelValue_eq σ π hcomm f hf w J hw

end Langlands.Archimedean.MixedSmooth
