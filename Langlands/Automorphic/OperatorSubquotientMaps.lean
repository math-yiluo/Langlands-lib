import Langlands.Automorphic.OperatorSubquotient

/-! # Descending actual numerator maps to operator quotients -/

noncomputable section
universe uF
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}

local instance quotientMapRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance quotientMapContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance quotientMapSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance quotientMapFormGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance quotientMapStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance quotientMapRealizationGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

namespace OperatorSubquotient

variable (Q T : OperatorSubquotient F n)

/-- All whole-action numerator maps which carry the actual source denominator
into the actual target denominator. -/
def compatibleMaps :
    Submodule ℂ (Q.upper.representation.IntertwiningMap T.upper.representation) where
  carrier := {L | ∀ f, f ∈ Q.lower → L f ∈ T.lower}
  zero_mem' := by
    intro f hf
    exact T.lower.toSubmodule.zero_mem
  add_mem' hL hM := by
    intro f hf
    exact T.lower.toSubmodule.add_mem (hL f hf) (hM f hf)
  smul_mem' c L hL := by
    intro f hf
    exact T.lower.toSubmodule.smul_mem c (hL f hf)

/-- Descend an actual denominator-preserving whole-operator numerator map. -/
def map (L : Q.upper.representation.IntertwiningMap T.upper.representation)
    (h : ∀ f, f ∈ Q.lower → L f ∈ T.lower) :
    Q.representation.IntertwiningMap T.representation :=
  Q.lift (T.projection.comp L) (by
    intro f hf
    exact (T.projection_eq_zero_iff (L f)).mpr (h f hf))

@[simp] theorem map_projection
    (L : Q.upper.representation.IntertwiningMap T.upper.representation)
    (h : ∀ f, f ∈ Q.lower → L f ∈ T.lower) (f : Q.upper.Space) :
    Q.map T L h (Q.projection f) = T.projection (L f) := rfl

/-- The canonical quotient projections commute with the descended map. -/
theorem map_naturality
    (L : Q.upper.representation.IntertwiningMap T.upper.representation)
    (h : ∀ f, f ∈ Q.lower → L f ∈ T.lower) :
    (Q.map T L h).comp Q.projection = T.projection.comp L := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro f
  rfl

/-- The projection formula determines the descended map uniquely. -/
theorem map_unique
    (L : Q.upper.representation.IntertwiningMap T.upper.representation)
    (h : ∀ f, f ∈ Q.lower → L f ∈ T.lower)
    (M : Q.representation.IntertwiningMap T.representation)
    (hM : ∀ f, M (Q.projection f) = T.projection (L f)) :
    M = Q.map T L h :=
  Q.lift_unique (T.projection.comp L) _ M hM

/-- Descent is complex-linear on all compatible numerator intertwiners. -/
def mapLinear :
    Q.compatibleMaps T →ₗ[ℂ] (Q.representation.IntertwiningMap T.representation) where
  toFun L := Q.map T L.val L.property
  map_add' L M := by
    apply Eq.symm
    apply Q.map_unique T (L + M).val (L + M).property
    intro v
    exact (T.projection.toLinearMap.map_add (L.val v) (M.val v)).symm
  map_smul' c L := by
    apply Eq.symm
    apply Q.map_unique T (c • L).val (c • L).property
    intro v
    exact (T.projection.toLinearMap.map_smul c (L.val v)).symm

@[simp] theorem mapLinear_apply (L : Q.compatibleMaps T) :
    Q.mapLinear T L = Q.map T L.val L.property := rfl

@[simp] theorem map_id :
    Q.map Q (Representation.IntertwiningMap.id Q.upper.representation)
        (fun _ hf => hf) = Representation.IntertwiningMap.id Q.representation := by
  exact (Q.map_unique Q _ _ _ (fun _ => rfl)).symm

variable {Q T}

theorem map_comp {U : OperatorSubquotient F n}
    (M : T.upper.representation.IntertwiningMap U.upper.representation)
    (L : Q.upper.representation.IntertwiningMap T.upper.representation)
    (hM : ∀ f, f ∈ T.lower → M f ∈ U.lower)
    (hL : ∀ f, f ∈ Q.lower → L f ∈ T.lower) :
    Q.map U (M.comp L) (fun f hf => hM (L f) (hL f hf)) =
      (T.map U M hM).comp (Q.map T L hL) := by
  exact (Q.map_unique U _ _ _ (fun _ => rfl)).symm

/-- Exact kernel membership is tested in the original target denominator. -/
@[simp] theorem map_projection_eq_zero_iff
    (L : Q.upper.representation.IntertwiningMap T.upper.representation)
    (h : ∀ f, f ∈ Q.lower → L f ∈ T.lower) (f : Q.upper.Space) :
    Q.map T L h (Q.projection f) = 0 ↔ L f ∈ T.lower :=
  T.projection_eq_zero_iff (L f)

theorem map_eq_zero_iff
    (L : Q.upper.representation.IntertwiningMap T.upper.representation)
    (h : ∀ f, f ∈ Q.lower → L f ∈ T.lower) :
    Q.map T L h = 0 ↔ ∀ f, L f ∈ T.lower := by
  constructor
  · intro hz f
    apply (T.projection_eq_zero_iff (L f)).mp
    exact congrArg
      (fun M : Q.representation.IntertwiningMap T.representation =>
        M (Q.projection f)) hz
  · intro hz
    apply Eq.symm
    apply Q.map_unique T L h
    intro v
    exact ((T.projection_eq_zero_iff (L v)).mpr (hz v)).symm

/-- Injectivity is equivalent to exact reflection of denominator membership. -/
theorem map_injective_iff
    (L : Q.upper.representation.IntertwiningMap T.upper.representation)
    (h : ∀ f, f ∈ Q.lower → L f ∈ T.lower) :
    Function.Injective (Q.map T L h) ↔
      ∀ f, L f ∈ T.lower → f ∈ Q.lower := by
  constructor
  · intro hi f hf
    apply (Q.projection_eq_zero_iff f).mp
    apply hi
    exact ((T.projection_eq_zero_iff (L f)).mpr hf).trans
      (Q.map T L h).toLinearMap.map_zero.symm
  · intro hr
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm
    · intro f hf
      obtain ⟨v, rfl⟩ := Q.projection_surjective f
      exact (Q.projection_eq_zero_iff v).mpr
        (hr v ((T.projection_eq_zero_iff (L v)).mp hf))
    · exact bot_le

set_option maxHeartbeats 800000 in
/-- A surjective numerator map gives a surjective actual quotient map. -/
theorem map_surjective
    (L : Q.upper.representation.IntertwiningMap T.upper.representation)
    (h : ∀ f, f ∈ Q.lower → L f ∈ T.lower)
    (hs : Function.Surjective L) :
    Function.Surjective (Q.map T L h) := by
  intro f
  obtain ⟨v, hv⟩ := T.projection_surjective f
  obtain ⟨w, hw⟩ := hs v
  exact ⟨Q.projection w, (congrArg T.projection hw).trans hv⟩

set_option maxHeartbeats 800000 in
/-- Exact surjectivity asks only for numerator surjectivity modulo the target denominator. -/
theorem map_surjective_iff
    (L : Q.upper.representation.IntertwiningMap T.upper.representation)
    (h : ∀ f, f ∈ Q.lower → L f ∈ T.lower) :
    Function.Surjective (Q.map T L h) ↔
      ∀ v : T.upper.Space, ∃ w : Q.upper.Space, L w - v ∈ T.lower := by
  constructor
  · intro hs v
    obtain ⟨f, hf⟩ := hs (T.projection v)
    obtain ⟨w, hw⟩ := Q.projection_surjective f
    refine ⟨w, (T.projection_eq_zero_iff (L w - v)).mp ?_⟩
    exact (T.projection.toLinearMap.map_sub (L w) v).trans
      (sub_eq_zero.mpr ((congrArg (Q.map T L h) hw).trans hf))
  · intro hs f
    obtain ⟨v, hv⟩ := T.projection_surjective f
    obtain ⟨w, hw⟩ := hs v
    refine ⟨Q.projection w, ?_⟩
    apply Eq.trans ?_ hv
    apply sub_eq_zero.mp
    exact (T.projection.toLinearMap.map_sub (L w) v).symm.trans
      ((T.projection_eq_zero_iff (L w - v)).mpr hw)

/-- A surjective numerator intertwiner which reflects the denominators gives a
genuine equivalence of the whole quotient actions. -/
def mapEquiv
    (L : Q.upper.representation.IntertwiningMap T.upper.representation)
    (h : ∀ f, f ∈ Q.lower → L f ∈ T.lower)
    (hr : ∀ f, L f ∈ T.lower → f ∈ Q.lower)
    (hs : Function.Surjective L) : Q.Equivalence T :=
  (Q.map T L h).ofBijective ⟨(map_injective_iff L h).mpr hr, map_surjective L h hs⟩

@[simp] theorem mapEquiv_projection
    (L : Q.upper.representation.IntertwiningMap T.upper.representation)
    (h : ∀ f, f ∈ Q.lower → L f ∈ T.lower)
    (hr : ∀ f, L f ∈ T.lower → f ∈ Q.lower)
    (hs : Function.Surjective L) (f : Q.upper.Space) :
    mapEquiv L h hr hs (Q.projection f) = T.projection (L f) := rfl

end OperatorSubquotient
end Langlands.Automorphic
