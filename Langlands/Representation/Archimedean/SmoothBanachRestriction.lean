import Langlands.Analysis.ClosedSubmoduleSmoothness
import Langlands.Representation.Archimedean.SmoothDerivativeCompleteness
import Langlands.Representation.Archimedean.SmoothHilbert
import Langlands.Representation.Archimedean.SmoothIntertwiner

/-! # Genuine smooth vectors of a closed invariant Banach subspace -/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.DerivativeSmoothVectors

universe uA uE uG

section Restriction

variable {G : Type uG} [Group G] {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (R : G →* (E →L[ℂ] E)) (U : Submodule ℂ E)
  (hU : ∀ g x, x ∈ U → R g x ∈ U)

/-- Restrict a bounded-operator action to an invariant subspace. -/
def banachRestriction : G →* (U →L[ℂ] U) where
  toFun g := (R g).restrict (hU g)
  map_one' := by
    ext v : 1
    apply Subtype.ext
    change R 1 (v : E) = v.val
    simp
  map_mul' g h := by
    ext v : 1
    apply Subtype.ext
    change R (g * h) (v : E) = R g (R h (v : E))
    rw [map_mul, mul_apply_eq_comp]

theorem isContinuousRepresentation_banachRestriction [TopologicalSpace G]
    (hR : IsContinuousRepresentation R) : IsContinuousRepresentation (banachRestriction R U hU) :=
  Continuous.subtype_mk (hR.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) _

end Restriction

variable {A : Type uA} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (R : Aˣ →* (E →L[ℂ] E)) (U : Submodule ℂ E)
  (hUG : ∀ (g : Aˣ) x, x ∈ U → R g x ∈ U)

local notation "I" => 𝓘(ℝ, A)
local notation "S" => banachRestriction R U hUG
local notation "ε" => derivativeCLM I R []

omit [CompleteSpace A] in
private theorem contDiffOn_submodule_of_ambient {f : A → U} {V : Set A}
    (hV : IsOpen V) (hU : IsClosed (U : Set E))
    (hf : ContDiffOn ℝ ∞ (fun y => (f y).val) V) : ContDiffOn ℝ ∞ f V := by
  let e : ULift.{uE} A ≃ₗᵢ[ℝ] A := LinearIsometryEquiv.ulift ℝ A
  let j : ULift.{uA} E ≃ₗᵢ[ℝ] E := LinearIsometryEquiv.ulift ℝ E
  let W := (U.restrictScalars ℝ).map j.symm.toLinearEquiv.toLinearMap
  let q := LinearIsometryEquiv.submoduleMap (U.restrictScalars ℝ) j.symm
  let g (x : ULift.{uE} A) : W := q (f (e x))
  have hW : IsClosed (W : Set (ULift.{uA} E)) :=
    j.symm.toHomeomorph.isClosedMap _ hU
  have hg : ContDiffOn ℝ ∞ (fun x => (g x).val) (e ⁻¹' V) :=
    j.symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn
      (hf.comp e.toContinuousLinearEquiv.contDiff.contDiffOn fun _ hx => hx)
  have hs := Langlands.Analysis.contDiffOn_infty_of_closedSubmodule hW
    (hV.preimage e.continuous) hg
  have he : MapsTo e.symm V (e ⁻¹' V) := fun y hy => by
    change e (e.symm y) ∈ V
    simpa only [LinearIsometryEquiv.apply_symm_apply] using hy
  have h := q.symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn
    (hs.comp e.symm.toContinuousLinearEquiv.contDiff.contDiffOn he)
  refine h.congr fun y _ => ?_
  change f y = q.symm (q (f (e (e.symm y))))
  rw [LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.apply_symm_apply]

private theorem isSmoothVector_banachRestriction (hU : IsClosed (U : Set E))
    (u : U) (h : IsSmoothVector I R u.val) : IsSmoothVector I S u := by
  let V := Set.range (Units.val : Aˣ → A)
  let c := Units.isOpenEmbedding_val.toOpenPartialHomeomorph (Units.val : Aˣ → A)
  have hc : ContMDiffOn I I ∞ c.symm V :=
    contMDiffOn_isOpenEmbedding_symm («I» := I) Units.isOpenEmbedding_val
  let f (y : A) := S (c.symm y) u
  have hf : ContDiffOn ℝ ∞ (fun y => (f y).val) V :=
    ((h.contMDiffOn (s := univ)).comp hc (fun _ _ => mem_univ _)).contDiffOn
  have hsm := contDiffOn_submodule_of_ambient U Units.isOpenEmbedding_val.isOpen_range hU hf
  refine (hsm.contMDiffOn.comp_contMDiff (Units.contMDiff_val (n := ∞))
    (fun g : Aˣ => ⟨g, rfl⟩)).congr fun g => ?_
  have he : c.symm (g : A) = g :=
    Units.isOpenEmbedding_val.toOpenPartialHomeomorph_left_inv (Units.val : Aˣ → A)
  change S g u = S (c.symm (g : A)) u
  rw [he]

variable [FiniteDimensional ℝ A] [CompleteSpace E]

/-- The genuine smooth restriction to a closed invariant Banach subspace is
a closed embedding onto the smooth vectors with values in the subspace. -/
def SmoothBanachRestrictionStatement : Prop :=
  IsContinuousRepresentation R → IsClosed (U : Set E) →
    IsContinuousRepresentation S ∧
    ∃ T : DerivativeSmoothVectors I S →L[ℂ] DerivativeSmoothVectors I R,
      IsClosedEmbedding T ∧ T.toLinearMap.range = U.comap (ε).toLinearMap ∧
      (∀ g v, T (representation I S g v) = representation I R g (T v)) ∧
      ∀ v, ε (T v) = (derivativeCLM I S [] v : E)

theorem smoothBanachRestriction : SmoothBanachRestrictionStatement R U hUG := by
  intro hR hU
  have hS := isContinuousRepresentation_banachRestriction R U hUG hR
  have hj (g : Aˣ) (x : U) : U.subtypeL (S g x) = R g (U.subtypeL x) := rfl
  let T := SmoothIntertwiner.derivativeMap I S R U.subtypeL hj
  let α := derivativeCoordinates I S
  let β := derivativeCoordinates I R
  let j : (List A → U) → (List A → E) := fun f w => (f w : E)
  let _ : CompleteSpace U := hU.completeSpace_coe
  have hα : IsClosedEmbedding α :=
    ⟨isEmbedding_derivativeCoordinates I S, isClosed_range_derivativeCoordinates_units S hS⟩
  have hjc : IsClosedEmbedding j :=
    IsClosedEmbedding.piMap fun _ => hU.isClosedEmbedding_subtypeVal
  have he : β ∘ T = j ∘ α := by
    funext v w
    exact SmoothIntertwiner.derivativeCoordinates_derivativeMapLinear I S R U.subtypeL hj v w
  have hT : IsClosedEmbedding T :=
    IsClosedEmbedding.of_comp (isEmbedding_derivativeCoordinates I R) (he.symm ▸ hjc.comp hα)
  have hTG (g : Aˣ) (v : DerivativeSmoothVectors I S) :
      T (representation I S g v) = representation I R g (T v) := by
    apply (toSmooth I R).injective
    exact SmoothIntertwiner.map_smoothRepresentation I S R U.subtypeL hj g (toSmooth I S v)
  have hTε (v : DerivativeSmoothVectors I S) : ε (T v) = (derivativeCLM I S [] v : E) :=
    SmoothIntertwiner.derivativeCoordinates_derivativeMapLinear I S R U.subtypeL hj v []
  refine ⟨hS, T, hT, ?_, hTG, hTε⟩
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    change ε (T w) ∈ U
    rw [hTε]
    exact (derivativeCLM I S [] w).prop
  · intro hv
    let u : U := ⟨ε v, hv⟩
    have h := isSmoothVector_banachRestriction R U hUG hU u (toSmooth I R v).prop
    let w := (toSmooth I S).symm ⟨u, h⟩
    refine ⟨w, ?_⟩
    apply (toSmooth I R).injective
    apply Subtype.ext
    change ε (T w) = ε v
    rw [hTε]
    exact congrArg (fun z : smoothVectors I S => z.val.val)
      (LinearEquiv.apply_symm_apply (toSmooth I S) ⟨u, h⟩)

end Langlands.Archimedean.DerivativeSmoothVectors
