import Langlands.Global.FiniteAdelicGL.RestrictedTensor
import Langlands.Correspondence.UnramifiedNormalization
import Langlands.Representation.Compact.SurjectivityProof
import Langlands.Representation.Exponents.WeylBranchPiecesSubquotient
import Langlands.Representation.RestrictedTensor.Exactness
import Langlands.Representation.Smooth.Admissibility.Extension

/-! # Restricted tensor products of actual local subquotients -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 500000

universe uF uV uW

namespace Langlands.Global.FiniteAdelicGL

open Correspondence (IsSubquotientOf)
open RestrictedTensor (map_injective_of_injective map_surjective_of_surjective)

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)
variable {V : FinitePlace F → Type uV} {W : FinitePlace F → Type uW}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
variable [∀ v, AddCommGroup (W v)] [∀ v, Module ℂ (W v)]
variable (ρ : ∀ v, Representation ℂ (FiniteLocalGL F n v) (V v))
  (σ : ∀ v, Representation ℂ (FiniteLocalGL F n v) (W v))
  (E : Finset (FinitePlace F))

/-- Compatible reference vectors exhibiting a subquotient between the two
actual finite adelic tensor representations. -/
structure TensorSubquotient where
  sourceReference : ∀ v, V v
  targetReference : ∀ v, W v
  source_fixed : ∀ v ∉ E, ∀ g ∈ localIntegral F n v,
    ρ v g (sourceReference v) = sourceReference v
  target_fixed : ∀ v ∉ E, ∀ g ∈ localIntegral F n v,
    σ v g (targetReference v) = targetReference v
  source_nonzero : ∀ v ∉ E, sourceReference v ≠ 0
  target_nonzero : ∀ v ∉ E, targetReference v ≠ 0
  subquotient : IsSubquotientOf
    (tensorRepresentation F n ρ E sourceReference source_fixed)
    (tensorRepresentation F n σ E targetReference target_fixed)

/-- Lift nonzero fixed vectors along the local quotient maps, and take
restricted tensors of the local inclusions and quotient maps. -/
def TensorSubquotient.ofLocalSubquotients
    (hρ : ∀ v, IsSmooth (ρ v)) (hσ : ∀ v, IsSmooth (σ v))
    (hsub : ∀ v, IsSubquotientOf (ρ v) (σ v))
    (hfixed : ∀ v ∉ E, fixedVectors (σ v) (localIntegral F n v).toSubgroup ≠ ⊥) :
    TensorSubquotient F n ρ σ E := by
  classical
  choose U q hq using hsub
  let υ (v : FinitePlace F) := (U v).toRepresentation
  have hlift (v : FinitePlace F) (hv : v ∉ E) :
      ∃ x : (U v).toSubmodule,
        x ∈ fixedVectors (υ v) (localIntegral F n v).toSubgroup ∧ q v x ≠ 0 := by
    obtain ⟨y, hy, hy_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hfixed v hv)
    have hsurj := Compact.fixedVectorSurjectivity (FiniteLocalGL F n v)
      (U v).toSubmodule (W v) (υ v) (σ v) (isSmooth_subrepresentation (hρ v) (U v))
      (hσ v) (localIntegral F n v) (isCompact_localIntegral F n v) (q v) (hq v)
    obtain ⟨x, hx⟩ := hsurj ⟨y, hy⟩
    have hxy : q v x = y := congrArg Subtype.val hx
    exact ⟨x, x.property, hxy ▸ hy_ne⟩
  choose x hx hx_ne using hlift
  let z (v : FinitePlace F) : (U v).toSubmodule := if hv : v ∉ E then x v hv else 0
  have hz (v : FinitePlace F) (hv : v ∉ E) (g : FiniteLocalGL F n v)
      (hg : g ∈ localIntegral F n v) : υ v g (z v) = z v := by
    simp only [z, dite_eq_left hv]
    exact hx v hv ⟨g, hg⟩
  let i (v : FinitePlace F) := WeylBranchPieces.subtypeMap (U v)
  let e (v : FinitePlace F) := i v (z v)
  let e' (v : FinitePlace F) := q v (z v)
  have hi (v : FinitePlace F) : Function.Injective (i v) := Subtype.val_injective
  have he (v : FinitePlace F) (hv : v ∉ E) (g : FiniteLocalGL F n v)
      (hg : g ∈ localIntegral F n v) : ρ v g (e v) = e v := by
    change ρ v g (i v (z v)) = i v (z v)
    rw [← (i v).isIntertwining, hz v hv g hg]
  have he' (v : FinitePlace F) (hv : v ∉ E) (g : FiniteLocalGL F n v)
      (hg : g ∈ localIntegral F n v) : σ v g (e' v) = e' v := by
    change σ v g (q v (z v)) = q v (z v)
    rw [← (q v).isIntertwining, hz v hv g hg]
  have he'_ne (v : FinitePlace F) (hv : v ∉ E) : e' v ≠ 0 := by
    simpa only [e', z, dite_eq_left hv] using hx_ne v hv
  have he_ne (v : FinitePlace F) (hv : v ∉ E) : e v ≠ 0 := by
    intro hzero
    have hz_zero : z v = 0 := hi v (by simpa only [map_zero] using hzero)
    exact he'_ne v hv (by simp only [e', hz_zero, map_zero])
  refine ⟨e, e', he, he', he_ne, he'_ne, ?_⟩
  let incl := tensorIntertwiner F n υ ρ E E z e hz he i (Filter.Eventually.of_forall fun _ => rfl)
  let proj := tensorIntertwiner F n υ σ E E z e' hz he' q (Filter.Eventually.of_forall fun _ => rfl)
  have hincl : Function.Injective incl :=
    map_injective_of_injective E E z e (fun v => (i v).toLinearMap) _ hi
  have hproj : Function.Surjective proj :=
    map_surjective_of_surjective E E z e' (fun v => (q v).toLinearMap) _ hq
  let rangeMap : (tensorRepresentation F n υ E z hz).IntertwiningMap
      incl.range.toRepresentation :=
    { toLinearMap := incl.toLinearMap.rangeRestrict
      isIntertwining' g := LinearMap.ext fun y =>
        Subtype.ext (incl.isIntertwining _ _ g y) }
  let equiv := rangeMap.ofBijective
    ⟨fun a b hab => hincl (congrArg Subtype.val hab), LinearMap.surjective_rangeRestrict _⟩
  exact ⟨incl.range, proj.comp equiv.symm.toIntertwiningMap, hproj.comp equiv.symm.surjective⟩

end Langlands.Global.FiniteAdelicGL
