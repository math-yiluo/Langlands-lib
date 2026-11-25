import Langlands.ClassFieldTheory.Global.IdeleGaloisDescentProof
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-! # Galois comparison at a unique finite place -/

noncomputable section

universe uF uE

set_option autoImplicit false

namespace Langlands.Global.AdelicFunctoriality

open IsDedekindDomain NumberField
open scoped NumberField FiniteExtension

variable {F : Type uF} {E : Type uE} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] {v : HeightOneSpectrum (𝓞 F)} (w : FinitePlacesAbove E v)

omit [NumberField F] in
/-- An automorphism over `F` fixes the unique finite place of `E` over `v`. -/
theorem finitePlaceEquiv_eq_of_unique (hw : ∀ w' : FinitePlacesAbove E v, w' = w)
    (σ : E ≃ₐ[F] E) : finitePlaceEquiv σ.toRingEquiv w.1 = w.1 := by
  let : w.1.asIdeal.LiesOver v.asIdeal := w.2
  let w' : FinitePlacesAbove E v :=
    ⟨_, ClassFieldTheory.Global.IdeleGaloisDescentProof.liesOver_finitePlaceEquiv σ v w.1⟩
  exact congrArg Subtype.val (hw w')

/-- The degree of the completion at the unique finite place is the global degree. -/
theorem localDegree_eq_global_of_unique (hw : ∀ w' : FinitePlacesAbove E v, w' = w) :
    letI : w.1.asIdeal.LiesOver v.asIdeal := w.2
    Module.finrank (v.adicCompletion F) (w.1.adicCompletion E) = Module.finrank F E := by
  let : w.1.asIdeal.LiesOver v.asIdeal := w.2
  let : Unique (FinitePlacesAbove E v) := ⟨⟨w⟩, hw⟩
  rw [localDegree_eq v w.1]
  simpa only [Fintype.sum_unique, hw default] using
    finitePlacesAbove_sum_ramification_inertia (L := E) v

section Galois

variable [IsGalois F E]

local instance : w.1.asIdeal.LiesOver v.asIdeal := w.2

private def restrictCompletionAut :
    (w.1.adicCompletion E ≃ₐ[v.adicCompletion F] w.1.adicCompletion E) →* (E ≃ₐ[F] E) :=
  (AlgEquiv.restrictNormalHom E).comp (AlgEquiv.restrictScalarsHom F)

private theorem restrictCompletionAut_apply
    (τ : w.1.adicCompletion E ≃ₐ[v.adicCompletion F] w.1.adicCompletion E) (x : E) :
    algebraMap E (w.1.adicCompletion E) (restrictCompletionAut w τ x) =
      τ (algebraMap E (w.1.adicCompletion E) x) := by
  simp only [restrictCompletionAut, MonoidHom.comp_apply, AlgEquiv.restrictNormalHom,
    MonoidHom.mk'_apply, AlgEquiv.restrictNormal_commutes]
  rfl

/-- Extension to the completion at the unique place above `v` identifies the
actual global and local Galois groups. -/
def uniquePlaceCompletionAutEquiv (hw : ∀ w' : FinitePlacesAbove E v, w' = w) :
    (E ≃ₐ[F] E) ≃* (w.1.adicCompletion E ≃ₐ[v.adicCompletion F] w.1.adicCompletion E) := by
  haveI := isGalois_adicCompletion v w.1
  have hinj : Function.Injective (restrictCompletionAut w) := by
    intro τ η h
    have htop : τ.toAlgHom.equalizer η.toAlgHom = ⊤ :=
      subalgebra_eq_top_of_algebraMap_mem v w.1 _ (fun x => by
        rw [AlgHom.mem_equalizer]
        change τ (algebraMap E _ x) = η (algebraMap E _ x)
        rw [← restrictCompletionAut_apply w, ← restrictCompletionAut_apply w, h])
    apply AlgEquiv.ext
    intro x
    have hx : x ∈ τ.toAlgHom.equalizer η.toAlgHom := by rw [htop]; trivial
    exact (AlgHom.mem_equalizer _ _ _).mp hx
  have hcard : Nat.card (w.1.adicCompletion E ≃ₐ[v.adicCompletion F] w.1.adicCompletion E) =
      Nat.card (E ≃ₐ[F] E) := by
    rw [IsGalois.card_aut_eq_finrank (v.adicCompletion F) (w.1.adicCompletion E),
      IsGalois.card_aut_eq_finrank F E, localDegree_eq_global_of_unique w hw]
  exact (MulEquiv.ofBijective (restrictCompletionAut w)
    ((Nat.bijective_iff_injective_and_card _).mpr ⟨hinj, hcard⟩)).symm

/-- The local automorphism in the comparison extends the original field automorphism. -/
@[simp] theorem uniquePlaceCompletionAutEquiv_algebraMap
    (hw : ∀ w' : FinitePlacesAbove E v, w' = w) (σ : E ≃ₐ[F] E) (x : E) :
    uniquePlaceCompletionAutEquiv w hw σ (algebraMap E (w.1.adicCompletion E) x) =
      algebraMap E (w.1.adicCompletion E) (σ x) := by
  have h : restrictCompletionAut w (uniquePlaceCompletionAutEquiv w hw σ) = σ :=
    (uniquePlaceCompletionAutEquiv w hw).symm_apply_apply σ
  rw [← restrictCompletionAut_apply w, h]

/-- Each nonidentity local automorphism comes from a nontrivial power of
the global cyclic generator, with exponent strictly below the degree. -/
theorem exists_pow_of_completionAut_ne_one
    (hw : ∀ w' : FinitePlacesAbove E v, w' = w) (σ : E ≃ₐ[F] E)
    (hgen : ∀ η : E ≃ₐ[F] E, η ∈ Subgroup.zpowers σ)
    (τ : w.1.adicCompletion E ≃ₐ[v.adicCompletion F] w.1.adicCompletion E) (hτ : τ ≠ 1) :
    ∃ i : ℕ, 0 < i ∧ i < Module.finrank F E ∧
      uniquePlaceCompletionAutEquiv w hw (σ ^ i) = τ := by
  classical
  let e := uniquePlaceCompletionAutEquiv w hw
  have horder : orderOf σ = Module.finrank F E :=
    (orderOf_eq_card_of_forall_mem_zpowers hgen).trans (IsGalois.card_aut_eq_finrank F E)
  have hmem := (isOfFinOrder_of_finite σ).mem_zpowers_iff_mem_range_orderOf.mp (hgen (e.symm τ))
  obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hmem
  have he : e (σ ^ i) = τ := by rw [heq, e.apply_symm_apply]
  have hi0 : 0 < i := Nat.pos_of_ne_zero fun h => hτ <| by simpa [h] using he.symm
  exact ⟨i, hi0, horder ▸ Finset.mem_range.mp hi, he⟩

end Galois

end Langlands.Global.AdelicFunctoriality
