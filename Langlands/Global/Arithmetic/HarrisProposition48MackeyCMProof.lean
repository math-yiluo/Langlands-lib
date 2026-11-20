import Langlands.Global.Arithmetic.CMSubfield
import Mathlib.FieldTheory.Normal.Closure

/-! # CM fields in the arithmetic Mackey step -/

noncomputable section

namespace Langlands.Global.CMRealization

open NumberField ComplexEmbedding IntermediateField

private theorem isCMField_of_common_conjugate (K : Type*) [Field K] [NumberField K]
    [IsTotallyComplex K]
    (h : ∀ x : K, ∃ y : K, ∀ φ : K →+* ℂ, φ y = starRingEnd ℂ (φ x)) :
    IsCMField K := by
  let φ : K →+* ℂ := Classical.choice inferInstance
  let c : K → K := fun x => (h x).choose
  have hc (ψ : K →+* ℂ) (x : K) : ψ (c x) = starRingEnd ℂ (ψ x) :=
    (h x).choose_spec ψ
  have hcc (x : K) : c (c x) = x := by
    apply φ.injective
    rw [hc, hc]
    simp
  let cRing : K ≃+* K :=
    { toFun := c
      invFun := c
      left_inv := hcc
      right_inv := hcc
      map_mul' := fun x y => φ.injective (by rw [hc, map_mul, map_mul, map_mul, hc, hc])
      map_add' := fun x y => φ.injective (by rw [hc, map_add, map_add, map_add, hc, hc]) }
  let σ : K ≃ₐ[ℚ] K := AlgEquiv.ofRingEquiv (f := cRing) fun r => by
    simp only [eq_ratCast, map_ratCast]
  have hσ (ψ : K →+* ℂ) : IsConj ψ σ :=
    RingHom.ext fun x => (hc ψ x).symm
  let R : IntermediateField ℚ K := fixedField (Subgroup.zpowers σ)
  have : IsTotallyReal R := ⟨fun w => by
    rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    ext1 x
    have hx : σ (algebraMap R K x) = algebraMap R K x :=
      (mem_fixedField_iff _ _).mp x.property σ (Subgroup.mem_zpowers σ)
    have hreal := (hσ (ComplexEmbedding.lift K w.embedding)).eq (algebraMap R K x)
    rw [hx, ComplexEmbedding.lift_algebraMap_apply] at hreal
    exact hreal.symm⟩
  have hσne := (isConj_ne_one_iff (hσ φ)).mpr (IsTotallyComplex.complexEmbedding_not_isReal φ)
  have : Algebra.IsQuadraticExtension R K := ⟨by
    change Module.finrank (fixedField (Subgroup.zpowers σ)) K = 2
    rw [finrank_fixedField_eq_card, Nat.card_zpowers, orderOf_isConj_two_of_ne_one (hσ φ) hσne]⟩
  exact IsCMField.ofCMExtension R K

/-- The relative normal closure of an extension of CM number fields is CM. -/
theorem isCMField_of_normalClosure (E K L : Type*) [Field E] [Field K] [Field L]
    [NumberField E] [NumberField K] [NumberField L] [IsCMField E] [IsCMField K]
    [Algebra E K] [Algebra E L] [hL : IsNormalClosure E K L] : IsCMField L := by
  let : IsTotallyComplex L := isTotallyComplex_of_algebra E L
  let S : IntermediateField E L :=
    { carrier := {x | ∃ y : L, ∀ φ : L →+* ℂ, φ y = starRingEnd ℂ (φ x)}
      zero_mem' := ⟨0, by simp⟩
      one_mem' := ⟨1, by simp⟩
      add_mem' := by
        rintro x z ⟨y, hy⟩ ⟨w, hw⟩
        exact ⟨y + w, fun φ => by rw [map_add, hy, hw, map_add, map_add]⟩
      mul_mem' := by
        rintro x z ⟨y, hy⟩ ⟨w, hw⟩
        exact ⟨y * w, fun φ => by rw [map_mul, hy, hw, map_mul, map_mul]⟩
      inv_mem' := by
        rintro x ⟨y, hy⟩
        exact ⟨y⁻¹, fun φ => by rw [map_inv₀, hy, map_inv₀, map_inv₀]⟩
      algebraMap_mem' := fun x =>
        ⟨algebraMap E L (conjQ E x), fun φ => embedding_conjQ (φ.comp (algebraMap E L)) x⟩ }
  have htop := (Algebra.IsAlgebraic.isNormalClosure_iff.mp hL).2
  have hS : normalClosure E K L ≤ S := normalClosure_le_iff.mpr fun f z ⟨x, hx⟩ => by
    change f x = z at hx
    subst z
    exact ⟨f (conjQ K x), fun φ => embedding_conjQ (φ.comp f.toRingHom) x⟩
  apply isCMField_of_common_conjugate L
  intro x
  exact hS (htop.symm ▸ (mem_top : x ∈ (⊤ : IntermediateField E L)))

/-- If a CM number field is Galois over a totally complex base, all intermediate fields are CM. -/
theorem isCMField_intermediateField {E L : Type*} [Field E] [Field L] [NumberField E]
    [NumberField L] [IsTotallyComplex E] [IsCMField L] [Algebra E L] [IsGalois E L]
    (D : IntermediateField E L) : IsCMField D := by
  let : IsTotallyComplex D := isTotallyComplex_of_algebra E D
  apply isCMField_of_common_conjugate D
  intro x
  have hx : conjQ L (x : L) ∈ D := by
    have hfixed : conjQ L (x : L) ∈ fixedField D.fixingSubgroup := by
      rw [mem_fixedField_iff]
      intro σ hσ
      have hcomm : σ (conjQ L (x : L)) = conjQ L (σ x) :=
        conjQ_central (σ.restrictScalars ℚ) x
      rw [hcomm, (mem_fixingSubgroup_iff _ _).mp hσ _ x.property]
    rwa [IsGalois.fixedField_fixingSubgroup D] at hfixed
  let y : D := ⟨conjQ L (x : L), hx⟩
  refine ⟨y, fun ψ => ?_⟩
  have h := embedding_conjQ (ComplexEmbedding.lift L ψ) (x : L)
  change (ComplexEmbedding.lift L ψ) (algebraMap D L y) =
    starRingEnd ℂ ((ComplexEmbedding.lift L ψ) (algebraMap D L x)) at h
  simpa only [ComplexEmbedding.lift_algebraMap_apply] using h

end Langlands.Global.CMRealization
