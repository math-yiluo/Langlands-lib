import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.Tactic

/-!
# CM types on actual number-field embeddings

A CM type selects exactly one embedding from each complex-conjugate pair.
Restriction along a field inclusion induces a CM type. In particular, choosing
an embedding of an imaginary quadratic subfield gives the type used by Harris.
For a CM extension, every real embedding has a unique selected extension.
-/

noncomputable section

universe u v w

namespace Langlands.Global

open NumberField Algebra

/-- A CM type on a CM number field, expressed as a set of actual embeddings. -/
structure CMType (K : Type u) [Field K] [NumberField K] [IsCMField K] where
  embeddings : Set (K →+* ℂ)
  conjugate_mem_iff : ∀ σ, ComplexEmbedding.conjugate σ ∈ embeddings ↔ σ ∉ embeddings

namespace CMType

variable {K : Type u} [Field K] [NumberField K] [IsCMField K]

instance : SetLike (CMType K) (K →+* ℂ) where
  coe := embeddings
  coe_injective Φ Ψ h := by cases Φ; cases Ψ; cases h; rfl

@[ext]
theorem ext {Φ Ψ : CMType K} (h : ∀ σ, σ ∈ Φ ↔ σ ∈ Ψ) : Φ = Ψ :=
  SetLike.ext h

@[simp]
theorem mem_conjugate_iff (Φ : CMType K) (σ : K →+* ℂ) :
    ComplexEmbedding.conjugate σ ∈ Φ ↔ σ ∉ Φ :=
  Φ.conjugate_mem_iff σ

theorem mem_or_conjugate_mem (Φ : CMType K) (σ : K →+* ℂ) :
    σ ∈ Φ ∨ ComplexEmbedding.conjugate σ ∈ Φ := by
  by_cases h : σ ∈ Φ
  · exact Or.inl h
  · exact Or.inr ((mem_conjugate_iff Φ σ).mpr h)

theorem not_mem_and_conjugate_mem (Φ : CMType K) (σ : K →+* ℂ) :
    ¬ (σ ∈ Φ ∧ ComplexEmbedding.conjugate σ ∈ Φ) := by
  simp

/-- The conjugate CM type, equivalently the complementary set of embeddings. -/
def conjugate (Φ : CMType K) : CMType K where
  embeddings := (Φ : Set (K →+* ℂ))ᶜ
  conjugate_mem_iff σ := by simp

@[simp]
theorem mem_conjugate (Φ : CMType K) (σ : K →+* ℂ) :
    σ ∈ Φ.conjugate ↔ σ ∉ Φ := Iff.rfl

@[simp]
theorem conjugate_conjugate (Φ : CMType K) : Φ.conjugate.conjugate = Φ := by
  ext σ
  simp

/-- Two selected embeddings which induce the same infinite place are equal. -/
theorem eq_of_mk_eq (Φ : CMType K) {σ τ : K →+* ℂ} (hσ : σ ∈ Φ) (hτ : τ ∈ Φ)
    (h : InfinitePlace.mk σ = InfinitePlace.mk τ) : σ = τ := by
  rcases InfinitePlace.mk_eq_iff.mp h with h | h
  · exact h
  · exact False.elim ((mem_conjugate_iff Φ σ).mp (h.symm ▸ hτ) hσ)

theorem existsUnique_embedding (Φ : CMType K) (v : InfinitePlace K) :
    ∃! σ : K →+* ℂ, σ ∈ Φ ∧ InfinitePlace.mk σ = v := by
  obtain h | h := Φ.mem_or_conjugate_mem v.embedding
  · refine ⟨v.embedding, ⟨h, InfinitePlace.mk_embedding v⟩, ?_⟩
    intro τ hτ
    exact Φ.eq_of_mk_eq hτ.1 h (hτ.2.trans (InfinitePlace.mk_embedding v).symm)
  · refine ⟨ComplexEmbedding.conjugate v.embedding, ⟨h, by simp⟩, ?_⟩
    intro τ hτ
    apply Φ.eq_of_mk_eq hτ.1 h
    simpa using hτ.2

/-- The selected embedding at a specified infinite place. -/
def embedding (Φ : CMType K) (v : InfinitePlace K) : K →+* ℂ :=
  (Φ.existsUnique_embedding v).exists.choose

@[simp]
theorem embedding_mem (Φ : CMType K) (v : InfinitePlace K) : Φ.embedding v ∈ Φ :=
  (Φ.existsUnique_embedding v).exists.choose_spec.1

@[simp]
theorem mk_embedding (Φ : CMType K) (v : InfinitePlace K) :
    InfinitePlace.mk (Φ.embedding v) = v :=
  (Φ.existsUnique_embedding v).exists.choose_spec.2

/-- Selected complex embeddings are in bijection with the actual infinite places. -/
def equivInfinitePlace (Φ : CMType K) : {σ : K →+* ℂ // σ ∈ Φ} ≃ InfinitePlace K :=
  Equiv.ofBijective (fun σ ↦ InfinitePlace.mk σ.val)
    ⟨fun σ τ h ↦ Subtype.ext (Φ.eq_of_mk_eq σ.property τ.property h),
      fun v ↦ ⟨⟨Φ.embedding v, Φ.embedding_mem v⟩, Φ.mk_embedding v⟩⟩

@[simp]
theorem equivInfinitePlace_apply (Φ : CMType K) (σ : {σ : K →+* ℂ // σ ∈ Φ}) :
    Φ.equivInfinitePlace σ = InfinitePlace.mk σ.val := rfl

instance (Φ : CMType K) : Fintype {σ : K →+* ℂ // σ ∈ Φ} :=
  Fintype.ofEquiv (InfinitePlace K) Φ.equivInfinitePlace.symm

theorem card (Φ : CMType K) :
    Fintype.card {σ : K →+* ℂ // σ ∈ Φ} = InfinitePlace.nrComplexPlaces K := by
  rw [Fintype.card_congr Φ.equivInfinitePlace,
    InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]

theorem two_mul_card (Φ : CMType K) :
    2 * Fintype.card {σ : K →+* ℂ // σ ∈ Φ} = Module.finrank ℚ K := by
  rw [Φ.card, IsTotallyComplex.finrank]

/-- Any actual section of complex embeddings over infinite places determines a CM type. -/
def ofSection (s : InfinitePlace K → (K →+* ℂ))
    (hs : ∀ v, InfinitePlace.mk (s v) = v) : CMType K where
  embeddings := Set.range s
  conjugate_mem_iff σ := by
    constructor
    · rintro ⟨v, hv⟩ ⟨w, hw⟩
      have hvw : v = w := by
        rw [← hs v, hv, InfinitePlace.mk_conjugate_eq, ← hw, hs w]
      subst w
      have heq : ComplexEmbedding.conjugate σ = σ := hv.symm.trans hw
      exact IsTotallyComplex.complexEmbedding_not_isReal σ heq
    · intro h
      have heq : InfinitePlace.mk (s (InfinitePlace.mk σ)) = InfinitePlace.mk σ := hs _
      rcases InfinitePlace.mk_eq_iff.mp heq with heq | heq
      · exact False.elim (h ⟨_, heq⟩)
      · refine ⟨InfinitePlace.mk σ, ?_⟩
        simpa using congrArg ComplexEmbedding.conjugate heq

/-- A constructed CM type using Mathlib's chosen embedding at each infinite place. -/
def canonical (K : Type u) [Field K] [NumberField K] [IsCMField K] : CMType K :=
  ofSection InfinitePlace.embedding InfinitePlace.mk_embedding

instance : Nonempty (CMType K) := ⟨canonical K⟩

section Induction

variable {F : Type v} [Field F] [NumberField F] [IsCMField F]

/-- Induce a CM type by selecting all embeddings whose restriction belongs to it. -/
def induce (Φ : CMType F) (ι : F →+* K) : CMType K where
  embeddings := {σ | σ.comp ι ∈ Φ}
  conjugate_mem_iff σ := by
    change ComplexEmbedding.conjugate (σ.comp ι) ∈ Φ ↔ σ.comp ι ∉ Φ
    exact Φ.conjugate_mem_iff _

@[simp]
theorem mem_induce (Φ : CMType F) (ι : F →+* K) (σ : K →+* ℂ) :
    σ ∈ Φ.induce ι ↔ σ.comp ι ∈ Φ := Iff.rfl

@[simp]
theorem induce_conjugate (Φ : CMType F) (ι : F →+* K) :
    Φ.conjugate.induce ι = (Φ.induce ι).conjugate := by
  ext σ
  rfl

theorem induce_comp {E : Type w} [Field E] [NumberField E] [IsCMField E]
    (Φ : CMType E) (ι : E →+* F) (j : F →+* K) :
    (Φ.induce ι).induce j = Φ.induce (j.comp ι) := by
  ext σ
  rfl

variable [IsQuadraticExtension ℚ F]

private theorem quadratic_mk_eq (σ τ : F →+* ℂ) :
    InfinitePlace.mk σ = InfinitePlace.mk τ := by
  have hc : Fintype.card (InfinitePlace F) = 1 := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
    have h := IsTotallyComplex.finrank (K := F)
    have hq := IsQuadraticExtension.finrank_eq_two ℚ F
    omega
  exact Fintype.card_le_one_iff.mp hc.le _ _

/-- For an imaginary quadratic field the chosen embedding alone is a CM type. -/
def ofImaginaryQuadratic (τ : F →+* ℂ) : CMType F where
  embeddings := {τ}
  conjugate_mem_iff σ := by
    change ComplexEmbedding.conjugate σ = τ ↔ σ ≠ τ
    constructor
    · intro h e
      subst σ
      exact IsTotallyComplex.complexEmbedding_not_isReal τ h
    · intro h
      exact (InfinitePlace.mk_eq_iff.mp (quadratic_mk_eq σ τ)).resolve_left h

@[simp]
theorem mem_ofImaginaryQuadratic (τ σ : F →+* ℂ) :
    σ ∈ ofImaginaryQuadratic τ ↔ σ = τ := Iff.rfl

/-- Harris's CM type: all embeddings restricting to one fixed embedding of
the imaginary quadratic subfield. -/
def inducedFromImaginaryQuadratic (ι : F →+* K) (τ : F →+* ℂ) : CMType K :=
  (ofImaginaryQuadratic τ).induce ι

@[simp]
theorem mem_inducedFromImaginaryQuadratic (ι : F →+* K) (τ : F →+* ℂ)
    (σ : K →+* ℂ) :
    σ ∈ inducedFromImaginaryQuadratic ι τ ↔ σ.comp ι = τ := Iff.rfl

theorem induced_embedding_restrict (ι : F →+* K) (τ : F →+* ℂ)
    (v : InfinitePlace K) :
    ((inducedFromImaginaryQuadratic ι τ).embedding v).comp ι = τ :=
  (inducedFromImaginaryQuadratic ι τ).embedding_mem v

end Induction

section RealEmbeddings

variable (E : Type v) [Field E] [NumberField E] [IsTotallyReal E]
  [Algebra E K] [IsQuadraticExtension E K]

/-- Restriction of infinite places is a bijection in an actual CM extension. -/
def realPlaceEquiv : InfinitePlace K ≃ InfinitePlace E :=
  Equiv.ofBijective (fun v : InfinitePlace K ↦ v.comap (algebraMap E K)) (by
    apply (Fintype.bijective_iff_surjective_and_card _).mpr
    refine ⟨InfinitePlace.comap_surjective, ?_⟩
    have hK := IsTotallyComplex.finrank (K := K)
    have hE := IsTotallyReal.finrank (K := E)
    have hmul := Module.finrank_mul_finrank ℚ E K
    have hq := IsQuadraticExtension.finrank_eq_two E K
    rw [hq] at hmul
    simp only [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero (K := K),
      IsTotallyReal.nrComplexPlaces_eq_zero (K := E),
      zero_add, add_zero]
    omega)

@[simp]
theorem realPlaceEquiv_apply (v : InfinitePlace K) :
    realPlaceEquiv (K := K) E v = v.comap (algebraMap E K) := rfl

/-- Extend a real embedding by the unique selected complex embedding above it. -/
def embeddingAbove (Φ : CMType K) (τ : E →+* ℝ) : K →+* ℂ :=
  Φ.embedding ((realPlaceEquiv (K := K) E).symm
    (InfinitePlace.mk (Complex.ofRealHom.comp τ)))

@[simp]
theorem embeddingAbove_mem (Φ : CMType K) (τ : E →+* ℝ) :
    Φ.embeddingAbove E τ ∈ Φ := Φ.embedding_mem _

theorem embeddingAbove_restrict (Φ : CMType K) (τ : E →+* ℝ) :
    (Φ.embeddingAbove E τ).comp (algebraMap E K) = Complex.ofRealHom.comp τ := by
  have hm : InfinitePlace.mk ((Φ.embeddingAbove E τ).comp (algebraMap E K)) =
      InfinitePlace.mk (Complex.ofRealHom.comp τ) := by
    rw [← InfinitePlace.comap_mk, embeddingAbove, Φ.mk_embedding,
      ← realPlaceEquiv_apply, Equiv.apply_symm_apply]
  rcases InfinitePlace.mk_eq_iff.mp hm with h | h
  · exact h
  · rwa [ComplexEmbedding.isReal_iff.mp
      (IsTotallyReal.complexEmbedding_isReal _)] at h

theorem eq_embeddingAbove (Φ : CMType K) (τ : E →+* ℝ) {σ : K →+* ℂ}
    (hσ : σ ∈ Φ) (hτ : σ.comp (algebraMap E K) = Complex.ofRealHom.comp τ) :
    σ = Φ.embeddingAbove E τ := by
  apply Φ.eq_of_mk_eq hσ (Φ.embeddingAbove_mem E τ)
  apply (realPlaceEquiv (K := K) E).injective
  simp only [realPlaceEquiv_apply, InfinitePlace.comap_mk,
    hτ, Φ.embeddingAbove_restrict E τ]

theorem existsUnique_embeddingAbove (Φ : CMType K) (τ : E →+* ℝ) :
    ∃! σ : K →+* ℂ, σ ∈ Φ ∧
      σ.comp (algebraMap E K) = Complex.ofRealHom.comp τ :=
  ⟨Φ.embeddingAbove E τ, ⟨Φ.embeddingAbove_mem E τ, Φ.embeddingAbove_restrict E τ⟩,
    fun _ h ↦ Φ.eq_embeddingAbove E τ h.1 h.2⟩

/-- In the induced type, the selected extension simultaneously has the prescribed
restriction to the imaginary quadratic field and to the totally real field. -/
theorem induced_embeddingAbove_restrict {F : Type w} [Field F] [NumberField F]
    [IsCMField F] [IsQuadraticExtension ℚ F]
    (ι : F →+* K) (τ₀ : F →+* ℂ) (τ : E →+* ℝ) :
    ((inducedFromImaginaryQuadratic ι τ₀).embeddingAbove E τ).comp ι = τ₀ :=
  (inducedFromImaginaryQuadratic ι τ₀).embeddingAbove_mem E τ

end RealEmbeddings
end CMType
end Langlands.Global
