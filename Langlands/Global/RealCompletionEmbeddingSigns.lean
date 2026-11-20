import Langlands.Global.RealCompletionWeakApproximation
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

/-! # Prescribing a sign at one embedding into a real completion -/

noncomputable section

universe u

open NumberField

namespace Langlands.Global

variable (F E : Type u) [Field F] [Field E] [Algebra F E]

private abbrev RealPlaces (K : Type u) [Field K] := {w : InfinitePlace K // w.IsReal}

private def completionComplexEmbedding (w : RealPlaces F) (f : E →ₐ[F] w.1.Completion) : E →+* ℂ :=
  Complex.ofRealHom.comp ((InfinitePlace.Completion.ringEquivRealOfIsReal w.2).toRingHom.comp
    f.toRingHom)

private theorem completionComplexEmbedding_real (w : RealPlaces F) (f : E →ₐ[F] w.1.Completion) :
    ComplexEmbedding.IsReal (completionComplexEmbedding F E w f) := by
  rw [ComplexEmbedding.isReal_iff]
  apply RingHom.ext
  intro x
  change star (Complex.ofReal ((InfinitePlace.Completion.ringEquivRealOfIsReal w.2) (f x))) = _
  exact Complex.conj_ofReal _

private def completionEmbeddingPlace (s : Σ w : RealPlaces F, E →ₐ[F] w.1.Completion) : RealPlaces E :=
  ⟨InfinitePlace.mk (completionComplexEmbedding F E s.1 s.2),
    InfinitePlace.isReal_mk_iff.mpr (completionComplexEmbedding_real F E s.1 s.2)⟩

private theorem completionComplexEmbedding_comp (w : RealPlaces F) (f : E →ₐ[F] w.1.Completion) :
    (completionComplexEmbedding F E w f).comp (algebraMap F E) = w.1.embedding := by
  apply RingHom.ext
  intro x
  change Complex.ofReal ((InfinitePlace.Completion.ringEquivRealOfIsReal w.2)
    (f (algebraMap F E x))) = w.1.embedding x
  rw [f.commutes, InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
  change Complex.ofReal (InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
    ((WithAbs.equiv w.1.1).symm x : w.1.Completion)) = _
  rw [InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe, RingEquiv.apply_symm_apply,
    InfinitePlace.embedding_of_isReal_apply]

private theorem completionEmbeddingPlace_injective :
    Function.Injective (completionEmbeddingPlace F E) := by
  rintro ⟨w, f⟩ ⟨v, g⟩ h
  have hres (w' : RealPlaces F) (f' : E →ₐ[F] w'.1.Completion) :
      (completionEmbeddingPlace F E ⟨w', f'⟩).1.comap (algebraMap F E) = w'.1 := by
    change (InfinitePlace.mk (completionComplexEmbedding F E w' f')).comap _ = _
    rw [InfinitePlace.comap_mk, completionComplexEmbedding_comp, InfinitePlace.mk_embedding]
  have hw : w = v := Subtype.ext ((hres w f).symm.trans
    ((congrArg (fun w' : RealPlaces E => w'.1.comap (algebraMap F E)) h).trans (hres v g)))
  subst v
  have hemb (a : E →ₐ[F] w.1.Completion) :
      (completionEmbeddingPlace F E ⟨w, a⟩).1.embedding = completionComplexEmbedding F E w a :=
    InfinitePlace.embedding_mk_eq_of_isReal (completionComplexEmbedding_real F E w a)
  have hfg := (hemb f).symm.trans ((congrArg (fun v' : RealPlaces E => v'.1.embedding) h).trans (hemb g))
  have hfg' : f = g := by
    apply AlgHom.ext
    intro x
    apply (InfinitePlace.Completion.ringEquivRealOfIsReal w.2).injective
    apply Complex.ofReal_injective
    exact DFunLike.congr_fun hfg x
  rw [hfg']

private theorem completionEmbeddingPlace_realValue (w : RealPlaces F) (f : E →ₐ[F] w.1.Completion)
    (a : E) :
    InfinitePlace.embedding_of_isReal (completionEmbeddingPlace F E ⟨w, f⟩).2 a =
      (InfinitePlace.Completion.ringEquivRealOfIsReal w.2) (f a) := by
  apply Complex.ofReal_injective
  rw [InfinitePlace.embedding_of_isReal_apply]
  exact DFunLike.congr_fun
    (InfinitePlace.embedding_mk_eq_of_isReal (completionComplexEmbedding_real F E w f)) a

/-- A unit has negative sign at one designated embedding into a real completion
and positive sign at all other embeddings into the real completions. -/
def RealCompletionEmbeddingSignsStatement : Prop :=
  ∀ (F E : Type u) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (w₀ : RealPlaces F) (f₀ : E →ₐ[F] w₀.1.Completion),
    ∃ a : Eˣ, (InfinitePlace.Completion.ringEquivRealOfIsReal w₀.2) (f₀ a) < 0 ∧
      ∀ (w : RealPlaces F) (f : E →ₐ[F] w.1.Completion),
        (⟨w, f⟩ : Σ v : RealPlaces F, E →ₐ[F] v.1.Completion) ≠ ⟨w₀, f₀⟩ →
        0 < (InfinitePlace.Completion.ringEquivRealOfIsReal w.2) (f a)

theorem realCompletionEmbeddingSigns : RealCompletionEmbeddingSignsStatement.{u} := by
  intro F E _ _ _ _ _ w₀ f₀
  let v := completionEmbeddingPlace F E ⟨w₀, f₀⟩
  obtain ⟨a, ha, hneg, hpos⟩ := exists_realPlace_signs E {v}
  refine ⟨Units.mk0 a ha, ?_, fun w f h => ?_⟩
  · change (InfinitePlace.Completion.ringEquivRealOfIsReal w₀.2) (f₀ a) < 0
    rw [← completionEmbeddingPlace_realValue F E w₀ f₀ a]
    exact hneg v (Set.mem_singleton v)
  · change 0 < (InfinitePlace.Completion.ringEquivRealOfIsReal w.2) (f a)
    rw [← completionEmbeddingPlace_realValue F E w f a]
    exact hpos _ (fun hv => h (completionEmbeddingPlace_injective F E (Set.mem_singleton_iff.mp hv)))

end Langlands.Global
