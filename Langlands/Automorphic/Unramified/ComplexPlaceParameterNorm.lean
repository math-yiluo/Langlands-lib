import Langlands.Automorphic.Unramified.ComplexPlaceParameterTransport
import Langlands.Automorphic.IsobaricComplexPlaceParameter
import Langlands.Global.AdelicFunctoriality.IdeleClassNorm

/-!
# Complex-place parameters of norm pullbacks

For number fields `K ⊆ L`, a complex place `v` of `K` and a place `w` of `L` above it, the
local norm `L_w → K_v` is, in the selected coordinates, the identity when the embedding of
`w` restricts to that of `v`, and complex conjugation otherwise. Hence if the Hecke character
`μ` of `K` has the parameter `d` at `v`, then `μ ∘ N_{L/K}` has the parameter `d` at `w` in
the first case and the conjugate parameter `d̄` in the second. Lemmas on multiplying and
conjugating character data are included.
-/

noncomputable section

universe uK uL

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.LocalFactor.Archimedean
open scoped NumberField.LiesOver

/-! ## Character data -/

namespace ComplexCharacterDataLemmas

/-- Character data with the same character, weight and exponent are equal. -/
theorem ext {d e : ComplexCharacterData} (hc : d.character = e.character)
    (hw : d.weight = e.weight) (he : d.exponent = e.exponent) : d = e := by
  cases d
  cases e
  simp only at hc hw he
  subst hc hw he
  rfl

theorem complexConjugation_complexConjugation (z : Weil.Archimedean.ComplexWeil) :
    complexConjugation (complexConjugation z) = z := by
  apply Units.ext
  change star (star (z : ℂ)) = (z : ℂ)
  exact star_star _

/-- Conjugation of character data is an involution. -/
theorem conj_conj (d : ComplexCharacterData) : d.conj.conj = d := by
  refine ext ?_ (neg_neg _) rfl
  ext z
  change (d.character (complexConjugation (complexConjugation z)) : ℂ) = (d.character z : ℂ)
  rw [complexConjugation_complexConjugation]

/-- Conjugation commutes with products of character data. -/
theorem conj_mul (d e : ComplexCharacterData) : (d.mul e).conj = d.conj.mul e.conj := by
  refine ext ?_ (neg_add _ _) rfl
  ext z
  rfl

end ComplexCharacterDataLemmas

/-! ## The local norm at a complex place -/

variable {K : Type uK} {L : Type uL} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

omit [NumberField K] in
/-- When the embedding of `w` restricts to that of `v`, the completion map is the identity in
the selected coordinates. -/
theorem extensionEmbedding_completionMap_of_comp_eq (v : NumberField.InfinitePlace K)
    (w : InfinitePlacesAbove L v) (h : w.1.embedding.comp (algebraMap K L) = v.embedding)
    (y : v.Completion) :
    extensionEmbedding w.1 (NumberField.LiesOver.completionMap y) = extensionEmbedding v y := by
  have : ComplexEmbedding.LiesOver w.1.embedding v.embedding := ⟨h⟩
  have := liesOver_extensionEmbedding w.1 v
  exact liesOver_extensionEmbedding_apply w.1 v (φ := extensionEmbedding w.1) (x := y)

omit [NumberField K] in
/-- Otherwise the completion map is complex conjugation in the selected coordinates. -/
theorem extensionEmbedding_completionMap_of_comp_ne (v : NumberField.InfinitePlace K)
    (w : InfinitePlacesAbove L v) (h : ¬ w.1.embedding.comp (algebraMap K L) = v.embedding)
    (y : v.Completion) :
    extensionEmbedding w.1 (NumberField.LiesOver.completionMap y) =
      starRingEnd ℂ (extensionEmbedding v y) := by
  have hc : (ComplexEmbedding.conjugate w.1.embedding).comp (algebraMap K L) = v.embedding :=
    (NumberField.InfinitePlace.LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq
      w.1 v).resolve_left h
  have : ComplexEmbedding.LiesOver (ComplexEmbedding.conjugate w.1.embedding) v.embedding := ⟨hc⟩
  have := liesOver_conjugate_extensionEmbedding w.1 v
  have h1 := liesOver_extensionEmbedding_apply w.1 v
    (φ := ComplexEmbedding.conjugate (extensionEmbedding w.1)) (x := y)
  rw [← h1]
  change _ = starRingEnd ℂ (starRingEnd ℂ (extensionEmbedding w.1 _))
  rw [Complex.conj_conj]
  rfl

omit [NumberField K] in
/-- A place above a complex place is unramified. -/
theorem isUnramified_of_isComplex (v : NumberField.InfinitePlace K) (hv : v.IsComplex)
    (w : InfinitePlacesAbove L v) : w.1.IsUnramified K := by
  change mult (w.1.comap (algebraMap K L)) = mult w.1
  rw [NumberField.InfinitePlace.LiesOver.comap_eq w.1 v, mult_isComplex ⟨v, hv⟩,
    mult_isComplex ⟨w.1, NumberField.InfinitePlace.LiesOver.isComplex_of_isComplex_under w.1 hv⟩]

omit [NumberField K] in
open Classical in
/-- In the selected coordinates, the local norm from a place `w` above a complex place `v` is
the identity when the embedding of `w` restricts to that of `v`, and complex conjugation
otherwise. -/
theorem extensionEmbedding_localNorm (v : NumberField.InfinitePlace K) (hv : v.IsComplex)
    (w : InfinitePlacesAbove L v) (x : w.1.Completion) :
    extensionEmbedding v (InfiniteExtension.localNorm v w.1 x) =
      if w.1.embedding.comp (algebraMap K L) = v.embedding then extensionEmbedding w.1 x
      else starRingEnd ℂ (extensionEmbedding w.1 x) := by
  have hdeg : Module.finrank v.Completion w.1.Completion = 1 :=
    (isUnramified_of_isComplex v hv w).finrank_eq_one v
  let e := ringEquivComplexOfIsComplex hv
  split_ifs with h
  · set y := e.symm (extensionEmbedding w.1 x) with hydef
    have hy : NumberField.LiesOver.completionMap y = x := by
      apply (isometry_extensionEmbedding w.1).injective
      rw [extensionEmbedding_completionMap_of_comp_eq v w h]
      exact e.apply_symm_apply _
    rw [← hy, InfiniteExtension.localNorm_algebraMap, hdeg, pow_one,
      extensionEmbedding_completionMap_of_comp_eq v w h]
  · set y := e.symm (starRingEnd ℂ (extensionEmbedding w.1 x)) with hydef
    have hey : extensionEmbedding v y = starRingEnd ℂ (extensionEmbedding w.1 x) :=
      e.apply_symm_apply _
    have hy : NumberField.LiesOver.completionMap y = x := by
      apply (isometry_extensionEmbedding w.1).injective
      rw [extensionEmbedding_completionMap_of_comp_ne v w h, hey, Complex.conj_conj]
    rw [← hy, InfiniteExtension.localNorm_algebraMap, hdeg, pow_one, hey, hy]

/-! ## The idele norm on a single infinite place -/

/-- The norm of the idele equal to `x` at the place `w` above `v`, and to `1` elsewhere, is the
idele equal to the local norm of `x` at `v` and to `1` elsewhere. -/
theorem ideleNorm_infiniteIdeleInclusion (v : NumberField.InfinitePlace K)
    (w : InfinitePlacesAbove L v) (x : (InfiniteCompletion L w.1)ˣ) :
    ideleNorm (K := K) (infiniteIdeleInclusion L w.1 x) =
      infiniteIdeleInclusion K v (InfiniteExtension.localUnitNorm v w.1 x) := by
  classical
  apply Units.ext
  rw [ideleNorm_val]
  change (infiniteAdeleNorm (K := K) (InfiniteAdeleRing.ofCompletion w.1 (x : w.1.Completion)),
      finiteAdeleNorm (K := K) (L := L) 1) =
    (InfiniteAdeleRing.ofCompletion v (InfiniteExtension.localNorm v w.1 (x : w.1.Completion)), 1)
  refine Prod.ext ?_ (map_one _)
  funext p
  change ∏ q : InfinitePlacesAbove L p, InfiniteExtension.localNorm p q.1
      (InfiniteAdeleRing.ofCompletion w.1 (x : w.1.Completion) q.1) =
    InfiniteAdeleRing.ofCompletion v (InfiniteExtension.localNorm v w.1 (x : w.1.Completion)) p
  by_cases hp : p = v
  · subst hp
    rw [Finset.prod_eq_single w]
    · rw [InfiniteAdeleRing.ofCompletion_apply, InfiniteAdeleRing.ofCompletion_apply,
        Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
    · intro q _ hq
      have hq' : q.1 ≠ w.1 := fun h => hq (Subtype.ext h)
      rw [InfiniteAdeleRing.ofCompletion_apply, Pi.mulSingle_eq_of_ne hq', map_one]
    · intro h
      exact absurd (Finset.mem_univ w) h
  · rw [InfiniteAdeleRing.ofCompletion_apply, Pi.mulSingle_eq_of_ne hp]
    refine Finset.prod_eq_one fun q _ => ?_
    have hq' : q.1 ≠ w.1 := by
      intro h
      apply hp
      have h1 := NumberField.InfinitePlace.LiesOver.comap_eq q.1 p
      have h2 := NumberField.InfinitePlace.LiesOver.comap_eq w.1 v
      rw [← h1, ← h2]
      exact congrArg (fun u : NumberField.InfinitePlace L => u.comap (algebraMap K L)) h
    rw [InfiniteAdeleRing.ofCompletion_apply, Pi.mulSingle_eq_of_ne hq', map_one]

/-! ## Parameters of norm pullbacks -/

open Classical in
/-- The parameter at a place `w` above the complex place `v` of the norm pullback of a
character with parameter `e` at `v`, in the coordinates of `w`: `e` itself when the embedding
of `w` restricts to that of `v`, and `ē` otherwise. -/
def normParameter (v : {v : NumberField.InfinitePlace K // v.IsComplex})
    (w : InfinitePlacesAbove L v.1) (e : ComplexCharacterData) : ComplexCharacterData :=
  if w.1.embedding.comp (algebraMap K L) = v.1.embedding then e else e.conj

/-- If `μ` has the parameter `d` at the complex place `v`, then `μ ∘ N_{L/K}` has at a place
`w` above `v` the parameter `d` when the embedding of `w` restricts to that of `v`, and `d̄`
otherwise. -/
theorem hasComplexPlaceParameter_comp_ideleClassNorm {μ : HeckeCharacter K}
    {v : {v : NumberField.InfinitePlace K // v.IsComplex}} {d : ComplexCharacterData}
    (hμ : μ.HasComplexPlaceParameter v d) (w : InfinitePlacesAbove L v.1) :
    HeckeCharacter.HasComplexPlaceParameter (μ.comp (ideleClassNorm (K := K) (L := L)))
      (complexPlaceAbove v w) (normParameter v w d) := by
  intro x
  unfold normParameter
  change μ (ideleClassNorm (K := K) (QuotientGroup.mk (infiniteIdeleInclusion L w.1 x))) = _
  rw [ideleClassNorm_mk, ideleNorm_infiniteIdeleInclusion v.1 w x]
  change μ.infiniteComponent v.1 (InfiniteExtension.localUnitNorm v.1 w.1 x) = _
  rw [hμ]
  have hloc := extensionEmbedding_localNorm v.1 v.2 w (show w.1.Completion from x.val)
  split_ifs with h
  · simp only [h, ↓reduceIte] at hloc
    congr 1
    apply Units.ext
    exact hloc
  · simp only [h, ↓reduceIte] at hloc
    change _ = d.character (complexConjugation _)
    congr 1
    apply Units.ext
    rw [coe_complexConjugation]
    exact hloc

/-! ## Multiplying induced parameter lists -/

/-- Multiplying a transported singleton by `e` is transporting the singleton multiplied by the
norm parameter of `e`. -/
theorem complexPlaceParameterTransport_map_mul
    (v : {v : NumberField.InfinitePlace K // v.IsComplex}) (w : InfinitePlacesAbove L v.1)
    (a e : ComplexCharacterData) :
    (complexPlaceParameterTransport v w [a]).map (fun d => d.mul e) =
      complexPlaceParameterTransport v w [a.mul (normParameter v w e)] := by
  classical
  by_cases h : w.1.embedding.comp (algebraMap K L) = v.1.embedding
  · simp only [complexPlaceParameterTransport, normParameter, h, ↓reduceIte, List.map_cons,
      List.map_nil]
  · simp only [complexPlaceParameterTransport, normParameter, h, ↓reduceIte, List.map_cons,
      List.map_nil, ComplexCharacterDataLemmas.conj_mul, ComplexCharacterDataLemmas.conj_conj]

/-- Multiplying the Langlands sum of singletons by `e` multiplies each singleton by the norm
parameter of `e`. -/
theorem complexPlaceLanglandsSum_map_mul (v : {v : NumberField.InfinitePlace K // v.IsComplex})
    {d : ℕ} (en : Fin d ≃ InfinitePlacesAbove L v.1)
    (a : InfinitePlacesAbove L v.1 → ComplexCharacterData) (e : ComplexCharacterData) :
    (complexPlaceLanglandsSum v en fun w => [a w]).map (fun c => c.mul e) =
      complexPlaceLanglandsSum v en fun w => [(a w).mul (normParameter v w e)] := by
  simp only [complexPlaceLanglandsSum, List.map_flatten, List.map_ofFn]
  congr 1
  congr 1
  funext i
  exact complexPlaceParameterTransport_map_mul v (en i) (a (en i)) e

end Langlands.Automorphic.Unramified
