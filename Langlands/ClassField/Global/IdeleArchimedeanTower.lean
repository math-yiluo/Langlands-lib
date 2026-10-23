import Langlands.ClassField.Global.IdeleArchimedean
import Langlands.ClassField.Global.IdeleCohomologyTower
import Langlands.ClassField.Global.ReciprocityTower

/-! # Archimedean idele invariants under inflation -/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField
open Langlands.Global.AdelicFunctoriality Langlands.ClassFieldTheory.Local
open CategoryTheory Reciprocity

universe u

section Coordinate

variable {E L : Type u} [Field E] [Field L]

/-- The real part of the complex value of a completion element is preserved by inclusion. -/
theorem extensionEmbedding_infiniteCompletionMap_re (f : E →+* L) (q : InfinitePlace L)
    (x : (q.comap f).Completion) :
    (InfinitePlace.Completion.extensionEmbedding q (infiniteCompletionMap f q x)).re =
      (InfinitePlace.Completion.extensionEmbedding (q.comap f) x).re := by
  induction x using InfinitePlace.Completion.induction_on with
  | hp =>
    exact isClosed_eq
      (Complex.continuous_re.comp
        ((InfinitePlace.Completion.isometry_extensionEmbedding q).continuous.comp
          (continuous_infiniteCompletionMap f q)))
      (Complex.continuous_re.comp
        (InfinitePlace.Completion.isometry_extensionEmbedding _).continuous)
  | ih a =>
    change (InfinitePlace.Completion.extensionEmbedding q
      (infiniteCompletionMap f q (algebraMap E _ (WithAbs.ofAbs a)))).re = _
    rw [infiniteCompletionMap_coe, extensionEmbedding_algebraMap]
    change _ = (InfinitePlace.Completion.extensionEmbedding (q.comap f)
      (algebraMap E _ (WithAbs.ofAbs a))).re
    rw [extensionEmbedding_algebraMap]
    have hw : q.comap f = InfinitePlace.mk (q.embedding.comp f) := by
      rw [← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
    rw [congrArg InfinitePlace.embedding hw]
    rcases InfinitePlace.embedding_mk_eq (q.embedding.comp f) with h | h
    · rw [h]; rfl
    · rw [h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]; rfl

/-- The sign class of a completion element is preserved by inclusion. -/
theorem signClass_infiniteCompletionMap (f : E →+* L) (q : InfinitePlace L)
    (x : (q.comap f).Completion) :
    signClass (InfinitePlace.Completion.extensionEmbedding q (infiniteCompletionMap f q x)) =
      signClass (InfinitePlace.Completion.extensionEmbedding (q.comap f) x) := by
  unfold signClass
  rw [extensionEmbedding_infiniteCompletionMap_re]

variable [NumberField E] [NumberField L] [Algebra E L]

/-- Inclusion preserves the sign class of an idele coordinate at an infinite place. -/
theorem signClass_ideleInfiniteCoordinate_ideleInclusion (q : InfinitePlace L)
    (a : IdeleGroup (𝓞 E) E) :
    signClass (InfinitePlace.Completion.extensionEmbedding q
        (ideleInfiniteCoordinate q (ideleInclusion a))) =
      signClass (InfinitePlace.Completion.extensionEmbedding (q.comap (algebraMap E L))
        (ideleInfiniteCoordinate (q.comap (algebraMap E L)) a)) :=
  signClass_infiniteCompletionMap (algebraMap E L) q _

end Coordinate

section CocycleValue

variable {F E : Type u} [Field F] [Field E] [NumberField E] [Algebra F E]

/-- The archimedean cocycle invariant may be computed at any nontrivial stabilizer element. -/
theorem archimedeanIdeleCocycleHom_apply_of_mem {w : InfinitePlace E} {c : E ≃ₐ[F] E}
    (hc : c ∈ MulAction.stabilizer (E ≃ₐ[F] E) w) (hc1 : c ≠ 1)
    (f : groupCohomology.cocycles₂ (relativeIdeleRepresentation F E)) :
    archimedeanIdeleCocycleHom F w f =
      signClass (InfinitePlace.Completion.extensionEmbedding w
        (ideleInfiniteCoordinate w (ideleConjugationValue c f))) := by
  have h : ∃ c : E ≃ₐ[F] E, c ∈ MulAction.stabilizer (E ≃ₐ[F] E) w ∧ c ≠ 1 := ⟨c, hc, hc1⟩
  rw [archimedeanIdeleCocycleHom_apply_of_exists h,
    (isConj_of_mem_stabilizer w h.choose_spec.1 h.choose_spec.2).ext
      (isConj_of_mem_stabilizer w hc hc1)]

/-- The archimedean cocycle invariant vanishes at a place with trivial stabilizer. -/
theorem archimedeanIdeleCocycleHom_apply_of_stabilizer_eq_bot {w : InfinitePlace E}
    (hw : MulAction.stabilizer (E ≃ₐ[F] E) w = ⊥)
    (f : groupCohomology.cocycles₂ (relativeIdeleRepresentation F E)) :
    archimedeanIdeleCocycleHom F w f = 0 := by
  refine archimedeanIdeleCocycleHom_apply_of_not_exists ?_ f
  rintro ⟨c, hc, hc1⟩
  rw [hw] at hc
  exact hc1 (Subgroup.mem_bot.1 hc)

end CocycleValue

section CocycleInflation

variable {F E L : Type u} [Field F] [Field E] [Field L]
  [NumberField E] [NumberField L] [Algebra F E] [Algebra E L]
  [Algebra F L] [IsScalarTower F E L] [Normal F E]

/-- The conjugation value of an inflated idele cocycle is the included lower value. -/
theorem ideleConjugationValue_inflation (c : L ≃ₐ[F] L)
    (f : groupCohomology.cocycles₂ (relativeIdeleRepresentation F E)) :
    ideleConjugationValue c (groupCohomology.mapCocycles₂ (AlgEquiv.restrictNormalHom E)
        (ideleInflationCoefficients F E L) f) =
      ideleInclusion (ideleConjugationValue (AlgEquiv.restrictNormalHom E c) f) := by
  have h1 : AlgEquiv.restrictNormalHom (F := F) (K₁ := L) E 1 = 1 := map_one _
  unfold ideleConjugationValue
  rw [groupCohomology.coe_mapCocycles₂]
  change ideleInclusion (@Additive.toMul (IdeleGroup (𝓞 E) E)
      (f (AlgEquiv.restrictNormalHom E c, AlgEquiv.restrictNormalHom E c))) *
    ideleInclusion (@Additive.toMul (IdeleGroup (𝓞 E) E)
      (f (AlgEquiv.restrictNormalHom E 1, AlgEquiv.restrictNormalHom E 1))) = _
  rw [h1, ← map_mul]
  rfl

end CocycleInflation

section Inflation

variable {F E L : Type u} [Field F] [Field E] [Field L]
  [NumberField F] [NumberField E] [NumberField L]
  [Algebra F E] [Algebra E L] [Algebra F L] [IsScalarTower F E L]
  [IsGalois F E] [IsGalois F L]

/-- Inflation preserves the archimedean idele invariant at a place and its restriction. -/
theorem archimedeanIdeleInvariant_relativeIdeleInflation (q : InfinitePlace L)
    (x : relativeIdeleCohomology F E 2) :
    archimedeanIdeleInvariant F q (relativeIdeleInflation F E L 2 x) =
      archimedeanIdeleInvariant F (q.comap (algebraMap E L)) x := by
  obtain ⟨f, rfl⟩ := H2π_surjective x
  rw [groupCohomology.H2π_comp_map_apply,
    archimedeanIdeleInvariant_H2π, archimedeanIdeleInvariant_H2π]
  set ψ := q.embedding.comp (algebraMap E L) with hψ
  have hw : q.comap (algebraMap E L) = InfinitePlace.mk ψ := by
    rw [hψ, ← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
  by_cases h : ∃ c : L ≃ₐ[F] L, c ∈ MulAction.stabilizer (L ≃ₐ[F] L) q ∧ c ≠ 1
  · obtain ⟨c, hcS, hc1⟩ := h
    rw [archimedeanIdeleCocycleHom_apply_of_mem hcS hc1, ideleConjugationValue_inflation]
    have hc := isConj_of_mem_stabilizer q hcS hc1
    have hr := isConj_comp_restrictNormal (E := E) hc
    by_cases hr1 : AlgEquiv.restrictNormalHom E c = 1
    · have hψr : ComplexEmbedding.IsReal ψ :=
        ComplexEmbedding.isConj_one_iff.1 (hr1 ▸ hr)
      have hbot : MulAction.stabilizer (E ≃ₐ[F] E)
          (q.comap (algebraMap E L)) = ⊥ := by
        rw [hw]
        exact InfinitePlace.IsUnramified.stabilizer_eq_bot
          (InfinitePlace.IsReal.isUnramified F (InfinitePlace.isReal_iff.2
            (by rwa [InfinitePlace.embedding_mk_eq_of_isReal hψr])))
      rw [archimedeanIdeleCocycleHom_apply_of_stabilizer_eq_bot hbot, hr1]
      let a := @Additive.toMul (IdeleGroup (𝓞 E) E) (f (1, 1))
      have hval : ideleConjugationValue 1 f = a * a := rfl
      have hfixed : relativeIdeleAut F L c (ideleInclusion a) = ideleInclusion a := by
        rw [← ideleInclusion_relativeIdeleAut F E L, hr1, map_one]
        rfl
      have hstar := extensionEmbedding_ideleInfiniteCoordinate_of_isConj hc (ideleInclusion a)
      rw [hfixed] at hstar
      rw [hval, map_mul, map_mul, Units.val_mul, map_mul]
      nth_rw 1 [hstar]
      exact signClass_star_mul_self _
    · have hrS : AlgEquiv.restrictNormalHom E c ∈
          MulAction.stabilizer (E ≃ₐ[F] E) (q.comap (algebraMap E L)) := by
        rw [hw]
        exact (InfinitePlace.mem_stabilizer_mk_iff ψ _).2 (Or.inr hr)
      rw [signClass_ideleInfiniteCoordinate_ideleInclusion,
        archimedeanIdeleCocycleHom_apply_of_mem hrS hr1]
  · rw [archimedeanIdeleCocycleHom_apply_of_not_exists h]
    have hq : InfinitePlace.IsUnramified F q := by
      rw [InfinitePlace.isUnramified_iff_stabilizer_eq_bot]
      refine (Subgroup.eq_bot_iff_forall _).2 fun c hc => ?_
      by_contra hc1
      exact h ⟨c, hc, hc1⟩
    rw [archimedeanIdeleCocycleHom_apply_of_stabilizer_eq_bot
      (InfinitePlace.IsUnramified.comap E hq).stabilizer_eq_bot]

end Inflation

section Sum

variable {F E : Type u} [Field F] [Field E] [NumberField F] [NumberField E]
  [Algebra F E]

/-- The sum of archimedean idele invariants over chosen places above the base places. -/
def archimedeanIdeleInvariantSum
    (wi : ∀ v : InfinitePlace F, InfinitePlacesAbove E v) :
    relativeIdeleCohomology F E 2 →+ RationalModIntegers :=
  ∑ v, archimedeanIdeleInvariant F (wi v).1

@[simp] theorem archimedeanIdeleInvariantSum_apply
    (wi : ∀ v : InfinitePlace F, InfinitePlacesAbove E v)
    (x : relativeIdeleCohomology F E 2) :
    archimedeanIdeleInvariantSum wi x = ∑ v, archimedeanIdeleInvariant F (wi v).1 x := by
  simp only [archimedeanIdeleInvariantSum, AddMonoidHom.finsetSum_apply]

variable {L : Type u} [Field L] [NumberField L] [Algebra E L] [Algebra F L]
  [IsScalarTower F E L] [IsGalois F E] [IsGalois F L]

/-- The sum of archimedean idele invariants is preserved under inflation at compatible places. -/
theorem archimedeanIdeleInvariantSum_relativeIdeleInflation
    (wi : ∀ v : InfinitePlace F, InfinitePlacesAbove E v)
    (wi' : ∀ v : InfinitePlace F, InfinitePlacesAbove L v)
    (hw : ∀ v, (wi' v).1.comap (algebraMap E L) = (wi v).1)
    (x : relativeIdeleCohomology F E 2) :
    archimedeanIdeleInvariantSum wi' (relativeIdeleInflation F E L 2 x) =
      archimedeanIdeleInvariantSum wi x := by
  simp only [archimedeanIdeleInvariantSum_apply,
    archimedeanIdeleInvariant_relativeIdeleInflation, hw]


end Sum

end Langlands.ClassField.Global
