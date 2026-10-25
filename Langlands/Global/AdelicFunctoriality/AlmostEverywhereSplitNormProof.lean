import Langlands.Global.AdelicFunctoriality.AlmostEverywhereSplitNormStatement
import Langlands.Global.AdelicFunctoriality.IdeleNormLift
import Langlands.ClassField.Global.IdeleArchimedean
import Langlands.Global.AdelicFunctoriality.MixedWeakApproximation
import Langlands.Global.AdelicFunctoriality.LocalNormNeighborhood

/-! # Surjectivity of idele-class norms for almost-everywhere split extensions -/

noncomputable section

namespace Langlands.Global.AdelicFunctoriality

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter
open Langlands.ClassField.Global
open scoped NumberField FiniteExtension

universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]

/-- At completed degree one the scalar inclusion is a section of the norm on units. -/
theorem localNorm_units_completionMap_of_finrank_eq_one
    (p : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    [q.asIdeal.LiesOver p.asIdeal]
    (h : Module.finrank (p.adicCompletion K) (q.adicCompletion L) = 1)
    (x : (p.adicCompletion K)ˣ) :
    Units.map (FiniteExtension.localNorm p q)
      (Units.map (FiniteExtension.completionMap p q).toMonoidHom x) = x := by
  apply Units.ext
  change FiniteExtension.localNorm p q (FiniteExtension.completionMap p q x) = x
  rw [FiniteExtension.localNorm_algebraMap, h, pow_one]

/-- Scalar inclusion preserves integral local units, including their inverses. -/
theorem completionMap_unit_integral
    (p : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    [q.asIdeal.LiesOver p.asIdeal] (x : (p.adicCompletion K)ˣ)
    (hx : (x : p.adicCompletion K) ∈ p.adicCompletionIntegers K)
    (hxi : ((x⁻¹ : (p.adicCompletion K)ˣ) : p.adicCompletion K) ∈
      p.adicCompletionIntegers K) :
    let y := Units.map (FiniteExtension.completionMap p q).toMonoidHom x
    (y : q.adicCompletion L) ∈ q.adicCompletionIntegers L ∧
      ((y⁻¹ : (q.adicCompletion L)ˣ) : q.adicCompletion L) ∈
        q.adicCompletionIntegers L := by
  constructor
  · exact (FiniteExtension.completionMap_mem_integers_iff p q _).2 hx
  · exact (FiniteExtension.completionMap_mem_integers_iff p q _).2 hxi

/-- Local norm preimages at the exceptional places suffice once the other finite
completed extensions have degree one. -/
theorem mem_range_ideleNorm_of_split_and_local
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (wf : ∀ p : HeightOneSpectrum (𝓞 K), FinitePlacesAbove L p)
    (wi : ∀ p : InfinitePlace K, InfinitePlacesAbove L p)
    (hsplit : ∀ p, p ∉ S →
      Module.finrank (p.adicCompletion K) ((wf p).1.adicCompletion L) = 1)
    (a : IdeleGroup (𝓞 K) K)
    (hf : ∀ p, p ∈ S → ideleCoordinate p a ∈
      Set.range (Units.map (FiniteExtension.localNorm p (wf p).1)))
    (hi : ∀ p, ideleInfiniteCoordinate p a ∈
      Set.range (Units.map (InfiniteExtension.localNorm p (wi p).1))) :
    a ∈ (ideleNorm (K := K) (L := L)).toMonoidHom.range := by
  classical
  let c : ∀ p : HeightOneSpectrum (𝓞 K), ((wf p).1.adicCompletion L)ˣ := fun p =>
    if h : p ∈ S then Classical.choose (hf p h)
    else Units.map (FiniteExtension.completionMap p (wf p).1).toMonoidHom
      (ideleCoordinate p a)
  have hcn : ∀ p, FiniteExtension.localNorm p (wf p).1 (c p) =
      (a : AdeleRing (𝓞 K) K).2 p := by
    intro p
    by_cases h : p ∈ S
    · have heq : Units.map (FiniteExtension.localNorm p (wf p).1) (c p) =
          ideleCoordinate p a := by
        simpa only [c, dite_eq_left h] using Classical.choose_spec (hf p h)
      exact congrArg Units.val heq
    · have heq : Units.map (FiniteExtension.localNorm p (wf p).1) (c p) =
          ideleCoordinate p a := by
        simpa only [c, dite_eq_right h] using
          localNorm_units_completionMap_of_finrank_eq_one p (wf p).1
            (hsplit p h) (ideleCoordinate p a)
      exact congrArg Units.val heq
  have hc : ∀ᶠ p in cofinite,
      (c p : (wf p).1.adicCompletion L) ∈ (wf p).1.adicCompletionIntegers L ∧
        ((c p)⁻¹ : ((wf p).1.adicCompletion L)ˣ).val ∈
          (wf p).1.adicCompletionIntegers L := by
    filter_upwards [S.finite_toSet.compl_mem_cofinite,
      (a : AdeleRing (𝓞 K) K).2.property,
      ((a⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K).2.property] with p hp hx hxi
    rw [show c p = Units.map (FiniteExtension.completionMap p (wf p).1).toMonoidHom
      (ideleCoordinate p a) from dite_eq_right hp]
    exact completionMap_unit_integral p (wf p).1 (ideleCoordinate p a) hx hxi
  let d : ∀ p : InfinitePlace K, ((wi p).1.Completion)ˣ :=
    fun p => Classical.choose (hi p)
  have hdn : ∀ p, InfiniteExtension.localNorm p (wi p).1 (d p) =
      (a : AdeleRing (𝓞 K) K).1 p := fun p =>
    congrArg Units.val (Classical.choose_spec (hi p))
  exact mem_range_ideleNorm_of_local wf wi a c hc hcn d hdn

/-- A norm representative after multiplying by a principal idele suffices on classes. -/
theorem surjective_ideleClassNorm_of_principal_adjustment
    (h : ∀ a : IdeleGroup (𝓞 K) K, ∃ α : Kˣ,
      (IdeleGroup.unitEmbedding (𝓞 K) K α)⁻¹ * a ∈
        (ideleNorm (K := K) (L := L)).toMonoidHom.range) :
    Function.Surjective (ideleClassNorm (K := K) (L := L)) := by
  intro x
  induction x using QuotientGroup.induction_on with
  | H a =>
    obtain ⟨α, b, hb⟩ := h a
    change ideleNorm (K := K) (L := L) b =
      (IdeleGroup.unitEmbedding (𝓞 K) K α)⁻¹ * a at hb
    refine ⟨QuotientGroup.mk b, ?_⟩
    rw [ideleClassNorm_mk]
    change QuotientGroup.mk (ideleNorm (K := K) (L := L) b) = QuotientGroup.mk a
    rw [hb, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have hα : (QuotientGroup.mk (IdeleGroup.unitEmbedding (𝓞 K) K α) :
        IdeleClassGroup (𝓞 K) K) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨α, rfl⟩
    rw [hα, inv_one]
    exact one_mul (QuotientGroup.mk a : IdeleClassGroup (𝓞 K) K)

/-- Every infinite place has an upper place for an arbitrary number-field extension. -/
theorem exists_infinitePlace_above (p : InfinitePlace K) :
    Nonempty (InfinitePlacesAbove L p) := by
  obtain ⟨q, hq⟩ := InfinitePlace.comap_surjective (K := L) p
  refine ⟨⟨q, ?_⟩⟩
  subst p
  exact ⟨rfl⟩

/-- The remaining arithmetic input to the split norm proof is the simultaneous
principal adjustment at the exceptional finite places and all infinite places. -/
theorem surjective_ideleClassNorm_of_split_and_adjustment
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (wf : ∀ p : HeightOneSpectrum (𝓞 K), FinitePlacesAbove L p)
    (wi : ∀ p : InfinitePlace K, InfinitePlacesAbove L p)
    (hsplit : ∀ p, p ∉ S →
      Module.finrank (p.adicCompletion K) ((wf p).1.adicCompletion L) = 1)
    (hadjust : ∀ a : IdeleGroup (𝓞 K) K, ∃ α : Kˣ,
      (∀ p, p ∈ S →
        ideleCoordinate p ((IdeleGroup.unitEmbedding (𝓞 K) K α)⁻¹ * a) ∈
          Set.range (Units.map (FiniteExtension.localNorm p (wf p).1))) ∧
      (∀ p, ideleInfiniteCoordinate p ((IdeleGroup.unitEmbedding (𝓞 K) K α)⁻¹ * a) ∈
        Set.range (Units.map (InfiniteExtension.localNorm p (wi p).1)))) :
    Function.Surjective (ideleClassNorm (K := K) (L := L)) := by
  apply surjective_ideleClassNorm_of_principal_adjustment
  intro a
  obtain ⟨α, hf, hi⟩ := hadjust a
  exact ⟨α, mem_range_ideleNorm_of_split_and_local S wf wi hsplit _ hf hi⟩

/-- The exact almost-everywhere split norm statement, at independent universes. -/
theorem almostEverywhereSplitIdeleClassNormSurjective :
    AlmostEverywhereSplitIdeleClassNormSurjective.{u, v} := by
  intro F _ _ E _ _ _ _ _ S hsplit
  classical
  let wf : ∀ p : HeightOneSpectrum (𝓞 F), FinitePlacesAbove E p := placeAbove E
  let wi : ∀ p : InfinitePlace F, InfinitePlacesAbove E p :=
    fun p => Classical.choice (exists_infinitePlace_above (L := E) p)
  apply surjective_ideleClassNorm_of_split_and_adjustment S wf wi
  · intro p hp
    exact hsplit p hp (wf p).1 (wf p).2
  · intro a
    exact exists_principal_inv_mul_mem S a
      (fun p => Set.range (Units.map (FiniteExtension.localNorm p (wf p).1)))
      (fun p _ => range_finiteLocalNorm_mem_nhds p (wf p).1)
      (fun p => Set.range (Units.map (InfiniteExtension.localNorm p (wi p).1)))
      (fun p => range_infiniteLocalNorm_mem_nhds p (wi p).1)

end Langlands.Global.AdelicFunctoriality
