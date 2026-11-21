import Langlands.Global.Arithmetic.HarrisParityArithmeticTransportStatement
import Langlands.Global.Arithmetic.HarrisDatumArchimedean

/-! # Infinity type and relative regularity under a Hecke norm twist -/

noncomputable section

namespace Langlands.Global.Harris

open NumberField InfinitePlace.Completion AdelicFunctoriality
open scoped NumberField NumberField.LiesOver

universe u

section Local

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [IsTotallyComplex K]

private theorem completion_finrank_one (v : InfinitePlace K) (w : InfinitePlace L)
    [w.LiesOver v] : Module.finrank v.Completion w.Completion = 1 := by
  have hw : w.IsUnramified K := InfinitePlace.isUnramified_iff.mpr (Or.inr (by
    rw [InfinitePlace.LiesOver.comap_eq w v]
    exact IsTotallyComplex.isComplex v))
  exact hw.finrank_eq_one v

private theorem localNorm_completionMap (v : InfinitePlace K) (w : InfinitePlace L)
    [w.LiesOver v] (x : v.Completion) :
    InfiniteExtension.localNorm v w (LiesOver.completionMap x) = x := by
  rw [InfiniteExtension.localNorm_algebraMap, completion_finrank_one v w, pow_one]

private theorem completionMap_localNorm (v : InfinitePlace K) (w : InfinitePlace L)
    [w.LiesOver v] (y : w.Completion) :
    LiesOver.completionMap (InfiniteExtension.localNorm v w y) = y := by
  have hs : Function.Surjective (LiesOver.completionMap (v := v) (w := w)) :=
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp (completion_finrank_one v w)).surjective
  obtain ⟨x, rfl⟩ := hs y
  rw [localNorm_completionMap v w]

end Local

section Infinity

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private def infinityNorm (x : (InfiniteAdeles L)ˣ) : (InfiniteAdeles K)ˣ :=
  Units.map infiniteAdeleNorm x

private theorem normComp_atInfinity (ν : HeckeCharacter K) (x : (InfiniteAdeles L)ˣ) :
    (HeckeCharacter.normComp (L := L) ν).atInfinity x = ν.atInfinity (infinityNorm x) := by
  change ν (ideleClassNorm (K := K) (QuotientGroup.mk (infiniteIdelesInclusion L x))) =
    ν (QuotientGroup.mk (infiniteIdelesInclusion K (infinityNorm x)))
  rw [ideleClassNorm_mk]
  apply congrArg (fun y : Ideles K => ν (QuotientGroup.mk y))
  apply Units.ext
  refine Prod.ext rfl ?_
  change finiteAdeleNorm (K := K) (L := L) 1 = 1
  exact map_one _

private def localNormCoordinate (v : InfinitePlace K) (w : InfinitePlace L) [w.LiesOver v]
    (x : (InfiniteAdeles L)ˣ) : ℂˣ :=
  Units.map (extensionEmbedding v).toMonoidHom
    (InfiniteExtension.localUnitNorm v w
      (Units.map (Pi.evalRingHom (fun p : InfinitePlace L => p.Completion) w).toMonoidHom x))

omit [NumberField K] in
private theorem coordinate_infinityNorm (v : InfinitePlace K) (x : (InfiniteAdeles L)ˣ) :
    InfinityType.coordinate v (infinityNorm x) =
      ∏ w : InfinitePlacesAbove L v, localNormCoordinate v w.1 x := by
  apply Units.ext
  rw [Units.coe_prod]
  change extensionEmbedding v (∏ w : InfinitePlacesAbove L v,
    InfiniteExtension.localNorm v w.1 (x.val w.1)) =
    ∏ w : InfinitePlacesAbove L v, extensionEmbedding v (InfiniteExtension.localNorm v w.1 (x.val w.1))
  exact map_prod (extensionEmbedding v) _ _

private theorem prod_placesAbove {M : Type*} [CommMonoid M] (f : InfinitePlace L → M) :
    (∏ v : InfinitePlace K, ∏ w : InfinitePlacesAbove L v, f w.1) = ∏ w, f w := by
  classical
  rw [← Fintype.prod_fiberwise (fun w : InfinitePlace L => w.comap (algebraMap K L)) f]
  refine Finset.prod_congr rfl fun v _ => ?_
  have h (w : InfinitePlace L) : w.LiesOver v ↔ w.comap (algebraMap K L) = v := by
    constructor
    · intro hw
      exact InfinitePlace.LiesOver.comap_eq w v
    · intro hw
      subst v
      exact ⟨rfl⟩
  exact Fintype.prod_equiv (Equiv.subtypeEquivRight h) _ _ (fun _ => rfl)

variable [IsTotallyComplex K]

omit [NumberField K] [NumberField L] in
private theorem coordinate_orientation (v : InfinitePlace K) (w : InfinitePlace L)
    [w.LiesOver v] (x : (InfiniteAdeles L)ˣ) :
    (w.embedding.comp (algebraMap K L) = v.embedding ∧
      InfinityType.coordinate w x = localNormCoordinate v w x) ∨
    ((ComplexEmbedding.conjugate w.embedding).comp (algebraMap K L) = v.embedding ∧
      InfinityType.coordinate w x = star (localNormCoordinate v w x)) := by
  let y := InfiniteExtension.localNorm v w (x.val w)
  have hy : LiesOver.completionMap y = x.val w := completionMap_localNorm v w _
  by_cases h : w.embedding.comp (algebraMap K L) = v.embedding
  · refine Or.inl ⟨h, Units.ext ?_⟩
    change extensionEmbedding w (x.val w) = extensionEmbedding v y
    exact (congrArg (extensionEmbedding w) hy).symm.trans
      (HarrisDatum.extensionEmbedding_completionMap_of_eq v w h y)
  · refine Or.inr ⟨(InfinitePlace.LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq
      w v).resolve_left h, Units.ext ?_⟩
    change extensionEmbedding w (x.val w) = star (extensionEmbedding v y)
    exact (congrArg (extensionEmbedding w) hy).symm.trans
      (HarrisDatum.extensionEmbedding_completionMap_of_ne v w h y)

private theorem moduli_infinityNorm (b : ℕ) (x : (InfiniteAdeles L)ˣ) :
    (∏ v : InfinitePlace K, ((‖(InfinityType.coordinate v (infinityNorm x) : ℂ)‖ : ℝ) : ℂ) ^ b) =
      ∏ w : InfinitePlace L, ((‖(InfinityType.coordinate w x : ℂ)‖ : ℝ) : ℂ) ^ b := by
  let upper (w : InfinitePlace L) : ℂ := ((‖(InfinityType.coordinate w x : ℂ)‖ : ℝ) : ℂ) ^ b
  change _ = ∏ w, upper w
  rw [← prod_placesAbove (K := K) upper]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [coordinate_infinityNorm, Units.coe_prod, _root_.norm_prod, Complex.ofReal_prod,
    ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun w _ => ?_
  dsimp only [upper]
  rcases coordinate_orientation v w.1 x with ⟨_, h⟩ | ⟨_, h⟩
  · rw [h]
  · rw [h, Units.coe_star, Complex.star_def, Complex.norm_conj]

private theorem toCharacter_infinityNorm [IsTotallyComplex L]
    (t : InfinityType K) (x : (InfiniteAdeles L)ˣ) :
    InfinityType.toCharacter t (infinityNorm x) =
      InfinityType.toCharacter (fun σ => t (σ.comp (algebraMap K L))) x := by
  let s : InfinityType L := fun σ => t (σ.comp (algebraMap K L))
  let upper (w : InfinitePlace L) : ℂˣ :=
    InfinityType.complexCharacter (s w.embedding) (s (ComplexEmbedding.conjugate w.embedding))
      (InfinityType.coordinate w x)
  change (∏ v : InfinitePlace K,
      InfinityType.complexCharacter (t v.embedding) (t (ComplexEmbedding.conjugate v.embedding))
        (InfinityType.coordinate v (infinityNorm x))) = ∏ w, upper w
  rw [← prod_placesAbove (K := K) upper]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [coordinate_infinityNorm, map_prod]
  refine Finset.prod_congr rfl fun w _ => ?_
  dsimp only [upper, s]
  rcases coordinate_orientation v w.1 x with ⟨he, hz⟩ | ⟨he, hz⟩
  · rw [hz, HarrisDatum.conjugate_comp, he]
  · have hc : w.1.embedding.comp (algebraMap K L) = ComplexEmbedding.conjugate v.embedding := by
      rw [← he, ← HarrisDatum.conjugate_comp, ComplexEmbedding.involutive_conjugate]
    rw [hz, he, hc, InfinityType.complexCharacter_conjugate]

private theorem normComp_infiniteComponent_completionMap (ν : HeckeCharacter K)
    (v : InfinitePlace K) (w : InfinitePlace L) [w.LiesOver v] (x : v.Completionˣ) :
    (HeckeCharacter.normComp (L := L) ν).infiniteComponent w
      (Units.map (LiesOver.completionMap (v := v) (w := w)).toMonoidHom x) =
      ν.infiniteComponent v x := by
  let y := Units.map (LiesOver.completionMap (v := v) (w := w)).toMonoidHom x
  change ν (ideleClassNorm (K := K) (IdeleClassGroup.ofCompletion (𝓞 L) L w y)) =
    ν (IdeleClassGroup.ofCompletion (𝓞 K) K v x)
  rw [ideleClassNorm_ofCompletion v (⟨w, inferInstance⟩ : InfinitePlacesAbove L v) y]
  have hy : InfiniteExtension.localUnitNorm v w y = x :=
    Units.ext (localNorm_completionMap v w x.val)
  rw [hy]

end Infinity

/-- A Hecke norm twist adds the restricted infinity type and preserves relative regularity. -/
theorem normTwistInfinity : NormTwistInfinityStatement.{u} := by
  intro K L _ _ _ _ _ _ _ ξ ν a b
  constructor
  · rintro ⟨s, hs⟩ ⟨t, ht⟩
    refine ⟨s + (fun σ => t (σ.comp (algebraMap K L))), fun x => ?_⟩
    have ht' := ht (infinityNorm x)
    rw [← normComp_atInfinity, moduli_infinityNorm, toCharacter_infinityNorm] at ht'
    have hmul : ((ξ * HeckeCharacter.normComp (L := L) ν).atInfinity x : ℂ) =
        (ξ.atInfinity x : ℂ) * ((HeckeCharacter.normComp (L := L) ν).atInfinity x : ℂ) := rfl
    simp only [hmul, pow_add, Finset.prod_mul_distrib, toCharacter_add, Units.val_mul]
    rw [mul_mul_mul_comm, hs x, ht']
  · intro hreg v w w' _ _ hne
    obtain ⟨x, hx⟩ := hreg v w w' hne
    refine ⟨x, fun heq => hx ?_⟩
    simp only [HeckeCharacter.infiniteComponent_mul, ContinuousMonoidHom.mul_apply,
      normComp_infiniteComponent_completionMap] at heq
    exact mul_right_cancel heq

end Langlands.Global.Harris
