import Langlands.Global.Arithmetic.HarrisParityArithmeticTransportStatement
import Langlands.Global.Arithmetic.HarrisDatumCharacterRealizationProof

/-! # The idele-class norm commutes with arithmetic CM conjugation -/

noncomputable section

universe u v

namespace Langlands.Global.Harris

open NumberField AdelicFunctoriality
open scoped NumberField FiniteExtension NumberField.LiesOver

private abbrev cmConj (K : Type*) [Field K] [NumberField K] [IsCMField K] : K ≃+* K :=
  (IsCMField.complexConj K).toRingEquiv

private theorem finitePlaceConj_involutive (K : Type*) [Field K] [NumberField K] [IsCMField K] :
    Function.Involutive (finitePlaceEquiv (cmConj K)) := by
  have h : (cmConj K).trans (cmConj K) = RingEquiv.refl K := by
    ext x
    exact IsCMField.complexConj_apply_apply K x
  intro p
  have hp := congrArg (fun e : FinitePlace K ≃ FinitePlace K => e p)
    (finitePlaceEquiv_trans (cmConj K) (cmConj K))
  rw [h, finitePlaceEquiv_refl] at hp
  exact hp.symm

section

variable {E : Type u} {E' : Type v} [Field E] [NumberField E] [IsCMField E]
  [Field E'] [NumberField E'] [IsCMField E'] [Algebra E E']

private def finitePlacesAboveConj (p : FinitePlace E) :
    FinitePlacesAbove E' p ≃ FinitePlacesAbove E' (finitePlaceEquiv (cmConj E) p) :=
  (finitePlaceEquiv (cmConj E')).subtypeEquiv fun q => by
    change q.asIdeal.LiesOver p.asIdeal ↔
      (finitePlaceEquiv (cmConj E') q).asIdeal.LiesOver (finitePlaceEquiv (cmConj E) p).asIdeal
    constructor
    · intro h
      exact HarrisDatum.conjPlace_liesOver p q
    · intro h
      have h' := HarrisDatum.conjPlace_liesOver (finitePlaceEquiv (cmConj E) p)
        (finitePlaceEquiv (cmConj E') q)
      change ((finitePlaceEquiv (cmConj E')) ((finitePlaceEquiv (cmConj E')) q)).asIdeal.LiesOver
        ((finitePlaceEquiv (cmConj E)) ((finitePlaceEquiv (cmConj E)) p)).asIdeal at h'
      rw [finitePlaceConj_involutive E' q, finitePlaceConj_involutive E p] at h'
      exact h'

private theorem finiteLocalNorm_conj (p : FinitePlace E) (q : FinitePlace E')
    [q.asIdeal.LiesOver p.asIdeal]
    [(finitePlaceEquiv (cmConj E') q).asIdeal.LiesOver (finitePlaceEquiv (cmConj E) p).asIdeal]
    (x : (finitePlaceEquiv (cmConj E') q).adicCompletion E') :
    FiniteExtension.localNorm p q (finiteCompletionEquiv (cmConj E') q x) =
      finiteCompletionEquiv (cmConj E) p
        (FiniteExtension.localNorm (finitePlaceEquiv (cmConj E) p)
          (finitePlaceEquiv (cmConj E') q) x) := by
  let p' := finitePlaceEquiv (cmConj E) p
  let q' := finitePlaceEquiv (cmConj E') q
  have hcomm (z : p'.adicCompletion E) :
      FiniteExtension.completionMap p q (finiteCompletionEquiv (cmConj E) p z) =
        finiteCompletionEquiv (cmConj E') q (FiniteExtension.completionMap p' q' z) := by
    apply congrFun ((p'.denseRange_algebraMap E).equalizer
      ((FiniteExtension.continuous_completionMap p q).comp
        (continuous_finiteCompletionEquiv (cmConj E) p))
      ((continuous_finiteCompletionEquiv (cmConj E') q).comp
        (FiniteExtension.continuous_completionMap p' q')) ?_) z
    funext a
    dsimp only [p', q']
    simp only [Function.comp_apply, FiniteExtension.completionMap_coe, finiteCompletionEquiv_coe]
    exact congrArg (algebraMap E' (q.adicCompletion E'))
      (HarrisDatum.complexConj_algebraMap a).symm
  change Algebra.norm (p.adicCompletion E) (finiteCompletionEquiv (cmConj E') q x) =
    finiteCompletionEquiv (cmConj E) p (Algebra.norm (p'.adicCompletion E) x)
  rw [Algebra.norm_eq_of_equiv_equiv (finiteCompletionEquiv (cmConj E) p)
    (finiteCompletionEquiv (cmConj E') q) (RingHom.ext hcomm) x, RingEquiv.apply_symm_apply]

private def infinitePlacesAboveConj (p : InfinitePlace E) :
    InfinitePlacesAbove E' p ≃ InfinitePlacesAbove E' (infinitePlaceEquiv (cmConj E) p) :=
  (infinitePlaceEquiv (cmConj E')).subtypeEquiv fun q => by
    change q.LiesOver p ↔
      (infinitePlaceEquiv (cmConj E') q).LiesOver (infinitePlaceEquiv (cmConj E) p)
    rw [infinitePlaceEquiv_complexConj, infinitePlaceEquiv_complexConj]

omit [NumberField E] [NumberField E'] [IsCMField E] [IsCMField E'] in
private theorem infiniteCompletionMap_algebraMap (p : InfinitePlace E) (q : InfinitePlace E')
    [q.LiesOver p] (a : E) :
    LiesOver.completionMap p q (algebraMap E p.Completion a) =
      algebraMap E' q.Completion (algebraMap E E' a) := by
  change LiesOver.completionMap p q ((WithAbs.toAbs p.1 a : WithAbs p.1) : p.Completion) =
    ((WithAbs.toAbs q.1 (algebraMap E E' a) : WithAbs q.1) : q.Completion)
  rw [LiesOver.completionMap_coe]
  rfl

private theorem infiniteLocalNorm_conj (p : InfinitePlace E) (q : InfinitePlace E')
    [q.LiesOver p] [(q.comap (cmConj E').toRingHom).LiesOver (p.comap (cmConj E).toRingHom)]
    (x : (q.comap (cmConj E').toRingHom).Completion) :
    InfiniteExtension.localNorm p q (infiniteCompletionEquiv (cmConj E') q x) =
      infiniteCompletionEquiv (cmConj E) p
        (InfiniteExtension.localNorm (p.comap (cmConj E).toRingHom)
          (q.comap (cmConj E').toRingHom) x) := by
  let p' := p.comap (cmConj E).toRingHom
  let q' := q.comap (cmConj E').toRingHom
  have hdense : DenseRange (algebraMap E p'.Completion) := by
    apply (InfinitePlace.Completion.denseRange_coe p').mono
    rintro _ ⟨a, rfl⟩
    exact ⟨WithAbs.equiv p'.1 a, rfl⟩
  have hcomm (z : p'.Completion) :
      LiesOver.completionMap (v := p) (w := q) (infiniteCompletionEquiv (cmConj E) p z) =
        infiniteCompletionEquiv (cmConj E') q (LiesOver.completionMap (v := p') (w := q') z) := by
    refine congrFun (hdense.equalizer
      ((LiesOver.continuous_completionMap (v := p) (w := q)).comp
        (continuous_infiniteCompletionMap (cmConj E).toRingHom p))
      ((continuous_infiniteCompletionMap (cmConj E').toRingHom q).comp
        (LiesOver.continuous_completionMap (v := p') (w := q'))) ?_) z
    funext a
    dsimp only [p', q']
    simp only [Function.comp_apply, infiniteCompletionMap_coe, infiniteCompletionMap_algebraMap]
    exact congrArg (algebraMap E' q.Completion) (HarrisDatum.complexConj_algebraMap a).symm
  change Algebra.norm p.Completion (infiniteCompletionEquiv (cmConj E') q x) =
    infiniteCompletionEquiv (cmConj E) p (Algebra.norm p'.Completion x)
  rw [Algebra.norm_eq_of_equiv_equiv (infiniteCompletionEquiv (cmConj E) p)
    (infiniteCompletionEquiv (cmConj E') q) (RingHom.ext hcomm) x, RingEquiv.apply_symm_apply]

private theorem adeleNorm_conj (a : AdeleRing (𝓞 E') E') :
    adeleNorm (K := E) (adeleEquiv (cmConj E') a) =
      adeleEquiv (cmConj E) (adeleNorm (K := E) a) := by
  apply Prod.ext
  · funext p
    change (∏ q : InfinitePlacesAbove E' p, InfiniteExtension.localNorm p q.1
      (infiniteCompletionEquiv (cmConj E') q.1 (a.1 (infinitePlaceEquiv (cmConj E') q.1)))) =
        infiniteCompletionEquiv (cmConj E) p
          (∏ q : InfinitePlacesAbove E' (infinitePlaceEquiv (cmConj E) p),
            InfiniteExtension.localNorm (infinitePlaceEquiv (cmConj E) p) q.1 (a.1 q.1))
    calc
      _ = ∏ q : InfinitePlacesAbove E' (infinitePlaceEquiv (cmConj E) p),
          infiniteCompletionEquiv (cmConj E) p
            (InfiniteExtension.localNorm (infinitePlaceEquiv (cmConj E) p) q.1 (a.1 q.1)) := by
        refine Fintype.prod_equiv (infinitePlacesAboveConj p) _ _ fun q => ?_
        let h : (q.1.comap (cmConj E').toRingHom).LiesOver (p.comap (cmConj E).toRingHom) :=
          (infinitePlacesAboveConj p q).2
        exact infiniteLocalNorm_conj p q.1 _
      _ = _ := (map_prod (infiniteCompletionEquiv (cmConj E) p) _ _).symm
  · apply IsDedekindDomain.FiniteAdeleRing.ext
    intro p
    change (∏ q : FinitePlacesAbove E' p, FiniteExtension.localNorm p q.1
      (finiteCompletionEquiv (cmConj E') q.1 (a.2 (finitePlaceEquiv (cmConj E') q.1)))) =
        finiteCompletionEquiv (cmConj E) p
          (∏ q : FinitePlacesAbove E' (finitePlaceEquiv (cmConj E) p),
            FiniteExtension.localNorm (finitePlaceEquiv (cmConj E) p) q.1 (a.2 q.1))
    rw [map_prod (finiteCompletionEquiv (cmConj E) p)]
    refine Fintype.prod_equiv (finitePlacesAboveConj p) _ _ fun q => ?_
    let h : (finitePlaceEquiv (cmConj E') q.1).asIdeal.LiesOver
        (finitePlaceEquiv (cmConj E) p).asIdeal :=
      (finitePlacesAboveConj p q).2
    exact finiteLocalNorm_conj p q.1 _

end

/-- The norm on actual idele classes commutes with the arithmetic CM involution. -/
theorem cmNormConjugation : CMNormConjugationStatement.{u, v} := by
  intro E E' _ _ _ _ _ _ _ x
  refine QuotientGroup.induction_on x fun a => ?_
  simp only [ideleClassNorm_mk, ideleClassComplexConj_mk]
  apply congrArg QuotientGroup.mk
  apply Units.ext
  exact adeleNorm_conj (E := E) a.val

end Langlands.Global.Harris
