import Langlands.Geometry.Analytic.FieldPointChartExtension
import Langlands.Geometry.Analytic.GeneralizedAffinoid.AffinoidPushout
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-! # Bounded characters and full field points on a global affinoid chart -/

noncomputable section

universe u v w uL

namespace Langlands.Analytic

open Set CategoryTheory Limits PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {L : Type uL} [NormedField L] [NormedAlgebra K L]

namespace AffinoidAtlasPresentation.FieldPoint

variable {A B : AffinoidAtlasPresentation.{u, v, w} K}

/-- Every chart evaluation is bounded, with norm bound one. -/
def boundedEval (p : FieldPoint L A) (i : A.atlas.Index)
    (hi : p.point ∈ range (A.atlas.chart i)) : BoundedAlgHom K (A.atlas.algebra i) L where
  toAlgHom := p.eval i hi
  bounded := by
    obtain ⟨s, -, hn⟩ := p.isChartPoint i hi
    refine ⟨1, zero_lt_one, fun a => ?_⟩
    change ‖p.eval i hi a‖ ≤ 1 * ‖a‖
    rw [one_mul, hn a]
    exact s.le_norm a

@[simp]
theorem boundedEval_toAlgHom (p : FieldPoint L A) (i : A.atlas.Index)
    (hi : p.point ∈ range (A.atlas.chart i)) :
    (p.boundedEval i hi).toAlgHom = p.eval i hi := rfl

/-- The actual field-point map computes bounded evaluation by the given
bounded chart pullback. -/
theorem map_boundedEval (p : FieldPoint L A) (f : StrongHom A B)
    (hA : A.atlas.HasAllLocalDomains) (j : B.atlas.Index)
    (hj : f.baseMap p.point ∈ range (B.atlas.chart j))
    (i : A.atlas.Index) (hi : p.point ∈ range (A.atlas.chart i))
    (hij : f.baseMap '' range (A.atlas.chart i) ⊆ range (B.atlas.chart j)) :
    (p.map f hA).boundedEval j hj = (p.boundedEval i hi).comp (f.pullback i j hij) := by
  apply BoundedAlgHom.ext
  exact AlgHom.congr_fun (p.map_eval f hA j hj i hi hij)

variable [CompleteSpace L]

/-- A full field point is determined by evaluation in a chart covering the
whole space, under the canonical domain residue comparison. -/
theorem boundedEval_injective
    (hd : DomainCompletedResidueSurjectivityStatement.{u})
    (i : A.atlas.Index) (hi : range (A.atlas.chart i) = univ) :
    Function.Injective (fun p : FieldPoint L A => p.boundedEval i (hi.symm ▸ mem_univ _)) := by
  intro p q hpq
  have hp := hi.symm ▸ mem_univ p.point
  have hq := hi.symm ▸ mem_univ q.point
  obtain ⟨s, hs, hn⟩ := p.isChartPoint i hp
  obtain ⟨t, ht, hm⟩ := q.isChartPoint i hq
  have hst : s = t := by
    apply BanachSpectrum.ext
    intro a
    exact (hn a).symm.trans ((congrArg norm (congrArg
      (fun c : BoundedAlgHom K (A.atlas.algebra i) L => c a) hpq)).trans (hm a))
  have hpoint : p.point = q.point := hs.symm.trans ((congrArg (A.atlas.chart i) hst).trans ht)
  exact eq_of_eval_eq hd hpoint i hp hq (congrArg BoundedAlgHom.toAlgHom hpq)

/-- Every bounded character on a global chart extends to a full field point,
under the canonical domain residue comparison. -/
theorem boundedEval_surjective
    (hd : DomainCompletedResidueSurjectivityStatement.{u})
    (i : A.atlas.Index) (hi : range (A.atlas.chart i) = univ) :
    Function.Surjective (fun p : FieldPoint L A => p.boundedEval i (hi.symm ▸ mem_univ _)) := by
  intro c
  let s := BanachSpectrum.comap c.toBoundedRingHom (BanachSpectrum.fieldPoint L)
  obtain ⟨p, ⟨-, hp, he⟩, -⟩ := existsUnique_of_chartCharacter
    hd (A.atlas.chart i s) i c.toAlgHom ⟨s, rfl, fun _ => rfl⟩
  exact ⟨p, BoundedAlgHom.ext (AlgHom.congr_fun he)⟩

/-- Full field points of an atlas with a global chart are exactly its bounded
characters, conditional on domain residue comparison. -/
def globalChartCharacterEquiv
    (hd : DomainCompletedResidueSurjectivityStatement.{u})
    (i : A.atlas.Index) (hi : range (A.atlas.chart i) = univ) :
    FieldPoint L A ≃ BoundedAlgHom K (A.atlas.algebra i) L :=
  Equiv.ofBijective _ ⟨boundedEval_injective hd i hi, boundedEval_surjective hd i hi⟩

end AffinoidAtlasPresentation.FieldPoint

namespace PresentedAffinoidAlgebra.AffinoidPushout

variable {A B C : PresentedAffinoidAlgebra K}
  (f : BoundedAlgHom K A B) (g : BoundedAlgHom K A C)

/-- Restriction of bounded characters along a bounded algebra map. -/
def restrictCharacter {R S : PresentedAffinoidAlgebra K} (h : BoundedAlgHom K R S) :
    BoundedAlgHom K S L ⟶ BoundedAlgHom K R L :=
  TypeCat.ofHom fun c => c.comp h

omit [CompleteSpace K] in
/-- The actual affinoid pushout has the pullback universal property on bounded
characters into any complete ultrametric field, in an independent universe. -/
theorem isPullback_characters [IsUltrametricDist L] [CompleteSpace L] :
    IsPullback (restrictCharacter (L := L) (leftMap f g))
      (restrictCharacter (L := L) (rightMap f g))
      (restrictCharacter (L := L) f) (restrictCharacter (L := L) g) := by
  apply (Types.isPullback_iff _ _ _ _).2
  refine ⟨?_, ?_, ?_⟩
  · ext c a
    exact congrArg (fun h : BoundedAlgHom K A (algebra f g) => c (h a)) (condition f g)
  · intro c d h
    exact hom_ext f g L c d h.1 h.2
  · intro c d h
    obtain ⟨e, he, -⟩ := existsUnique_lift f g L c d h
    exact ⟨e, he⟩

end PresentedAffinoidAlgebra.AffinoidPushout

end Langlands.Analytic
