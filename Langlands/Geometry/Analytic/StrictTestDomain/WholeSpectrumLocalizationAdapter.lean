import Langlands.Geometry.Analytic.StrictTestDomain.StandardRationalGluingPreparation
import Langlands.Geometry.Analytic.StrictTestDomain.TrivialScalarRationalLocalizationProof
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Ordinary-localization adapter for whole-spectrum descent

The generic assembly lemma assumes ordinary localization. The final lemma
discharges this premise under the trivial scalar norm bound using the published
localization proof. Neither lemma is the unconditional whole-spectrum target.
-/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTestDomain

open RationalData

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}

/-- Conditional algebraic gluing for actual rational quotients, assuming their
ordinary-localization property, discharged in the scalar-bound specialization below. -/
theorem existsUnique_whole_gluing_of_localizations
    (h : ∀ d : RationalData K P,
      letI := d.baseMap.toAlgHom.toRingHom.toAlgebra
      IsLocalization.Away d.denominator d.algebra)
    {I : Type u} (D : I → RationalData K P)
    (hc : ∀ x : BanachSpectrum P, ∃ i, x ∈ (D i).locus)
    (s : ∀ i, (D i).algebra)
    (hs : ∀ i j, (interLeft (D i) (D j)).restriction (s i) =
      (interRight (D i) (D j)).restriction (s j)) :
    ∃! a : P, ∀ i, (D i).baseMap a = s i := by
  classical
  let al (d : RationalData K P) : Algebra P d.algebra :=
    d.baseMap.toAlgHom.toRingHom.toAlgebra
  have loc (d : RationalData K P) : IsLocalization.Away d.denominator d.algebra := h d
  have res {d e : RationalData K P} (f : Inclusion d e) (a : P) :
      f.restriction (algebraMap P e.algebra a) = algebraMap P d.algebra a :=
    congrArg (fun g : BoundedAlgHom K P d.algebra => g a) f.restriction_comp_baseMap
  let A : Set P := Set.range (fun i => (D i).denominator)
  let pick (a : A) : I := a.property.choose
  have pick_eq (a : A) : (D (pick a)).denominator = a.val := a.property.choose_spec
  have locPick (a : A) : IsLocalization.Away a.val (D (pick a)).algebra := by
    rw [← pick_eq a]
    infer_instance
  let e (a : A) : Localization.Away a.val ≃ₐ[P] (D (pick a)).algebra :=
    IsLocalization.algEquiv (Submonoid.powers a.val) _ _
  have locInter (a b : A) :
      IsLocalization.Away (a.val * b.val) ((D (pick a)).inter (D (pick b))).algebra := by
    rw [← pick_eq a, ← pick_eq b]
    exact loc ((D (pick a)).inter (D (pick b)))
  let ee (a b : A) : Localization.Away (a.val * b.val) ≃ₐ[P]
      ((D (pick a)).inter (D (pick b))).algebra :=
    IsLocalization.algEquiv (Submonoid.powers (a.val * b.val)) _ _
  have left_eq (a b : A) :
      (ee a b).symm.toRingHom.comp
          ((interLeft (D (pick a)) (D (pick b))).restriction.toAlgHom.toRingHom.comp
            (e a).toRingHom) =
        IsLocalization.Away.awayToAwayRight (S := Localization.Away a.val)
          (P := Localization.Away (a.val * b.val)) a.val b.val := by
    apply IsLocalization.ringHom_ext (Submonoid.powers a.val)
    ext r
    change (ee a b).symm ((interLeft (D (pick a)) (D (pick b))).restriction
      (e a (algebraMap P (Localization.Away a.val) r))) = _
    rw [(e a).commutes, RingHom.comp_apply, IsLocalization.Away.awayToAwayRight_eq]
    exact (congrArg (ee a b).symm (res (interLeft (D (pick a)) (D (pick b))) r)).trans
      ((ee a b).symm.commutes r)
  have right_eq (a b : A) :
      (ee a b).symm.toRingHom.comp
          ((interRight (D (pick a)) (D (pick b))).restriction.toAlgHom.toRingHom.comp
            (e b).toRingHom) =
        IsLocalization.Away.awayToAwayLeft (S := Localization.Away b.val)
          (P := Localization.Away (a.val * b.val)) b.val a.val := by
    apply IsLocalization.ringHom_ext (Submonoid.powers b.val)
    ext r
    change (ee a b).symm ((interRight (D (pick a)) (D (pick b))).restriction
      (e b (algebraMap P (Localization.Away b.val) r))) = _
    rw [(e b).commutes, RingHom.comp_apply, IsLocalization.Away.awayToAwayLeft_eq]
    exact (congrArg (ee a b).symm (res (interRight (D (pick a)) (D (pick b))) r)).trans
      ((ee a b).symm.commutes r)
  let t (a : A) : Localization.Away a.val := (e a).symm (s (pick a))
  have ht (a b : A) :
      IsLocalization.Away.awayToAwayRight (P := Localization.Away (a.val * b.val))
          a.val b.val (t a) =
        IsLocalization.Away.awayToAwayLeft b.val a.val (t b) := by
    rw [← left_eq a b, ← right_eq a b]
    change (ee a b).symm ((interLeft (D (pick a)) (D (pick b))).restriction
        (e a ((e a).symm (s (pick a))))) =
      (ee a b).symm ((interRight (D (pick a)) (D (pick b))).restriction
        (e b ((e b).symm (s (pick b)))))
    simpa only [AlgEquiv.apply_symm_apply] using
      congrArg (ee a b).symm (hs (pick a) (pick b))
  obtain ⟨r, hr, hu⟩ := Localization.existsUnique_algebraMap_eq_of_span_eq_top A
    (span_denominators_eq_top_of_whole_cover D hc) t ht
  have hrPick (a : A) : (D (pick a)).baseMap r = s (pick a) := by
    change algebraMap P (D (pick a)).algebra r = s (pick a)
    have hh := congrArg (e a) (hr a)
    simpa only [t, AlgEquiv.commutes, AlgEquiv.apply_symm_apply] using hh
  refine ⟨r, fun i => ?_, fun r' hr' => ?_⟩
  · let a : A := ⟨(D i).denominator, Set.mem_range_self i⟩
    let j := pick a
    have hg : (D j).denominator = (D i).denominator := pick_eq a
    have hunit : IsUnit (algebraMap P (D i).algebra ((D i).inter (D j)).denominator) := by
      change IsUnit (algebraMap P (D i).algebra ((D i).denominator * (D j).denominator))
      rw [hg, map_mul]
      exact (IsLocalization.Away.algebraMap_isUnit (D i).denominator).mul
        (IsLocalization.Away.algebraMap_isUnit (D i).denominator)
    let back : ((D i).inter (D j)).algebra →+* (D i).algebra :=
      IsLocalization.Away.lift ((D i).inter (D j)).denominator hunit
    have back_left : back.comp (interLeft (D i) (D j)).restriction.toAlgHom.toRingHom =
        RingHom.id (D i).algebra := by
      apply IsLocalization.ringHom_ext (Submonoid.powers (D i).denominator)
      ext x
      change back ((interLeft (D i) (D j)).restriction (algebraMap P (D i).algebra x)) = _
      rw [res]
      exact IsLocalization.Away.lift_eq _ _ x
    have hh := congrArg back (hs i j)
    change (back.comp (interLeft (D i) (D j)).restriction.toAlgHom.toRingHom) (s i) = _ at hh
    rw [back_left, RingHom.id_apply, ← hrPick a] at hh
    change s i = back ((interRight (D i) (D j)).restriction (algebraMap P (D j).algebra r)) at hh
    rw [res, IsLocalization.Away.lift_eq] at hh
    exact hh.symm
  · apply hu r'
    intro a
    apply (e a).injective
    dsimp only [t]
    rw [AlgEquiv.commutes, AlgEquiv.apply_symm_apply]
    exact hr' (pick a)

/-- Whole-spectrum scalar gluing under the trivial scalar norm bound, using
ordinary denominator localization for the actual rational quotients. -/
theorem existsUnique_whole_gluing_of_trivial_scalar_norm
    (hK : ∀ c : K, ‖c‖ ≤ 1)
    {I : Type u} (D : I → RationalData K P)
    (hc : ∀ x : BanachSpectrum P, ∃ i, x ∈ (D i).locus)
    (s : ∀ i, (D i).algebra)
    (hs : ∀ i j, (interLeft (D i) (D j)).restriction (s i) =
      (interRight (D i) (D j)).restriction (s j)) :
    ∃! a : P, ∀ i, (D i).baseMap a = s i :=
  existsUnique_whole_gluing_of_localizations
    (trivialScalarRationalLocalization K P hK) D hc s hs

end Langlands.Analytic.StrictTestDomain
