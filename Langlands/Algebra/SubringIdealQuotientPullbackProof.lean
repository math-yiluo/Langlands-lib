import Langlands.Algebra.SubringIdealQuotientPullbackStatement

open CategoryTheory CategoryTheory.Limits

universe u

namespace Langlands.Algebra

/-- The canonical square of a subring and a contained ambient ideal is a pullback. -/
theorem subringIdealQuotientPullback : SubringIdealQuotientPullbackStatement.{u} := by
  intro B _ R I hIR
  let q := Ideal.quotientMap (I := I.comap R.subtype) I R.subtype le_rfl
  have w : CommRingCat.ofHom R.subtype ≫ CommRingCat.ofHom (Ideal.Quotient.mk I) =
      CommRingCat.ofHom (Ideal.Quotient.mk (I.comap R.subtype)) ≫
        CommRingCat.ofHom q := by
    ext r
    exact (Ideal.quotientMap_mk (I := I) (J := I.comap R.subtype)
      (f := R.subtype) (H := le_rfl) (x := r)).symm
  apply IsPullback.of_isLimit (c := PullbackCone.mk _ _ w)
  apply PullbackCone.isLimitAux'
  intro s
  have hmem (x : s.pt) : s.fst x ∈ R := by
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (s.snd x)
    have hc := ConcreteCategory.congr_hom s.condition x
    change Ideal.Quotient.mk I (s.fst x) = q (s.snd x) at hc
    rw [← hr, Ideal.quotientMap_mk] at hc
    have hd : s.fst x - (r : B) ∈ R :=
      hIR ((Ideal.Quotient.mk_eq_mk_iff_sub_mem (I := I) _ _).mp hc)
    simpa only [sub_add_cancel] using R.add_mem hd r.property
  let l : s.pt ⟶ CommRingCat.of R :=
    CommRingCat.ofHom (s.fst.hom.codRestrict R hmem)
  refine ⟨l, ?_, ?_, ?_⟩
  · ext x
    rfl
  · ext x
    apply Ideal.quotientMap_injective (I := I) (f := R.subtype)
    change q (Ideal.Quotient.mk (I.comap R.subtype) (l x)) = q (s.snd x)
    rw [Ideal.quotientMap_mk]
    exact ConcreteCategory.congr_hom s.condition x
  · intro m hm _
    ext x
    apply Subtype.ext
    exact ConcreteCategory.congr_hom hm x

end Langlands.Algebra
