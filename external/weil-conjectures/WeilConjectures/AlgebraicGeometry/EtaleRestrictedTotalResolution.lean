/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleRestrictedAugmentationComm
import WeilConjectures.CategoryTheory.CartanEilenbergTotalResolution

/-! # Properties of the restricted augmented CE total

Source: Stacks Project, Tags 015J and 0133.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The augmentation with prescribed degree-zero summand maps.
Source: Stacks, Tags 015J and 0133. Its data are explicit; only the named
commutation lemma supplies the chain-map proof.
(blueprint: def-weil-pbc-etale-restricted-augmentation). -/
noncomputable def etaleRestrictedAugmentation
    (X : Scheme.{u})
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (T : EtaleTermwiseHypercohomology X K) (q : ℤ) :
    K.obj.stupidTrunc (ComplexShape.embeddingUpIntGE q) ⟶
      etaleRestrictedTotal X K T q where
  f := etaleRestrictedAugmentationComponent X K T q
  comm' := etaleRestrictedAugmentation_comm X K T q

private noncomputable def restrictedRowAugmentation
    (X : Scheme.{u})
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (T : EtaleTermwiseHypercohomology X K) (q : ℤ) :
    ((CochainComplex.single₀
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (K.obj.stupidTrunc (ComplexShape.embeddingUpIntGE q)) ⟶
      etaleRestrictedBicomplex X K T q :=
  ((K.obj.restriction (ComplexShape.embeddingUpIntGE q)).mapExtendIso
    (ComplexShape.embeddingUpIntGE q)
    (CochainComplex.single₀ (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))).hom ≫
      HomologicalComplex.stupidTruncMap T.a (ComplexShape.embeddingUpIntGE q)

set_option backward.isDefEq.respectTransparency false in
/-- The explicit restricted augmentation is a K-injective resolution.
Source: Stacks, Tag 015J, proof remark (3), and Tag 0133.

Proof: Restrict T.a to outer degrees at least q and extend by zero. In a retained
row, the restriction is conjugate to T.a.f s by the stupid-truncation component
isomorphisms, hence is a quasi-isomorphism by T.rows. In an omitted row both
complexes are zero. The retained terms are injective by T.terms and the omitted
terms are zero, hence injective. The restricted bicomplex vanishes below q.
Apply cartanEilenberg_total_resolution to these rows and the stupid truncation,
which is bounded below by q. Its augmentation formula agrees degreewise with
etaleRestrictedAugmentationComponent: in retained rows the projection and
inclusion cancel, and in omitted rows the source is zero. Extensionality of
chain maps identifies the resulting augmentation with the explicit map here.
Thus it is a quasi-isomorphism and its total is K-injective. Equivalently the
finite diagonal filtration of its cone has acyclic augmented rows, and its
terms are finite sums of injectives. This also treats the zero complex, negative
q, and degrees below q, whose diagonals are empty.
(blueprint: lem-weil-pbc-etale-restricted-total-resolution). -/
theorem etaleRestrictedTotal_resolution
    (X : Scheme.{u})
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (T : EtaleTermwiseHypercohomology X K) (q : ℤ) :
    QuasiIso (etaleRestrictedAugmentation X K T q) ∧
      CochainComplex.IsKInjective (etaleRestrictedTotal X K T q) := by
  classical
  let e := ComplexShape.embeddingUpIntGE q
  let Iq := etaleRestrictedBicomplex X K T q
  let aq := restrictedRowAugmentation X K T q
  have hterms (s : ℤ) (r : ℕ) : Injective ((Iq.X s).X r) := by
    by_cases hs : q ≤ s
    · obtain ⟨i, hi⟩ : ∃ i : ℕ, e.f i = s := by
        refine ⟨(s - q).toNat, ?_⟩
        change q + ((s - q).toNat : ℤ) = s
        rw [Int.toNat_of_nonneg (by omega)]
        omega
      exact Injective.of_iso ((HomologicalComplex.eval _ _ r).mapIso
        (T.I.stupidTruncXIso e hi)).symm (T.terms s r)
    · exact ((HomologicalComplex.eval _ _ r).map_isZero
        (T.I.isZero_stupidTrunc_X e s
          (fun i hi ↦ by change q + (i : ℤ) = s at hi; omega))).injective
  have hrows (s : ℤ) : QuasiIso (aq.f s) := by
    by_cases hs : q ≤ s
    · obtain ⟨i, hi⟩ : ∃ i : ℕ, e.f i = s := by
        refine ⟨(s - q).toNat, ?_⟩
        change q + ((s - q).toNat : ℤ) = s
        rw [Int.toNat_of_nonneg (by omega)]
        omega
      subst s
      let := T.I.isIso_ιStupidTrunc_f e (i := i) rfl
      rw [← quasiIso_iff_comp_right (aq.f (e.f i))
        ((T.I.ιStupidTrunc e).f (e.f i))]
      dsimp only [aq, restrictedRowAugmentation, HomologicalComplex.comp_f]
      rw [Category.assoc, ← HomologicalComplex.comp_f,
        HomologicalComplex.ιStupidTrunc_naturality, HomologicalComplex.comp_f]
      dsimp only [HomologicalComplex.mapExtendIso, HomologicalComplex.Hom.isoOfComponents]
      let := T.rows (e.f i)
      infer_instance
    · have hzero := T.I.isZero_stupidTrunc_X e s
        (fun i hi ↦ by change q + (i : ℤ) = s at hi; omega)
      have hsrc := K.obj.isZero_stupidTrunc_X e s
        (fun i hi ↦ by change q + (i : ℤ) = s at hi; omega)
      have hsrc' := (CochainComplex.single₀
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})).map_isZero hsrc
      have : IsIso (aq.f s) := hsrc'.isIso (hzero) _
      infer_instance
  let Kq : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    ⟨K.obj.stupidTrunc e, ⟨q, by
      rw [CochainComplex.isStrictlyGE_iff]
      intro n hn
      exact K.obj.isZero_stupidTrunc_X e n
        (fun i hi ↦ by change q + (i : ℤ) = n at hi; omega)⟩⟩
  obtain ⟨r, hr, hq, hk⟩ := Functor.cartanEilenberg_total_resolution Kq Iq aq
    (etaleRestrictedBicomplex_below X K T q) hterms hrows
  have hformula (n : ℤ) : (aq.f n).f 0 =
      (K.obj.ιStupidTrunc e).f n ≫ (T.a.f n).f 0 ≫ (T.I.πStupidTruncf e n).f 0 := by
    by_cases hn : q ≤ n
    · obtain ⟨i, hi⟩ : ∃ i : ℕ, e.f i = n := by
        refine ⟨(n - q).toNat, ?_⟩
        change q + ((n - q).toNat : ℤ) = n
        rw [Int.toNat_of_nonneg (by omega)]
        omega
      subst n
      dsimp [aq, restrictedRowAugmentation, HomologicalComplex.stupidTruncMap]
      simp only [e, HomologicalComplex.mapExtendIso,
        HomologicalComplex.ιStupidTrunc, HomologicalComplex.ιStupidTruncf_eq,
        HomologicalComplex.πStupidTruncf_eq]
      dsimp only [HomologicalComplex.Hom.isoOfComponents]
      rw [HomologicalComplex.extendMap_f _ (ComplexShape.embeddingUpIntGE q)
        (i := i) (i' := (ComplexShape.embeddingUpIntGE q).f i) rfl]
      rw [HomologicalComplex.mapExtendX_hom_eq _ _
        ((ComplexShape.embeddingUpIntGE q).r_f i)]
      simp [HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso,
        HomologicalComplex.restrictionMap]
    · exact (K.obj.isZero_stupidTrunc_X e n
        (fun i hi ↦ by change q + (i : ℤ) = n at hi; omega)).eq_of_src _ _
  have he : r = etaleRestrictedAugmentation X K T q := by
    ext n : 1
    rw [hr]
    change (aq.f n).f 0 ≫ _ = etaleRestrictedAugmentationComponent X K T q n
    rw [hformula]
    rfl
  exact ⟨he ▸ hq, hk⟩

end AlgebraicGeometry.Etale
