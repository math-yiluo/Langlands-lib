/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleRestrictedTotalConstruction

/-! # Properties of the restricted augmented CE total

Source: Stacks Project, Tags 015J and 0133.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
/-- The explicit augmentation components commute with the total differential.
Source: Stacks, Tag 015J, proof remark (3); Tag 0133, augmented total.

Proof: If n < q, the source of the two composites is zero. Otherwise both n and
n+1 are retained. Transport by the stupid-truncation component isomorphisms and
by extension from natural resolution degrees. On the resolution-degree-zero
summand the vertical differential vanishes, since the row augmentation is a
chain map from a single complex. The horizontal differential has sign +1 in
resolution degree zero and commutes with the augmentation by T.a.comm.
These give the equation for adjacent indices; nonadjacent differentials are zero.
The argument includes q < 0 and empty diagonals without a change of signs.
(blueprint: lem-weil-pbc-etale-restricted-augmentation-comm). -/
theorem etaleRestrictedAugmentation_comm
    (X : Scheme.{u})
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (T : EtaleTermwiseHypercohomology X K) (q n m : ℤ) (h : (ComplexShape.up ℤ).Rel n m) :
    etaleRestrictedAugmentationComponent X K T q n ≫
        (etaleRestrictedTotal X K T q).d n m =
      (K.obj.stupidTrunc (ComplexShape.embeddingUpIntGE q)).d n m ≫
        etaleRestrictedAugmentationComponent X K T q m := by
  classical
  have hm : m = n + 1 := by simpa using h.symm
  subst m
  by_cases hn : q ≤ n
  · obtain ⟨i, hi⟩ : ∃ i : ℕ, q + i = n := by
      refine ⟨(n - q).toNat, ?_⟩
      rw [Int.toNat_of_nonneg (by omega)]
      omega
    let J := ((CartanEilenbergPresentation.mappedFunctor
      (𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))).obj
        (etaleRestrictedBicomplex X K T q)).flip
    dsimp only [etaleRestrictedAugmentationComponent, etaleRestrictedTotal,
      HomologicalComplex₂.total]
    simp only [Preadditive.comp_add, Category.assoc, HomologicalComplex₂.ι_D₁,
      HomologicalComplex₂.ι_D₂]
    rw [J.d₁_eq (ComplexShape.up ℤ) (by simp : (ComplexShape.up ℤ).Rel 0 1) n
        (n + 1) (by dsimp [ComplexShape.π]; omega),
      J.d₂_eq (ComplexShape.up ℤ) 0 (by simp : (ComplexShape.up ℤ).Rel n (n + 1))
        (n + 1) (by simp)]
    simp only [ComplexShape.ε₁, ComplexShape.ε₂]
    dsimp only [TotalComplexShape.ε₁, TotalComplexShape.ε₂]
    simp only [ComplexShape.ε_zero, one_smul]
    let Iq := etaleRestrictedBicomplex X K T q
    change _ ≫ _ ≫ _ ≫ _ ≫
        ((Iq.X n).extend ComplexShape.embeddingUpNat).d 0 1 ≫ _ +
      _ ≫ _ ≫ _ ≫ _ ≫
        (HomologicalComplex.extendMap (Iq.d n (n + 1))
          ComplexShape.embeddingUpNat).f 0 ≫ _ = _
    rw [HomologicalComplex.extend_d_eq (Iq.X n) ComplexShape.embeddingUpNat
        (i := 0) (j := 1) (i' := 0) (j' := 1) rfl rfl,
      HomologicalComplex.extendMap_f (Iq.d n (n + 1)) ComplexShape.embeddingUpNat
        (i := 0) (i' := 0) rfl]
    simp only [Category.assoc]
    have hv := (T.a.f n).comm 0 1
    change (T.a.f n).f 0 ≫ (T.I.X n).d 0 1 = 0 ≫ (T.a.f n).f 1 at hv
    simp only [zero_comp] at hv
    have hπv := (T.I.πStupidTruncf (ComplexShape.embeddingUpIntGE q) n).comm 0 1
    simp only [HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso, eqToIso]
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    change _ ≫ (T.a.f n).f 0 ≫
        (T.I.πStupidTruncf (ComplexShape.embeddingUpIntGE q) n).f 0 ≫
        (Iq.X n).d 0 1 ≫ _ + _ = _
    dsimp only [Iq, etaleRestrictedBicomplex]
    rw [← Category.assoc
        ((T.I.πStupidTruncf (ComplexShape.embeddingUpIntGE q) n).f 0),
      hπv, Category.assoc, ← Category.assoc ((T.a.f n).f 0), hv, zero_comp, comp_zero,
      zero_add]
    have hh := congrArg (fun g ↦ g.f 0) (T.a.comm n (n + 1))
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_obj_d,
      CochainComplex.single₀_map_f_zero] at hh
    have hi' : (ComplexShape.embeddingUpIntGE q).f (i + 1) = n + 1 := by
      change q + ((i + 1 : ℕ) : ℤ) = n + 1
      omega
    have hπh : T.I.πStupidTruncf (ComplexShape.embeddingUpIntGE q) n ≫
        (T.I.stupidTrunc (ComplexShape.embeddingUpIntGE q)).d n (n + 1) =
      T.I.d n (n + 1) ≫ T.I.πStupidTruncf (ComplexShape.embeddingUpIntGE q) (n + 1) := by
      rw [T.I.πStupidTruncf_eq' (ComplexShape.embeddingUpIntGE q) hi,
        T.I.πStupidTruncf_eq' (ComplexShape.embeddingUpIntGE q) hi']
      dsimp only [HomologicalComplex.stupidTrunc]
      rw [HomologicalComplex.extend_d_eq _ (ComplexShape.embeddingUpIntGE q) hi hi',
        T.I.restriction_d_eq (ComplexShape.embeddingUpIntGE q) hi hi']
      simp
    have hπh₀ := congrArg (fun g ↦ g.f 0) hπh
    simp only [HomologicalComplex.comp_f] at hπh₀
    rw [← Category.assoc
        ((T.I.πStupidTruncf (ComplexShape.embeddingUpIntGE q) n).f 0),
      hπh₀, Category.assoc, ← Category.assoc ((T.a.f n).f 0), hh, Category.assoc]
    have hK := (K.obj.ιStupidTrunc (ComplexShape.embeddingUpIntGE q)).comm n (n + 1)
    rw [← Category.assoc ((K.obj.ιStupidTrunc (ComplexShape.embeddingUpIntGE q)).f n),
      hK, Category.assoc]
    rfl
  · exact (K.obj.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE q) n
      (fun i hi ↦ by change q + (i : ℤ) = n at hi; omega)).eq_of_src _ _

end AlgebraicGeometry.Etale
