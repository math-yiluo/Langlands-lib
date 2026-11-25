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
/-- The canonical sections inclusion factors through the filtered step.
Source: Stacks, Tag 015J, proof remark (3), column filtration.

Proof: In each degree the restricted mapped total is the coproduct of the
summands with complex degree s ≥ q. Its map to the full mapped total is their
coproduct inclusion. Thus its image is the second-filtration subobject at q.
T.filtration_formula identifies this with (T.L).complexStep q n. The canonical
finite-diagonal sections comparison identifies Γ of the restricted sheaf total
with this restricted mapped total. Factor its inclusion degreewise through the
step inclusions. These maps commute with differentials: after composing with
the monic step inclusion the equation is the chain-map equation for the total
inclusion. Thus they assemble into a factorization through (T.L).step q.
In empty diagonals all maps are zero; no positivity assumption on q is used.
(blueprint: lem-weil-pbc-etale-restricted-sections-factors). -/
theorem etaleRestrictedSections_factors
    (X : Scheme.{u})
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (T : EtaleTermwiseHypercohomology X K) (q : ℤ) :
    (T.L.step q).Factors (etaleRestrictedSectionsInclusion X K T q) := by
  classical
  let F := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let J := ((CartanEilenbergPresentation.mappedFunctor F).obj T.I).flip
  let R := ((CartanEilenbergPresentation.mappedFunctor F).obj
    (etaleRestrictedBicomplex X K T q)).flip
  let φ : R ⟶ J := (HomologicalComplex₂.flipFunctor AddCommGrpCat.{u + 1}
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map
      ((CartanEilenbergPresentation.mappedFunctor F).map
        (T.I.ιStupidTrunc (ComplexShape.embeddingUpIntGE q)))
  let f : R.total (ComplexShape.up ℤ) ⟶ J.total (ComplexShape.up ℤ) :=
    HomologicalComplex₂.total.map φ (ComplexShape.up ℤ)
  have hz (r s : ℤ) (h : r < 0 ∨ s < q) : IsZero ((R.X r).X s) := by
    rcases h with h | h
    · exact HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat r
        (fun m hm ↦ by change (m : ℤ) = r at hm; omega)
    · exact (HomologicalComplex.eval AddCommGrpCat.{u + 1} (ComplexShape.up ℤ) r).map_isZero
        ((ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u + 1}).map_isZero
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map_isZero
            (T.I.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE q) s
              (fun i hi ↦ by change q + (i : ℤ) = s at hi; omega))))
  have hf (n : ℤ) : (T.L.complexStep q n).Factors (f.f n) := by
    let Q := T.L.complexStep q n
    have hι (r s : ℤ) (h : r + s = n) :
        Q.Factors (R.ιTotal (ComplexShape.up ℤ) r s n h ≫ f.f n) := by
      by_cases hr : 0 ≤ r
      · by_cases hs : q ≤ s
        · rw [HomologicalComplex₂.ιTotal_map]
          apply Subobject.factors_of_factors_right
          have hle : imageSubobject (J.ιTotal (ComplexShape.up ℤ) r s n h) ≤ Q := by
            change imageSubobject (J.ιTotal (ComplexShape.up ℤ) r s n h) ≤
              T.L.complexStep q n
            rw [T.filtration_formula]
            dsimp [HomologicalComplex₂.secondFiltration]
            have hm : s ∈ Finset.Icc q n := Finset.mem_Icc.mpr ⟨hs, by omega⟩
            have hh := Finset.le_sup (f := fun k ↦ imageSubobject
              (J.ιTotalOrZero (ComplexShape.up ℤ) (n - k) k n)) hm
            rw [show n - s = r by omega,
              J.ιTotalOrZero_eq (ComplexShape.up ℤ) r s n h] at hh
            exact hh
          apply Subobject.factors_of_le _ hle
          simpa only [Category.id_comp] using imageSubobject_factors_comp_self
              (J.ιTotal (ComplexShape.up ℤ) r s n h) (𝟙 _)
        · rw [(hz r s (Or.inr (by omega))).eq_zero_of_src
            (R.ιTotal (ComplexShape.up ℤ) r s n h ≫ f.f n)]
          exact Subobject.factors_zero
      · rw [(hz r s (Or.inl (by omega))).eq_zero_of_src
          (R.ιTotal (ComplexShape.up ℤ) r s n h ≫ f.f n)]
        exact Subobject.factors_zero
    let a : (R.total (ComplexShape.up ℤ)).X n ⟶ Q :=
      R.totalDesc (fun r s h ↦ Q.factorThru _ (hι r s h))
    have ha : a ≫ Q.arrow = f.f n := by
      apply HomologicalComplex₂.total.hom_ext
      intro r s h
      simp only [a, ← Category.assoc, HomologicalComplex₂.ι_totalDesc,
        Subobject.factorThru_arrow]
    rw [← ha]
    exact Subobject.factors_comp_arrow a
  have hf' (n : ℤ) : (Subobject.mk ((T.L.step q).arrow.f n)).Factors (f.f n) := by
    have h := hf n
    simpa only [DecreasingFiltration.complexStep, imageSubobject_mono] using h
  let g (n : ℤ) : (R.total (ComplexShape.up ℤ)).X n ⟶
      (T.L.step q : CochainComplex _ ℤ).X n :=
    (Subobject.mk ((T.L.step q).arrow.f n)).factorThru (f.f n) (hf' n) ≫
      (Subobject.underlyingIso ((T.L.step q).arrow.f n)).hom
  have hg (n : ℤ) : g n ≫ (T.L.step q).arrow.f n = f.f n := by
    simp [g]
  let lift : R.total (ComplexShape.up ℤ) ⟶ (T.L.step q : CochainComplex _ ℤ) :=
    { f := g
      comm' := by
        intro i j h
        apply (cancel_mono ((T.L.step q).arrow.f j)).1
        simp only [Category.assoc]
        rw [← (T.L.step q).arrow.comm i j, ← Category.assoc, hg, hg]
        exact f.comm i j }
  have hlift : lift ≫ (T.L.step q).arrow = f := by
    apply HomologicalComplex.hom_ext
    intro n
    exact hg n
  apply Subobject.factors_of_factors_right
    ((etaleCEMappedTotalIso F (etaleRestrictedBicomplex X K T q)
      (etaleRestrictedBicomplex_below X K T q)).inv)
  change (T.L.step q).Factors f
  rw [← hlift]
  exact Subobject.factors_comp_arrow lift

end AlgebraicGeometry.Etale
