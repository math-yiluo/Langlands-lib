/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleRestrictedAugmentationInclusion

/-! # Global sections of the restricted resolution comparison

Source: Stacks Project, Tag 015J, finite-diagonal mapped-total comparison.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
private theorem restricted_iso_formula
    (X : Scheme.{u})
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (T : EtaleTermwiseHypercohomology X K) (q : ℤ)
    (m : ℕ) (s n : ℤ) (h : (m : ℤ) + s = n) :
    (((CartanEilenbergPresentation.mappedFunctor
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1})).obj
        (etaleRestrictedBicomplex X K T q)).flip).ιTotal
          (ComplexShape.up ℤ) (m : ℤ) s n h ≫
      (etaleCEMappedTotalIso (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1})
        (etaleRestrictedBicomplex X K T q)
        (etaleRestrictedBicomplex_below X K T q)).hom.f n =
    (HomologicalComplex.extendXIso
      (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj ((etaleRestrictedBicomplex X K T q).X s))
      ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ)) rfl).hom ≫
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
      ((HomologicalComplex.extendXIso
        (((𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj ((etaleRestrictedBicomplex X K T q).X s))
        ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ)) rfl).inv ≫
        (((CartanEilenbergPresentation.mappedFunctor
          (𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))).obj
            (etaleRestrictedBicomplex X K T q)).flip).ιTotal
              (ComplexShape.up ℤ) (m : ℤ) s n h) := by
  classical
  dsimp only [etaleCEMappedTotalIso, Iso.trans_hom, HomologicalComplex.comp_f]
  rw [HomologicalComplex₂.total.mapIso_hom]
  rw [← Category.assoc, HomologicalComplex₂.ιTotal_map, Category.assoc]
  dsimp only [HomologicalComplex₂.mapTotalIso, HomologicalComplex.Hom.isoOfComponents]
  rw [HomologicalComplex₂.ι_mapTotalXIso_hom]
  have hr : ComplexShape.embeddingUpNat.r (m : ℤ) = some m :=
    ComplexShape.embeddingUpNat.r_f m
  have hx := HomologicalComplex.mapExtendX_hom_eq
    ((etaleRestrictedBicomplex X K T q).X s)
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}) hr
  simp only [HomologicalComplex₂.flipFunctor, NatIso.mapHomologicalComplex,
    ComplexShape.Embedding.mapExtendFunctorNatIso, HomologicalComplex.mapExtendIso]
  change (HomologicalComplex.mapExtendX ((etaleRestrictedBicomplex X K T q).X s)
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (ComplexShape.embeddingUpNat.r (m : ℤ))).inv ≫ _ = _
  rw [hx]
  simp only [HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso,
    eqToIso, Functor.map_comp, eqToHom_map]
  rw [← Category.assoc, eqToHom_trans]


set_option backward.isDefEq.respectTransparency false in
/-- The complex map obtained by sections of the restricted resolution comparison
is the prescribed sections inclusion followed by the full comparison.
Source: Stacks Project, Tag 015J, proof remark (3).

Proof: In degree n, precompose both maps with the images under Γ of the
restricted total summands in bidegrees (r,s), where r ≥ 0, s ≥ q, r+s=n.
The finite-diagonal coproduct comparison etaleCEMappedTotalIso identifies
these generators with the summands of the restricted mapped total. The total
map sends each summand through the corresponding column inclusion to the
full total. Apply T.w_formula to that full summand. Naturality of the
extension-by-zero comparison cancels the extension isomorphisms on both
sides, leaving Γ of the sheaf-total inclusion followed by T.comparison.
The coproduct universal property gives equality in degree n, and chain-map
extensionality gives the assertion. Negative resolution degrees and omitted
columns are zero. Empty diagonals and zero terms require no separate choice;
the same proof applies to every integer q.
(blueprint: lem-weil-pbc-etale-restricted-sections-comparison-map). -/
theorem etaleRestrictedSections_comparison_map
    (X : Scheme.{u})
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (T : EtaleTermwiseHypercohomology X K) (q : ℤ) :
    ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
      (ComplexShape.up ℤ)).map
        (etaleRestrictedTotalInclusion X K T q ≫ T.comparison) =
      etaleRestrictedSectionsInclusion X K T q ≫ T.w := by
  classical
  let F := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let e := etaleCEMappedTotalIso F (etaleRestrictedBicomplex X K T q)
    (etaleRestrictedBicomplex_below X K T q)
  apply (cancel_epi e.hom).1
  simp only [etaleRestrictedSectionsInclusion, e, F, Category.assoc, Iso.hom_inv_id_assoc]
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex₂.total.hom_ext
  intro r s h
  by_cases hr : 0 ≤ r
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hr
    dsimp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
    rw [← Category.assoc, restricted_iso_formula X K T q m s n h]
    dsimp only [etaleRestrictedMappedInclusion]
    rw [HomologicalComplex₂.ιTotal_map_assoc]
    erw [T.w_formula m s n h]
    simp only [Functor.map_comp,
      Category.assoc]
    dsimp only [etaleRestrictedTotalInclusion]
    simp only [← Functor.map_comp]
    erw [HomologicalComplex₂.ιTotal_map_assoc]
    simp only [Functor.map_comp]
    dsimp [HomologicalComplex₂.flipFunctor, CartanEilenbergPresentation.mappedFunctor]
    erw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat
      (i := m) (i' := (m : ℤ)) rfl]
    erw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat
      (i := m) (i' := (m : ℤ)) rfl]
    simp only [HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso,
      Functor.map_comp, Category.assoc]
    simp [← Functor.map_comp]
  · exact (HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat r
      (fun m hm ↦ by change (m : ℤ) = r at hm; omega)).eq_of_src _ _

end AlgebraicGeometry.Etale
