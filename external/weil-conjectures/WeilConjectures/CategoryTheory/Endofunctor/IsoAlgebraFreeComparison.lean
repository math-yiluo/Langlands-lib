/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.OfBijectiveCounit
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra

/-!
# Free algebras and transport of algebras

Let `F : C ⥤ C` and `G : D ⥤ D` be autoequivalences, `L : C ⥤ D` a functor and
`e : L ⋙ G ≅ F ⋙ L`, transporting algebras along `L` (`IsoAlgebra.mapOfNatIso e`). The free algebra
`∐ₙ Gⁿ (L S)` maps to the transport `L (∐ₙ Fⁿ S)` of the free algebra on `S`
(`CategoryTheory.Adjunction.freeComparison` for the free–forgetful adjunctions and
`IsoAlgebra.mapOfNatIsoCompForgetIso e`); on the summand `n` it is the iterated exchange
isomorphism `Gⁿ (L S) ≅ L (Fⁿ S)` followed by `L` of the inclusion of `Fⁿ S`. Hence it is an
isomorphism as soon as `L` preserves the coproduct `∐ₙ Fⁿ S`
(`CategoryTheory.Endofunctor.IsoAlgebra.isIso_freeComparison_mapOfNatIso`).
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C D : Type*} [Category C] [Category D] {F : C ⥤ C} [F.IsEquivalence] {G : D ⥤ D}
  [G.IsEquivalence] [HasColimitsOfShape (Discrete ℤ) C] [HasColimitsOfShape (Discrete ℤ) D]
  {L : C ⥤ D} (e : L ⋙ G ≅ F ⋙ L)

omit [HasColimitsOfShape (Discrete ℤ) D] in
/-- On the summands, the morphism `∐ₙ Gⁿ (L S) ⟶ L (∐ₙ Fⁿ S)` induced by `L` of the inclusion of
`S` is an isomorphism `Gⁿ (L S) ≅ L (Fⁿ S)` followed by `L` of the inclusion of `Fⁿ S`. -/
lemma exists_iso_free_hom_eq (S : C) (n : ℤ) :
    ∃ φ : Free.obj G (L.obj S) n ≅ L.obj (Free.obj F S n),
      Free.hom ((mapOfNatIso e).obj (Free.algebra F S)) (L.map (Sigma.ι (Free.obj F S) 0)) n =
        φ.hom ≫ L.map (Sigma.ι (Free.obj F S) n) := by
  set K := (mapOfNatIso e).obj (Free.algebra F S)
  set s := L.map (Sigma.ι (Free.obj F S) 0)
  have hK : K.str.hom = e.hom.app _ ≫ L.map (Free.str F S).hom := by
    simp [K, Free.algebra]
  have key (m : ℤ) (φ : Free.obj G (L.obj S) m ≅ L.obj (Free.obj F S m)) :
      G.map (φ.hom ≫ L.map (Sigma.ι (Free.obj F S) m)) ≫ K.str.hom =
        (G.mapIso φ ≪≫ e.app _ ≪≫ L.mapIso (Free.objSucc F S m)).hom ≫
          L.map (Sigma.ι (Free.obj F S) (m + 1)) := by
    have := e.hom.naturality (Sigma.ι (Free.obj F S) m)
    dsimp at this
    simp only [hK, Functor.map_comp, Category.assoc, Iso.trans_hom, Functor.mapIso_hom,
      Iso.app_hom]
    rw [reassoc_of% this, ← L.map_comp, ← L.map_comp, Free.map_ι_comp_str]
  have up (m : ℤ) (φ : Free.obj G (L.obj S) m ≅ L.obj (Free.obj F S m))
      (hφ : Free.hom K s m = φ.hom ≫ L.map (Sigma.ι (Free.obj F S) m)) :
      ∃ ψ : Free.obj G (L.obj S) (m + 1) ≅ L.obj (Free.obj F S (m + 1)),
        Free.hom K s (m + 1) = ψ.hom ≫ L.map (Sigma.ι (Free.obj F S) (m + 1)) := by
    refine ⟨(Free.objSucc G (L.obj S) m).symm ≪≫ G.mapIso φ ≪≫ e.app _ ≪≫
      L.mapIso (Free.objSucc F S m), ?_⟩
    rw [← cancel_epi (Free.objSucc G (L.obj S) m).hom, ← Free.map_hom_comp_str, hφ, key]
    simp
  have down (m m' : ℤ) (hm : m + 1 = m') (φ : Free.obj G (L.obj S) m' ≅ L.obj (Free.obj F S m'))
      (hφ : Free.hom K s m' = φ.hom ≫ L.map (Sigma.ι (Free.obj F S) m')) :
      ∃ ψ : Free.obj G (L.obj S) m ≅ L.obj (Free.obj F S m),
        Free.hom K s m = ψ.hom ≫ L.map (Sigma.ι (Free.obj F S) m) := by
    subst hm
    refine ⟨G.preimageIso (Free.objSucc G (L.obj S) m ≪≫ φ ≪≫
      L.mapIso (Free.objSucc F S m).symm ≪≫ (e.app _).symm), ?_⟩
    apply G.map_injective
    rw [← cancel_mono K.str.hom, Free.map_hom_comp_str, hφ, key]
    simp
    rfl
  exact Int.induction_on n ⟨Iso.refl _, by simp [s]⟩ (fun m ⟨φ, hφ⟩ ↦ up m φ hφ)
    (fun m ⟨φ, hφ⟩ ↦ down _ _ (by omega) φ hφ)

/-- The comparison `∐ₙ Gⁿ (L S) ⟶ L (∐ₙ Fⁿ S)` of the free algebras is the morphism of algebras
induced by `L` of the inclusion of `S`. -/
lemma freeComparison_mapOfNatIso (S : C) :
    Adjunction.freeComparison (Free.adjunction F) (Free.adjunction G) (mapOfNatIso e) L
      (mapOfNatIsoCompForgetIso e) S =
        Free.desc ((mapOfNatIso e).obj (Free.algebra F S)) (L.map (Sigma.ι (Free.obj F S) 0)) := by
  refine Free.hom_ext ?_
  simp only [Adjunction.freeComparison, Free.adjunction, mapOfNatIsoCompForgetIso,
    Adjunction.mkOfHomEquiv_homEquiv, Equiv.symm_mk, Adjunction.mkOfHomEquiv_unit_app,
    Equiv.coe_fn_mk, id_hom_f, Iso.refl_inv, NatTrans.id_app, Free.ι_desc_hom_f]
  exact (Category.comp_id _).trans (congrArg L.map (Category.comp_id _))

/-- **Free algebras commute with transport along a functor preserving their coproducts.** If `L`
preserves the coproduct `∐ₙ Fⁿ S`, the comparison `∐ₙ Gⁿ (L S) ⟶ L (∐ₙ Fⁿ S)` of the free
algebras is an isomorphism. -/
theorem isIso_freeComparison_mapOfNatIso (S : C)
    [PreservesColimit (Discrete.functor (Free.obj F S)) L] :
    IsIso (Adjunction.freeComparison (Free.adjunction F) (Free.adjunction G) (mapOfNatIso e) L
      (mapOfNatIsoCompForgetIso e) S) := by
  choose φ hφ using exists_iso_free_hom_eq e S
  rw [← isIso_iff_of_reflects_iso _ (forget G)]
  have h : (forget G).map (Adjunction.freeComparison (Free.adjunction F) (Free.adjunction G)
      (mapOfNatIso e) L (mapOfNatIsoCompForgetIso e) S) =
        Limits.Sigma.map (fun n ↦ (φ n).hom) ≫ sigmaComparison L (Free.obj F S) := by
    refine Sigma.hom_ext _ _ fun n ↦ ?_
    rw [forget_map, Sigma.ι_map_assoc, ι_comp_sigmaComparison, ← hφ]
    rw [freeComparison_mapOfNatIso]
    exact Sigma.ι_comp_desc _ n
  rw [h]
  infer_instance

end CategoryTheory.Endofunctor.IsoAlgebra
