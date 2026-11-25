/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.RankOneLocal
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ClosedImmersion
public import WeilConjectures.SixFunctors.Etale.SupportCohomologyRestriction

/-!
# The cup product with closed supports, through the coefficient sheaves of the supports

Let `i : Z ⟶ X` and `k : W ⟶ X` be closed immersions and `h : V ⟶ X` a closed immersion onto
`Z ∩ W` (for instance `Z ×_X W`). Reading a class of `H^a_Z(X, F)` as a morphism
`i_* Λ_Z ⟶ F[a]` (`AlgebraicGeometry.Etale.derivedSupportCohomologyAddEquiv`, blueprint
`lemma-sections-support-closed-subscheme--1`), the supported cup product of `α ∈ H^a_Z(X, F)` and
`β ∈ H^b_W(X, G)` is

`h_* Λ_V ≅ i_* Λ_Z ⊗ᴸ k_* Λ_W ⟶ F[a] ⊗ᴸ G[b] ≅ (F ⊗ᴸ G)[a + b]`,

read in `H^{a+b}_{Z ∩ W}(X, F ⊗ᴸ G)` (`AlgebraicGeometry.Etale.cupSupportCohomology`).

The identification `h_* Λ_V ≅ i_* Λ_Z ⊗ᴸ k_* Λ_W`
(`AlgebraicGeometry.Etale.lowerStarConstantTensorIso`) is obtained without stalks. Write
`ηᵢ : Λ_X ⟶ i_* Λ_Z` and `η_k : Λ_X ⟶ k_* Λ_W` for the units. The map
`ηᵢ ⊗ η_k : Λ_X ⟶ i_* Λ_Z ⊗ᴸ k_* Λ_W` becomes invertible after `Lh^*`, since `h` factors through
`i` and through `k` and `Li^* ηᵢ`, `Lk^* η_k` are invertible; and its target vanishes on the
complement of `Z ∩ W`, being a tensor product of objects vanishing on the complements of `Z` and
of `W`. By the open–closed triangle the unit of `Lh^* ⊣ Rh_*` at the target is then invertible,
which gives `Rh_* Λ_V ≅ Rh_* Lh^* Λ_X ≅ i_* Λ_Z ⊗ᴸ k_* Λ_W`.

## Main definitions

- `AlgebraicGeometry.Etale.lowerStarConstantTensorIso`
- `AlgebraicGeometry.Etale.cupSupportedHom`, `AlgebraicGeometry.Etale.cupSupportCohomology`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

-- the exceptional adjunction of a closed immersion is that of `i_* ⊣ i^!`, not the general one
attribute [local instance 2000] isLeftAdjoint_rightDerivedLowerShriek_of_isClosedImmersion

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  {X Z W V : Scheme.{u}} (i : Z ⟶ X) (k : W ⟶ X) (h : V ⟶ X)
  [IsClosedImmersion i] [IsClosedImmersion k] [IsClosedImmersion h]
  (p : V ⟶ Z) (q : V ⟶ W) (hp : p ≫ i = h) (hq : q ≫ k = h)
  (hr : Set.range h.base = Set.range i.base ∩ Set.range k.base)

/-- The unit `Λ_X ⟶ Ri_! Λ_Z` of a closed immersion `i`: the unit of `Li^* ⊣ Ri_*`, read through
`Li^* Λ_X ≅ Λ_Z` and `Ri_! ≅ Ri_*`. -/
noncomputable def constantComplexToLowerShriek :
    constantComplex Λ X ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z) :=
  (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app (constantComplex Λ X) ≫
    (R((i)_*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarConstantComplexIso Λ i).hom ≫
    ((rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) i).app _).inv

omit [Finite Λ] [IsClosedImmersion h] in
include hp in
/-- The unit `Λ_X ⟶ Ri_! Λ_Z` becomes invertible after pulling back along a morphism `h`
factoring through `i`. -/
lemma isIso_leftDerivedUpperStar_map_constantComplexToLowerShriek :
    IsIso ((L((h)^*[ModuleCat.{u + 1} Λ])).map (constantComplexToLowerShriek Λ i)) := by
  have := isIso_leftDerivedUpperStar_map_unit_of_isClosedImmersion (ModuleCat.{u + 1} Λ) i
    (constantComplex Λ X)
  have : IsIso ((L((i)^*[ModuleCat.{u + 1} Λ])).map (constantComplexToLowerShriek Λ i)) := by
    rw [constantComplexToLowerShriek, Functor.map_comp, Functor.map_comp]
    infer_instance
  exact (NatIso.isIso_map_iff (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) p i h hp.symm)
    (constantComplexToLowerShriek Λ i)).2
    (inferInstanceAs (IsIso ((L((p)^*[ModuleCat.{u + 1} Λ])).map
      ((L((i)^*[ModuleCat.{u + 1} Λ])).map (constantComplexToLowerShriek Λ i)))))

/-- The tensor product `Ri_! Λ_Z ⊗ᴸ Rk_! Λ_W` of the coefficient objects of two supports. -/
noncomputable abbrev lowerShriekConstantTensor :
    _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
    ((R(i)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z))).obj
      ((R(k)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ W))

/-- The map `ηᵢ ⊗ η_k : Λ_X ≅ Λ_X ⊗ᴸ Λ_X ⟶ Ri_! Λ_Z ⊗ᴸ Rk_! Λ_W`. -/
noncomputable def constantComplexToLowerShriekConstantTensor :
    constantComplex Λ X ⟶ lowerShriekConstantTensor Λ i k :=
  (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) X (constantComplex Λ X)).inv ≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).map (constantComplexToLowerShriek Λ i)).app _ ≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj _).map (constantComplexToLowerShriek Λ k)

omit [Finite Λ] [IsClosedImmersion h] in
include hp hq in
lemma isIso_leftDerivedUpperStar_map_constantComplexToLowerShriekConstantTensor :
    IsIso ((L((h)^*[ModuleCat.{u + 1} Λ])).map
      (constantComplexToLowerShriekConstantTensor Λ i k)) := by
  have := isIso_leftDerivedUpperStar_map_derivedTensor_map_app (ModuleCat.{u + 1} Λ) h
    (constantComplexToLowerShriek Λ i) (constantComplex Λ X)
    (isIso_leftDerivedUpperStar_map_constantComplexToLowerShriek Λ i h p hp)
  have := isIso_leftDerivedUpperStar_map_derivedTensor_obj_map (ModuleCat.{u + 1} Λ) h
    ((R(i)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z)) (constantComplexToLowerShriek Λ k)
    (isIso_leftDerivedUpperStar_map_constantComplexToLowerShriek Λ k h q hq)
  rw [constantComplexToLowerShriekConstantTensor, Functor.map_comp, Functor.map_comp]
  infer_instance

include hr in
/-- `Ri_! Λ_Z ⊗ᴸ Rk_! Λ_W` vanishes on the open complement of `Z ∩ W`: its restriction to that
complement vanishes on the complements of `Z` and of `W`, which cover it. -/
lemma isZero_leftDerivedUpperStar_openComplement_lowerShriekConstantTensor :
    IsZero ((L((h.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).obj
      (lowerShriekConstantTensor Λ i k)) := by
  set j := h.openComplement.ι
  have hcd : Disjoint (Set.range (pullback.snd i j)) (Set.range (pullback.snd k j)) := by
    rw [Scheme.Pullback.range_snd, Scheme.Pullback.range_snd, Set.disjoint_left]
    intro x hx₁ hx₂
    apply x.2
    rw [hr]
    exact ⟨hx₁, hx₂⟩
  refine isZero_of_isZero_leftDerivedUpperStar_of_disjoint Λ
    (pullback.snd i j) (pullback.snd k j) _ _ (Scheme.Hom.range_eq_compl_range_openComplement_ι _)
    (Scheme.Hom.range_eq_compl_range_openComplement_ι _) hcd ?_ ?_
  · refine IsZero.of_iso ?_ ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) _ j).app _).symm
    exact (isZero_derivedTensor_obj_obj_of_isZero_left
      (isZero_leftDerivedUpperStar_openComplement_comp_obj_rightDerivedLowerShriek
        (ModuleCat.{u + 1} Λ) i j _) _).of_iso
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) _ _ _)
  · refine IsZero.of_iso ?_ ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) _ j).app _).symm
    exact (isZero_derivedTensor_obj_obj_of_isZero_right _
      (isZero_leftDerivedUpperStar_openComplement_comp_obj_rightDerivedLowerShriek
        (ModuleCat.{u + 1} Λ) k j _)).of_iso
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) _ _ _)

include hr in
/-- The unit `T ⟶ Rh_* Lh^* T` at `T = Ri_! Λ_Z ⊗ᴸ Rk_! Λ_W` is an isomorphism, `T` vanishing on
the open complement of `h` (open–closed triangle). -/
lemma isIso_mapDerivedUpperStarLowerStarAdjunction_unit_app_lowerShriekConstantTensor :
    IsIso ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).unit.app
      (lowerShriekConstantTensor Λ i k)) := by
  set j := h.openComplement.ι
  obtain ⟨w, hT⟩ := exists_distTriang_openClosed (ModuleCat.{u + 1} Λ) j h
    h.range_eq_compl_range_openComplement_ι (lowerShriekConstantTensor Λ i k)
  have h₁ : IsZero (D((j)_!open[ModuleCat.{u + 1} Λ]).obj
      (D((j)^*[ModuleCat.{u + 1} Λ]).obj (lowerShriekConstantTensor Λ i k))) :=
    D((j)_!open[ModuleCat.{u + 1} Λ]).map_isZero
      ((isZero_leftDerivedUpperStar_openComplement_lowerShriekConstantTensor Λ i k h hr).of_iso
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j).app _).symm)
  exact (Triangle.isZero₁_iff_isIso₂ _ hT).1 h₁

/-- The identification `Rh_! Λ_V ≅ Ri_! Λ_Z ⊗ᴸ Rk_! Λ_W` for a closed immersion `h` onto `Z ∩ W`
factoring through `i` and `k`: `Rh_! Λ_V ≅ Rh_* Lh^* Λ_X`, then `Rh_* Lh^*` of the map
`ηᵢ ⊗ η_k : Λ_X ⟶ Ri_! Λ_Z ⊗ᴸ Rk_! Λ_W`, which `Lh^*` inverts, followed by the inverse of the unit
of `Lh^* ⊣ Rh_*` at the target, which is invertible since the target is supported on `Z ∩ W`. -/
noncomputable def lowerShriekConstantTensorIso :
    (R(h)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ V) ≅ lowerShriekConstantTensor Λ i k :=
  haveI := isIso_leftDerivedUpperStar_map_constantComplexToLowerShriekConstantTensor Λ i k h p q
    hp hq
  haveI := isIso_mapDerivedUpperStarLowerStarAdjunction_unit_app_lowerShriekConstantTensor Λ i k h
    hr
  (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) h).app _ ≪≫
    (R((h)_*[ModuleCat.{u + 1} Λ])).mapIso (leftDerivedUpperStarConstantComplexIso Λ h).symm ≪≫
    (R((h)_*[ModuleCat.{u + 1} Λ])).mapIso
      (asIso ((L((h)^*[ModuleCat.{u + 1} Λ])).map
        (constantComplexToLowerShriekConstantTensor Λ i k)) ≪≫
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) h).app _) ≪≫
    (asIso ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).unit.app
      (lowerShriekConstantTensor Λ i k))).symm

/-- The coefficient sheaf `i_* Λ_Z` of a support, placed in degree `0`. -/
noncomputable abbrev lowerStarConstant (i : Z ⟶ X) :
    _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (_root_.DerivedCategory.singleFunctor _ 0).obj ((i)_*[ModuleCat.{u + 1} Λ].obj
    ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)))

/-- Blueprint `proposition-purity-vector-bundles`: Cup product with closed supports (the
identification of the coefficient sheaves)

For closed immersions `i : Z ⟶ X`, `k : W ⟶ X` and a closed immersion `h : V ⟶ X` onto `Z ∩ W`
factoring through both (for instance `V = Z ×_X W`), the identification
`h_* Λ_V ≅ i_* Λ_Z ⊗ᴸ k_* Λ_W` of the coefficient sheaves, the sheaves being placed in degree
`0` (`AlgebraicGeometry.Etale.lowerShriekConstantTensorIso`, read through
`Ri_! Λ_Z ≅ i_* Λ_Z`, `AlgebraicGeometry.Etale.rightDerivedLowerShriekConstantComplexIso`). -/
noncomputable def lowerStarConstantTensorIso :
    lowerStarConstant Λ h ≅ ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
      (lowerStarConstant Λ i)).obj (lowerStarConstant Λ k) :=
  (rightDerivedLowerShriekConstantComplexIso Λ h).symm ≪≫
    lowerShriekConstantTensorIso Λ i k h p q hp hq hr ≪≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).mapIso
      (rightDerivedLowerShriekConstantComplexIso Λ i)).app _ ≪≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj _).mapIso
      (rightDerivedLowerShriekConstantComplexIso Λ k)

/-- Blueprint `proposition-purity-vector-bundles`: Cup product with closed supports (on morphisms)

For classes represented by morphisms `α : i_* Λ_Z ⟶ F[a]` and `β : k_* Λ_W ⟶ G[b]`
(`lemma-sections-support-closed-subscheme--1`), their supported cup product is the morphism

`h_* Λ_V ≅ i_* Λ_Z ⊗ᴸ k_* Λ_W ⟶ F[a] ⊗ᴸ G[b] ≅ (F ⊗ᴸ G)[a + b]`,

the first identification being `AlgebraicGeometry.Etale.lowerStarConstantTensorIso` and the
last the shift compatibility of the derived tensor product. -/
noncomputable def cupSupportedHom
    {F G : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} {a b : ℤ}
    (α : lowerStarConstant Λ i ⟶ F⟦a⟧) (β : lowerStarConstant Λ k ⟶ G⟦b⟧) :
    lowerStarConstant Λ h ⟶ (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj F).obj G)⟦a + b⟧ :=
  (lowerStarConstantTensorIso Λ i k h p q hp hq hr).hom ≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).map α).app _ ≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj _).map β ≫
    (derivedTensorShiftIso (ModuleCat.{u + 1} Λ) F G a b).hom

/-- Blueprint `proposition-purity-vector-bundles`: Cup product with closed supports

Let `i : Z ⟶ X` and `k : W ⟶ X` be closed immersions and `h : V ⟶ X` a closed immersion onto
`Z ∩ W` factoring through both (for instance `h : Z ×_X W ⟶ X`,
`AlgebraicGeometry.Etale.cupSupportCohomologyPullback`). For `α ∈ H^a_Z(X, F)` and
`β ∈ H^b_W(X, G)`, represented by morphisms `i_* Λ_Z ⟶ F[a]` and `k_* Λ_W ⟶ G[b]`
(`AlgebraicGeometry.Etale.derivedSupportCohomologyAddEquiv`,
`lemma-sections-support-closed-subscheme--1`), their
*supported cup product* is the morphism

`h_* Λ_V ≅ i_* Λ_Z ⊗ᴸ k_* Λ_W ⟶ (F ⊗ᴸ G)[a + b]`

(`AlgebraicGeometry.Etale.cupSupportedHom`), read as an element of
`H^{a+b}_{Z ∩ W}(X, F ⊗ᴸ G)`. As throughout the purity chapter (`def-pur-conventions`) this is
the étale form. The cup product of classes in the model `Λ_X ⟶ Ri_! Ri^! M` is
`AlgebraicGeometry.Etale.cupWithSupports`. -/
noncomputable def cupSupportCohomology
    {F G : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} {a b : ℤ}
    (α : (derivedSupportCohomology (ModuleCat.{u + 1} Λ) i a).obj F)
    (β : (derivedSupportCohomology (ModuleCat.{u + 1} Λ) k b).obj G) :
    (derivedSupportCohomology (ModuleCat.{u + 1} Λ) h (a + b)).obj
      (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj F).obj G) :=
  (derivedSupportCohomologyAddEquiv Λ h _ (a + b)).symm
    (cupSupportedHom Λ i k h p q hp hq hr (derivedSupportCohomologyAddEquiv Λ i F a α)
      (derivedSupportCohomologyAddEquiv Λ k G b β))

omit [IsClosedImmersion h] in
/-- Blueprint `proposition-purity-vector-bundles`: Cup product with closed supports (for `Z ×_X W`)

The supported cup product `H^a_Z(X, F) × H^b_W(X, G) ⟶ H^{a+b}_{Z ×_X W}(X, F ⊗ᴸ G)` of
`AlgebraicGeometry.Etale.cupSupportCohomology` for `h : Z ×_X W ⟶ X`. -/
noncomputable def cupSupportCohomologyPullback
    {F G : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} {a b : ℤ}
    (α : (derivedSupportCohomology (ModuleCat.{u + 1} Λ) i a).obj F)
    (β : (derivedSupportCohomology (ModuleCat.{u + 1} Λ) k b).obj G) :
    (derivedSupportCohomology (ModuleCat.{u + 1} Λ) (pullback.fst i k ≫ i) (a + b)).obj
      (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj F).obj G) :=
  cupSupportCohomology Λ i k (pullback.fst i k ≫ i) (pullback.fst i k) (pullback.snd i k) rfl
    pullback.condition.symm (by rw [Scheme.Pullback.range_fst_comp]) α β

end Etale

end AlgebraicGeometry
