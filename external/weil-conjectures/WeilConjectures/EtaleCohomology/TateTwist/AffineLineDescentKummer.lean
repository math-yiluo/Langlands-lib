/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.TateTwist.AffineLineDescent

/-!
# Descent of the degree-zero and degree-one computations on `𝔾ₘ`

The degree-zero and degree-one computations of blueprint `sk-prop-a1-kummer` for the twist
`Λ(1) = μₙ ⊗ Λ`, in the form of `WeilConjectures.EtaleCohomology.Purity.Smooth.GmRelativeKummer`
(for `π = j ≫ p` with `j : G ⟶ 𝔸¹_B` an open complement of the zero section), over a base `B`
separated and locally of finite type over an arbitrary field `k`:

* the unit `Λ_B(1) ⟶ Rp_* Lp^* Λ_B(1)` of `p : 𝔸¹_B ⟶ B` is an isomorphism
  (`AlgebraicGeometry.Etale.isIso_unit_tateObject_affineLine_of_field`);
* the unit `Λ_B(1) ⟶ Rπ_* Lπ^* Λ_B(1)` is an isomorphism on `H⁰`
  (`AlgebraicGeometry.Etale.isIso_homology_zero_unit_tateObject_multiplicativeGroup_of_field`);
* for every `β : Lπ^* Λ_B ≅ Λ_G`, the adjoint `Λ_B ⟶ Rπ_*(Λ(1)[1])` of the Kummer class `κ(t)`
  is an isomorphism on `H⁰`
  (`AlgebraicGeometry.Etale.isIso_homology_zero_homEquiv_kummerClass_of_field`).

As in `WeilConjectures.EtaleCohomology.TateTwist.AffineLineDescent`, these are reduced to the
case of an algebraically closed field and a quasi-compact base by base change to the affine
opens of `B` and to an algebraic closure of `k`, along which isomorphisms of cohomology sheaves
descend. The compatibility of the units and of the Kummer classes with base change is the one
used in the proof of
`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_app_tateObject_multiplicativeGroup`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Isomorphisms between cohomology sheaves in a given degree descend along a jointly surjective
family of morphisms `u_i : U_i ⟶ X`: the pullbacks commute with the cohomology sheaves. -/
theorem isIso_homology_map_of_jointlySurjective {X : Scheme.{u}} {ι : Type u}
    {U : ι → Scheme.{u}} (u : ∀ i, U i ⟶ X) (hu : ∀ x : X, ∃ (i : ι) (y : U i), (u i).base y = x)
    {M N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : M ⟶ N) (n : ℤ)
    (h : ∀ i, IsIso ((_root_.DerivedCategory.homologyFunctor _ n).map
      ((L((u i)^*[ModuleCat.{u + 1} Λ])).map φ))) :
    IsIso ((_root_.DerivedCategory.homologyFunctor _ n).map φ) :=
  Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} Λ) u hu _ fun i ↦
    (NatIso.isIso_map_iff (leftDerivedUpperStarHomologyFunctorIso _ (u i) n) φ).2 (h i)

/-- Base change of units on cohomology sheaves: for a commutative square with derived base
change map `BC : Lg^* Rf_* ⟶ Rf'_* Lg'^*` invertible at `Lf^* M`, and an identification
`Lg^* M ≅ M'`, if the unit `M' ⟶ Rf'_* Lf'^* M'` is an isomorphism on `Hⁿ`, then so is the
pullback along `g` of the unit `M ⟶ Rf_* Lf^* M`. -/
lemma isIso_homology_map_leftDerivedUpperStar_unit_app {X Y X' Y' : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g)
    (M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    {M' : _root_.DerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (e : (L((g)^*[ModuleCat.{u + 1} Λ])).obj M ≅ M') (n : ℤ)
    (hBC : IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq).app
      ((L((f)^*[ModuleCat.{u + 1} Λ])).obj M)))
    (h' : IsIso ((_root_.DerivedCategory.homologyFunctor _ n).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f').unit.app M'))) :
    IsIso ((_root_.DerivedCategory.homologyFunctor _ n).map
      ((L((g)^*[ModuleCat.{u + 1} Λ])).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app M))) := by
  let H := _root_.DerivedCategory.homologyFunctor (Sheaf Y'.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)) n
  have hu := map_unit_derivedBaseChangeMap_app (ModuleCat.{u + 1} Λ) sq M
  have : IsIso (H.map ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f').unit.app
      ((L((g)^*[ModuleCat.{u + 1} Λ])).obj M))) :=
    (NatTrans.isIso_app_iff_of_iso (Functor.whiskerRight (derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} Λ) f').unit H) e).2 h'
  have : IsIso (H.map ((L((g)^*[ModuleCat.{u + 1} Λ])).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app M)) ≫
      H.map ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq).app _)) := by
    rw [← Functor.map_comp, hu, Functor.map_comp]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (H.map ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq).app _))

variable [NeZero (ringChar Λ)]

section Pullback

variable {B B' G G' : Scheme.{u}} (g : B' ⟶ B)
  (j : G ⟶ 𝔸(ULift.{u} (Fin 1); B)) [IsOpenImmersion j]
  (j' : G' ⟶ 𝔸(ULift.{u} (Fin 1); B')) [IsOpenImmersion j']
  (hj : Set.range j.base = (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B).base)ᶜ)
  (hj' : Set.range j'.base =
    (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B').base)ᶜ)
  [HasInvertibleExponent Λ B] [HasInvertibleExponent Λ B'] [HasInvertibleExponent Λ G]
  [HasInvertibleExponent Λ G']

omit [HasInvertibleExponent Λ G'] in
/-- Base change of the degree-zero clause: for `g : B' ⟶ B` with base change
`G' ⟶ G` of the complements of the zero sections, if the derived base change map of
`π : G ⟶ B` along `g` is an isomorphism at `Λ_G(1)` and the unit
`Λ_{B'}(1) ⟶ Rπ'_* Lπ'^* Λ_{B'}(1)` is an isomorphism on `H⁰`, then so is the pullback along
`g` of the unit `Λ_B(1) ⟶ Rπ_* Lπ^* Λ_B(1)`. -/
lemma isIso_homology_zero_map_leftDerivedUpperStar_unit_tateObject
    (hBC : IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
      (AffineSpace.isPullback_complementMap_over g j j' hj hj').toCommSq).app
        (tateObject Λ G 1)))
    (h' : IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
        (j' ≫ 𝔸(ULift.{u} (Fin 1); B') ↘ B')).unit.app (tateObject Λ B' 1)))) :
    IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      ((L((g)^*[ModuleCat.{u + 1} Λ])).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
          (j ≫ 𝔸(ULift.{u} (Fin 1); B) ↘ B)).unit.app (tateObject Λ B 1)))) :=
  isIso_homology_map_leftDerivedUpperStar_unit_app Λ
    (AffineSpace.isPullback_complementMap_over g j j' hj hj').toCommSq _
    (leftDerivedUpperStarTateObjectIso g 1) 0
    ((NatTrans.isIso_app_iff_of_iso _ (leftDerivedUpperStarTateObjectIso _ 1)).2 hBC) h'

-- the composites of derived functors between the derived categories of the two bases are large
omit [HasInvertibleExponent Λ B] [HasInvertibleExponent Λ B'] in
/-- Base change of the degree-one clause: for `g : B' ⟶ B` with base change `q : G' ⟶ G` of
the complements of the zero sections, if the derived base change map of `π : G ⟶ B` along `g`
is an isomorphism at `Λ_G(1)` and, for every identification `β' : Lπ'^* Λ_{B'} ≅ Λ_{G'}`, the
adjoint `Λ_{B'} ⟶ Rπ'_*(Λ(1)[1])` of the Kummer class `κ(t')` is an isomorphism on `H⁰`, then
the pullback along `g` of the adjoint `Λ_B ⟶ Rπ_*(Λ(1)[1])` of `κ(t)` is an isomorphism on
`H⁰`, for every identification `β : Lπ^* Λ_B ≅ Λ_G`. -/
lemma isIso_homology_zero_map_leftDerivedUpperStar_homEquiv_kummerClass [Finite Λ]
    (hBC : IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
      (AffineSpace.isPullback_complementMap_over g j j' hj hj').toCommSq).app
        (tateObject Λ G 1)))
    (h' : ∀ β' : (L((j' ≫ 𝔸(ULift.{u} (Fin 1); B') ↘ B')^*[ModuleCat.{u + 1} Λ])).obj
        (constantComplex Λ B') ≅ constantComplex Λ G',
      IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
          (j' ≫ 𝔸(ULift.{u} (Fin 1); B') ↘ B')).homEquiv _ _
            (β'.hom ≫ kummerClass Λ (AffineSpace.unitLineCoord j' hj')))))
    (β : (L((j ≫ 𝔸(ULift.{u} (Fin 1); B) ↘ B)^*[ModuleCat.{u + 1} Λ])).obj
        (constantComplex Λ B) ≅ constantComplex Λ G) :
    IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      ((L((g)^*[ModuleCat.{u + 1} Λ])).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
          (j ≫ 𝔸(ULift.{u} (Fin 1); B) ↘ B)).homEquiv _ _
            (β.hom ≫ kummerClass Λ (AffineSpace.unitLineCoord j hj))))) := by
  let π' := j' ≫ 𝔸(ULift.{u} (Fin 1); B') ↘ B'
  let q := AffineSpace.complementMap g j j' hj hj'
  let sq := (AffineSpace.isPullback_complementMap_over g j j' hj hj').toCommSq
  let BC := derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq
  let K := tateObject Λ G 1
  let H := _root_.DerivedCategory.homologyFunctor (Sheaf B'.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)) 0
  let θq := leftDerivedUpperStarConstantComplexIso Λ q
  let θg := leftDerivedUpperStarConstantComplexIso Λ g
  let κ := kummerClass Λ (AffineSpace.unitLineCoord j hj)
  let κ' := kummerClass Λ (AffineSpace.unitLineCoord j' hj')
  have hmate := derivedBaseChangeMap_app_homEquiv Λ sq (β.hom ≫ κ)
  -- `Lq^* κ(t) = κ(t')` up to isomorphisms
  let C := ((L((q)^*[ModuleCat.{u + 1} Λ])).commShiftIso (1 : ℤ)).app (tateObject Λ G 1) ≪≫
    (shiftFunctor _ (1 : ℤ)).mapIso (leftDerivedUpperStarTateObjectIso q 1)
  have hnat : (L((q)^*[ModuleCat.{u + 1} Λ])).map κ = θq.hom ≫ κ' ≫ C.inv := by
    rw [← Category.assoc, Iso.eq_comp_inv]
    exact leftDerivedUpperStar_map_kummerClass_coord Λ (g := g) (j := j) (hj := hj) (j' := j')
      (hj' := hj')
  let A := (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).app (constantComplex Λ B) ≪≫
    (L((q)^*[ModuleCat.{u + 1} Λ])).mapIso β ≪≫ θq
  let Bι := (L((π')^*[ModuleCat.{u + 1} Λ])).mapIso θg.symm ≪≫ A
  have hR : (L((g)^*[ModuleCat.{u + 1} Λ])).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
          (j ≫ 𝔸(ULift.{u} (Fin 1); B) ↘ B)).homEquiv _ _ (β.hom ≫ κ)) ≫ BC.app (K⟦(1 : ℤ)⟧) =
      θg.hom ≫ (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) π').homEquiv _ _
        (Bι.hom ≫ κ') ≫ (R((π')_*[ModuleCat.{u + 1} Λ])).map C.inv := by
    rw [hmate, ← Adjunction.homEquiv_naturality_right, ← Adjunction.homEquiv_naturality_left]
    congr 1
    simp only [Bι, A, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom,
      Category.assoc, Functor.map_comp]
    rw [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
    exact congrArg (fun f ↦ (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom.app
      (constantComplex Λ B) ≫ (L((q)^*[ModuleCat.{u + 1} Λ])).map β.hom ≫ f) hnat
  have : IsIso (BC.app (K⟦(1 : ℤ)⟧)) := by
    rw [NatTrans.app_shift BC (1 : ℤ) K]
    infer_instance
  have := h' Bι
  have : IsIso (H.map ((L((g)^*[ModuleCat.{u + 1} Λ])).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
          (j ≫ 𝔸(ULift.{u} (Fin 1); B) ↘ B)).homEquiv _ _ (β.hom ≫ κ))) ≫
      H.map (BC.app (K⟦(1 : ℤ)⟧))) := by
    rw [← Functor.map_comp, hR, Functor.map_comp, Functor.map_comp]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (H.map (BC.app (K⟦(1 : ℤ)⟧)))

end Pullback

section AlgClosed

variable [Finite Λ] {k : Type u} [Field k] [IsAlgClosed k]
  [HasInvertibleExponent Λ (Spec (.of k))] {Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
  [IsSeparated aY] [LocallyOfFiniteType aY] [HasInvertibleExponent Λ Y]
  {G : Scheme.{u}} (j : G ⟶ 𝔸(ULift.{u} (Fin 1); Y)) [IsOpenImmersion j]
  (hj : Set.range j.base = (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y).base)ᶜ)
  [HasInvertibleExponent Λ G]

include aY in
/-- Over an algebraically closed field and for `Y` quasi-compact: for every identification
`β : Lπ^* Λ_Y ≅ Λ_G`, the adjoint `Λ_Y ⟶ Rπ_*(Λ(1)[1])` of the Kummer class `κ(t)` is an
isomorphism on `H⁰`. This is `AlgebraicGeometry.Etale.isIso_homology_zero_kummerClassAdjoint`
for an arbitrary identification `β`. -/
theorem isIso_homology_zero_homEquiv_kummerClass_of_quasiCompact [QuasiCompact aY]
    (β : (L((j ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)^*[ModuleCat.{u + 1} Λ])).obj
        (constantComplex Λ Y) ≅ constantComplex Λ G) :
    IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
        (j ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).homEquiv _ _
          (β.hom ≫ kummerClass Λ (AffineSpace.unitLineCoord j hj)))) := by
  let j₀ := (multiplicativeGroupModel k).ι
  have hj₀ := range_multiplicativeGroupModel_ι k
  have : HasInvertibleExponent Λ (multiplicativeGroupModel k) := .of_hom j₀
  exact isIso_homology_zero_kummerClassAdjoint_of_cohomology Λ aY
    (kummerClass_coord_smul_eq_zero Λ) j₀ hj₀
    (isZero_cohomology_multiplicativeGroup Λ j₀ hj₀)
    (nonempty_iso_cohomology_zero_multiplicativeGroup Λ j₀ hj₀).some
    (nonempty_iso_cohomology_one_multiplicativeGroup Λ j₀ hj₀).some j hj β

include aY hj in
/-- Over an algebraically closed field and without quasi-compactness assumption on `Y`: the
unit `Λ_Y(1) ⟶ Rπ_* Lπ^* Λ_Y(1)` of `π : G ⟶ 𝔸¹_Y ⟶ Y` is an isomorphism on `H⁰`. By étale
base change this may be checked on the affine opens of `Y`, where it is
`AlgebraicGeometry.Etale.isIso_homology_zero_unit_tateObject_multiplicativeGroup`. -/
theorem isIso_homology_zero_unit_tateObject_multiplicativeGroup_of_isAlgClosed :
    IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
        (j ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).unit.app (tateObject Λ Y 1))) := by
  refine isIso_homology_map_of_jointlySurjective Λ (fun V : Y.affineOpens ↦ V.1.ι)
    (fun x ↦ ?_) _ 0 fun V ↦ ?_
  · exact Y.exists_affineOpens_ι_eq x
  have : IsAffine V.1 := V.2
  have : QuasiCompact (V.1.ι ≫ aY) := inferInstance
  have : HasInvertibleExponent Λ V.1 := .of_hom V.1.ι
  let jV := (𝔸(ULift.{u} (Fin 1); V.1).basicOpen (AffineSpace.coord V.1 (ULift.up 0))).ι
  have hjV := AffineSpace.range_basicOpen_ι_coord V.1
  have : HasInvertibleExponent Λ
      (𝔸(ULift.{u} (Fin 1); V.1).basicOpen (AffineSpace.coord V.1 (ULift.up 0))) :=
    .of_hom (jV ≫ 𝔸(ULift.{u} (Fin 1); V.1) ↘ V.1)
  exact isIso_homology_zero_map_leftDerivedUpperStar_unit_tateObject Λ V.1.ι j jV hj hjV
    (isIso_derivedBaseChangeMap_app_tateObject_of_etale Λ
      (AffineSpace.isPullback_complementMap_over V.1.ι j jV hj hjV) 1)
    (isIso_homology_zero_unit_tateObject_multiplicativeGroup Λ (V.1.ι ≫ aY) jV hjV)

include aY in
/-- Over an algebraically closed field and without quasi-compactness assumption on `Y`: for
every identification `β : Lπ^* Λ_Y ≅ Λ_G`, the adjoint `Λ_Y ⟶ Rπ_*(Λ(1)[1])` of the Kummer
class `κ(t)` is an isomorphism on `H⁰`. By étale base change this may be checked on the affine
opens of `Y`, where it is
`AlgebraicGeometry.Etale.isIso_homology_zero_homEquiv_kummerClass_of_quasiCompact`. -/
theorem isIso_homology_zero_homEquiv_kummerClass_of_isAlgClosed
    (β : (L((j ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)^*[ModuleCat.{u + 1} Λ])).obj
        (constantComplex Λ Y) ≅ constantComplex Λ G) :
    IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
        (j ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).homEquiv _ _
          (β.hom ≫ kummerClass Λ (AffineSpace.unitLineCoord j hj)))) := by
  refine isIso_homology_map_of_jointlySurjective Λ (fun V : Y.affineOpens ↦ V.1.ι)
    (fun x ↦ ?_) _ 0 fun V ↦ ?_
  · exact Y.exists_affineOpens_ι_eq x
  have : IsAffine V.1 := V.2
  have : QuasiCompact (V.1.ι ≫ aY) := inferInstance
  have : HasInvertibleExponent Λ V.1 := .of_hom V.1.ι
  let jV := (𝔸(ULift.{u} (Fin 1); V.1).basicOpen (AffineSpace.coord V.1 (ULift.up 0))).ι
  have hjV := AffineSpace.range_basicOpen_ι_coord V.1
  have : HasInvertibleExponent Λ
      (𝔸(ULift.{u} (Fin 1); V.1).basicOpen (AffineSpace.coord V.1 (ULift.up 0))) :=
    .of_hom (jV ≫ 𝔸(ULift.{u} (Fin 1); V.1) ↘ V.1)
  exact isIso_homology_zero_map_leftDerivedUpperStar_homEquiv_kummerClass Λ V.1.ι j jV hj hjV
    (isIso_derivedBaseChangeMap_app_tateObject_of_etale Λ
      (AffineSpace.isPullback_complementMap_over V.1.ι j jV hj hjV) 1)
    (isIso_homology_zero_homEquiv_kummerClass_of_quasiCompact Λ (V.1.ι ≫ aY) jV hjV) β

omit [HasInvertibleExponent Λ G] in
include aY in
/-- Over an algebraically closed field and without quasi-compactness assumption on `Y`: the unit
`Λ_Y(1) ⟶ Rp_* Lp^* Λ_Y(1)` of the projection `p : 𝔸¹_Y ⟶ Y` is an isomorphism. By étale base
change this may be checked on the affine opens of `Y`, where it is
`AlgebraicGeometry.Etale.isIso_unit_tateObject_affineLine`. -/
theorem isIso_unit_tateObject_affineLine_of_isAlgClosed :
    IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
      (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).unit.app (tateObject Λ Y 1)) := by
  rw [_root_.DerivedCategory.isIso_iff]
  intro n
  refine isIso_homology_map_of_jointlySurjective Λ (fun V : Y.affineOpens ↦ V.1.ι)
    (fun x ↦ ?_) _ n fun V ↦ ?_
  · exact Y.exists_affineOpens_ι_eq x
  have : IsAffine V.1 := V.2
  have : QuasiCompact (V.1.ι ≫ aY) := inferInstance
  have : HasInvertibleExponent Λ V.1 := .of_hom V.1.ι
  have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin 1); Y) := .of_hom (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)
  let sq := AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) V.1.ι
  have := isIso_unit_tateObject_affineLine Λ (V.1.ι ≫ aY)
  exact isIso_homology_map_leftDerivedUpperStar_unit_app Λ sq.toCommSq _
    (leftDerivedUpperStarTateObjectIso V.1.ι 1) n
    ((NatTrans.isIso_app_iff_of_iso _ (leftDerivedUpperStarTateObjectIso _ 1)).2
      (isIso_derivedBaseChangeMap_app_tateObject_of_etale Λ sq 1)) inferInstance

end AlgClosed

section Field

variable {k : Type u} [Field k] {B : Scheme.{u}} (aB : B ⟶ Spec (.of k))

omit [NeZero (ringChar Λ)] in
/-- Isomorphisms between cohomology sheaves descend along the base change
`B ×_k k̄ ⟶ B` to an algebraic closure `k̄` of `k`, which is surjective. The hypothesis may use
that the exponent of `Λ` is invertible in `k`, which holds as soon as `B` is nonempty. -/
theorem isIso_homology_map_of_algebraicClosure [HasInvertibleExponent Λ B]
    {M N : _root_.DerivedCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : M ⟶ N) (n : ℤ)
    (h : HasInvertibleExponent Λ (Spec (.of k)) →
      IsIso ((_root_.DerivedCategory.homologyFunctor _ n).map
        ((L((pullback.fst aB (Spec.map (CommRingCat.ofHom
          (algebraMap k (AlgebraicClosure k)))))^*[ModuleCat.{u + 1} Λ])).map φ))) :
    IsIso ((_root_.DerivedCategory.homologyFunctor _ n).map φ) := by
  by_cases hB : Nonempty B
  · have := HasInvertibleExponent.of_hom_of_nonempty (Λ := Λ) aB
    let ι := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
    have : HasInvertibleExponent Λ (Spec (.of (AlgebraicClosure k))) := .of_hom ι
    have : Surjective ι := ⟨fun _ ↦ ⟨default, Subsingleton.elim _ _⟩⟩
    have hg : Surjective (pullback.fst aB ι) :=
      MorphismProperty.of_isPullback (IsPullback.of_hasPullback aB ι).flip this
    refine isIso_homology_map_of_jointlySurjective Λ (ι := PUnit.{u + 1})
      (fun _ ↦ pullback.fst aB ι) (fun x ↦ ?_) φ n fun _ ↦ h inferInstance
    obtain ⟨y, hy⟩ := hg.surj x
    exact ⟨⟨⟩, y, hy⟩
  · rw [not_nonempty_iff] at hB
    exact isIso_homology_map_of_jointlySurjective Λ (ι := PEmpty.{u + 1}) (fun _ ↦ 𝟙 B)
      (fun x ↦ isEmptyElim x) φ n fun i ↦ i.elim

variable [Finite Λ] [IsSeparated aB] [LocallyOfFiniteType aB] [HasInvertibleExponent Λ B]
  {G : Scheme.{u}} (j : G ⟶ 𝔸(ULift.{u} (Fin 1); B)) [IsOpenImmersion j] [QuasiCompact j]
  (hj : Set.range j.base = (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B).base)ᶜ)
  [HasInvertibleExponent Λ G]

include aB hj in
/-- Over an arbitrary field: for `B` separated and locally of finite type over a field `k` and
a quasi-compact open immersion `j : G ⟶ 𝔸¹_B` onto the complement of the zero section, the
unit `Λ_B(1) ⟶ Rπ_* Lπ^* Λ_B(1)` of `π = j ≫ p` is an isomorphism on `H⁰`. After base change
to an algebraic closure of `k` this is
`isIso_homology_zero_unit_tateObject_multiplicativeGroup_of_isAlgClosed`. -/
theorem isIso_homology_zero_unit_tateObject_multiplicativeGroup_of_field :
    IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
        (j ≫ 𝔸(ULift.{u} (Fin 1); B) ↘ B)).unit.app (tateObject Λ B 1))) := by
  refine isIso_homology_map_of_algebraicClosure Λ aB _ 0 fun _ ↦ ?_
  let ι := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  have hY := IsPullback.of_hasPullback aB ι
  have : HasInvertibleExponent Λ (Spec (.of (AlgebraicClosure k))) := .of_hom ι
  have : IsSeparated (pullback.snd aB ι) := MorphismProperty.of_isPullback hY inferInstance
  have : LocallyOfFiniteType (pullback.snd aB ι) :=
    MorphismProperty.of_isPullback hY inferInstance
  have : HasInvertibleExponent Λ (pullback aB ι) := .of_hom (pullback.fst aB ι)
  let j' := (𝔸(ULift.{u} (Fin 1); pullback aB ι).basicOpen
    (AffineSpace.coord (pullback aB ι) (ULift.up 0))).ι
  have hj' := AffineSpace.range_basicOpen_ι_coord (pullback aB ι)
  have : HasInvertibleExponent Λ (𝔸(ULift.{u} (Fin 1); pullback aB ι).basicOpen
      (AffineSpace.coord (pullback aB ι) (ULift.up 0))) :=
    .of_hom (j' ≫ 𝔸(ULift.{u} (Fin 1); pullback aB ι) ↘ pullback aB ι)
  exact isIso_homology_zero_map_leftDerivedUpperStar_unit_tateObject Λ (pullback.fst aB ι) j j'
    hj hj' (isIso_derivedBaseChangeMap_app_tateObject_of_fieldExtension Λ aB _ hY
      (AffineSpace.isPullback_complementMap_over (pullback.fst aB ι) j j' hj hj') 1)
    (isIso_homology_zero_unit_tateObject_multiplicativeGroup_of_isAlgClosed Λ
      (pullback.snd aB ι) j' hj')

include aB in
/-- Over an arbitrary field: for `B` separated and locally of finite type over a field `k`, a
quasi-compact open immersion `j : G ⟶ 𝔸¹_B` onto the complement of the zero section and every
identification `β : Lπ^* Λ_B ≅ Λ_G`, the adjoint `Λ_B ⟶ Rπ_*(Λ(1)[1])` of the Kummer class
`κ(t)` is an isomorphism on `H⁰`. After base change to an algebraic closure of `k` this is
`isIso_homology_zero_homEquiv_kummerClass_of_isAlgClosed`. -/
theorem isIso_homology_zero_homEquiv_kummerClass_of_field
    (β : (L((j ≫ 𝔸(ULift.{u} (Fin 1); B) ↘ B)^*[ModuleCat.{u + 1} Λ])).obj
        (constantComplex Λ B) ≅ constantComplex Λ G) :
    IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
        (j ≫ 𝔸(ULift.{u} (Fin 1); B) ↘ B)).homEquiv _ _
          (β.hom ≫ kummerClass Λ (AffineSpace.unitLineCoord j hj)))) := by
  refine isIso_homology_map_of_algebraicClosure Λ aB _ 0 fun _ ↦ ?_
  let ι := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  have hY := IsPullback.of_hasPullback aB ι
  have : HasInvertibleExponent Λ (Spec (.of (AlgebraicClosure k))) := .of_hom ι
  have : IsSeparated (pullback.snd aB ι) := MorphismProperty.of_isPullback hY inferInstance
  have : LocallyOfFiniteType (pullback.snd aB ι) :=
    MorphismProperty.of_isPullback hY inferInstance
  have : HasInvertibleExponent Λ (pullback aB ι) := .of_hom (pullback.fst aB ι)
  let j' := (𝔸(ULift.{u} (Fin 1); pullback aB ι).basicOpen
    (AffineSpace.coord (pullback aB ι) (ULift.up 0))).ι
  have hj' := AffineSpace.range_basicOpen_ι_coord (pullback aB ι)
  have : HasInvertibleExponent Λ (𝔸(ULift.{u} (Fin 1); pullback aB ι).basicOpen
      (AffineSpace.coord (pullback aB ι) (ULift.up 0))) :=
    .of_hom (j' ≫ 𝔸(ULift.{u} (Fin 1); pullback aB ι) ↘ pullback aB ι)
  exact isIso_homology_zero_map_leftDerivedUpperStar_homEquiv_kummerClass Λ (pullback.fst aB ι)
    j j' hj hj' (isIso_derivedBaseChangeMap_app_tateObject_of_fieldExtension Λ aB _ hY
      (AffineSpace.isPullback_complementMap_over (pullback.fst aB ι) j j' hj hj') 1)
    (isIso_homology_zero_homEquiv_kummerClass_of_isAlgClosed Λ (pullback.snd aB ι) j' hj') β


omit [HasInvertibleExponent Λ G] in
include aB in
/-- Over an arbitrary field: for `B` separated and locally of finite type over a field `k`, the
unit `Λ_B(1) ⟶ Rp_* Lp^* Λ_B(1)` of the projection `p : 𝔸¹_B ⟶ B` is an isomorphism. After
base change to an algebraic closure of `k` this is
`isIso_unit_tateObject_affineLine_of_isAlgClosed`. -/
theorem isIso_unit_tateObject_affineLine_of_field :
    IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
      (𝔸(ULift.{u} (Fin 1); B) ↘ B)).unit.app (tateObject Λ B 1)) := by
  rw [_root_.DerivedCategory.isIso_iff]
  intro n
  refine isIso_homology_map_of_algebraicClosure Λ aB _ n fun _ ↦ ?_
  let ι := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  have hY := IsPullback.of_hasPullback aB ι
  have : HasInvertibleExponent Λ (Spec (.of (AlgebraicClosure k))) := .of_hom ι
  have : IsSeparated (pullback.snd aB ι) := MorphismProperty.of_isPullback hY inferInstance
  have : LocallyOfFiniteType (pullback.snd aB ι) :=
    MorphismProperty.of_isPullback hY inferInstance
  have : HasInvertibleExponent Λ (pullback aB ι) := .of_hom (pullback.fst aB ι)
  have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin 1); B) := .of_hom (𝔸(ULift.{u} (Fin 1); B) ↘ B)
  let sq := AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) (pullback.fst aB ι)
  have := isIso_unit_tateObject_affineLine_of_isAlgClosed Λ (pullback.snd aB ι)
  exact isIso_homology_map_leftDerivedUpperStar_unit_app Λ sq.toCommSq _
    (leftDerivedUpperStarTateObjectIso (pullback.fst aB ι) 1) n
    ((NatTrans.isIso_app_iff_of_iso _ (leftDerivedUpperStarTateObjectIso _ 1)).2
      (isIso_derivedBaseChangeMap_app_tateObject_of_fieldExtension Λ aB _ hY sq 1))
    inferInstance

end Field

end Etale

end AlgebraicGeometry
