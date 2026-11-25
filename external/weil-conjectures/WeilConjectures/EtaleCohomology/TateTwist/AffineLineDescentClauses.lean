/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLineNormalization
public import WeilConjectures.EtaleCohomology.TateTwist.AffineLineDescentKummer
public import WeilConjectures.EtaleCohomology.TateTwist.KummerClass

/-!
# The degree-zero and degree-one clauses of `sk-prop-a1-kummer` over an arbitrary field

The clauses (b) of blueprint `sk-prop-a1-kummer` for the twist `Λ(1) = μₙ ⊗ Λ`, over a base `B`
separated and locally of finite type over an arbitrary field, in the form of
`AlgebraicGeometry.Etale.affineLine_multiplicativeGroup_homology_tateObject`: with
`p : 𝔸¹_B ⟶ B` and `j : 𝔾_{m,B} ⟶ 𝔸¹_B` the basic open of the coordinate,

* the restriction `R⁰p_* Λ(1) ⟶ R⁰p_* Rj_* j^* Λ(1)` is an isomorphism
  (`AlgebraicGeometry.Etale.isIso_homology_zero_map_unit_multiplicativeGroup_of_field`);
* the Kummer class `κ(t) : Λ_B ⟶ (Rp_* Rj_* j^* Λ(1))[1]` induces an isomorphism
  `Λ_B ≅ R¹π_* Λ(1)`
  (`AlgebraicGeometry.Etale.isIso_shiftMap_kummerClassAffineLineDirectImage_of_field`).

They follow from the statements of
`WeilConjectures.EtaleCohomology.TateTwist.AffineLineDescentKummer` for `π = j ≫ p` through the
comparison of the adjunction `Lπ^* ⊣ Rπ_*` with the composite of `Lp^* ⊣ Rp_*` and
`Lj^* ⊣ Rj_*`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [NeZero (ringChar Λ)]
  {k : Type u} [Field k] (B : Scheme.{u}) (aB : B ⟶ Spec (.of k)) [IsSeparated aB]
  [LocallyOfFiniteType aB] [HasInvertibleExponent Λ B]

include aB in
/-- Blueprint `sk-prop-a1-kummer`, clause (b) in degree zero, for the twist `Λ(1) = μₙ ⊗ Λ`,
over an arbitrary field: for `B` separated and locally of finite type over a field `k`, the
projection `p : 𝔸¹_B ⟶ B` and the basic open `j : 𝔾_{m,B} ⟶ 𝔸¹_B` of the coordinate, the
restriction `R⁰p_* Λ(1) ⟶ R⁰p_* Rj_* j^* Λ(1)` is an isomorphism. Both the unit of `p` and the
unit of `π = j ≫ p` are isomorphisms on `H⁰`
(`AlgebraicGeometry.Etale.isIso_unit_tateObject_affineLine_of_field`,
`AlgebraicGeometry.Etale.isIso_homology_zero_unit_tateObject_multiplicativeGroup_of_field`), and
the unit of `π` is the unit of `p` followed by `Rp_*` of the unit of `j`. -/
theorem isIso_homology_zero_map_unit_multiplicativeGroup_of_field :
    IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      ((R((𝔸(ULift.{u} (Fin 1); B) ↘ B)_*[ModuleCat.{u + 1} Λ])).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
          ((𝔸(ULift.{u} (Fin 1); B).basicOpen (AffineSpace.coord B (ULift.up 0))).ι)).unit.app
            (tateObject Λ 𝔸(ULift.{u} (Fin 1); B) 1)))) := by
  let p := 𝔸(ULift.{u} (Fin 1); B) ↘ B
  let j := (𝔸(ULift.{u} (Fin 1); B).basicOpen (AffineSpace.coord B (ULift.up 0))).ι
  let H := _root_.DerivedCategory.homologyFunctor (Sheaf B.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)) 0
  let adjp := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p
  let adjj := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j
  let adjπ := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (j ≫ p)
  let e := leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) j p
  have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin 1); B) := .of_hom p
  have : HasInvertibleExponent Λ
      (𝔸(ULift.{u} (Fin 1); B).basicOpen (AffineSpace.coord B (ULift.up 0))) := .of_hom j
  have hπ := isIso_homology_zero_unit_tateObject_multiplicativeGroup_of_field Λ aB j
    (AffineSpace.range_basicOpen_ι_coord B)
  have hp := isIso_unit_tateObject_affineLine_of_field Λ aB
  have hconj := unit_conjugateEquiv (adjp.comp adjj) adjπ e.hom (tateObject Λ B 1)
  have hC : IsIso (H.map ((adjp.comp adjj).unit.app (tateObject Λ B 1))) := by
    have : IsIso (H.map ((adjp.comp adjj).unit.app (tateObject Λ B 1)) ≫
        H.map ((conjugateEquiv (adjp.comp adjj) adjπ e.hom).app _)) := by
      rw [← Functor.map_comp, hconj, Functor.map_comp]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (H.map ((conjugateEquiv (adjp.comp adjj) adjπ e.hom).app _))
  rw [Adjunction.comp_unit_app, Functor.map_comp] at hC
  have := IsIso.of_isIso_comp_left (H.map (adjp.unit.app (tateObject Λ B 1)))
    (H.map ((R((p)_*[ModuleCat.{u + 1} Λ])).map
      (adjj.unit.app ((L((p)^*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ B 1)))))
  exact (NatTrans.isIso_app_iff_of_iso (Functor.whiskerRight (Functor.whiskerRight adjj.unit
    (R((p)_*[ModuleCat.{u + 1} Λ]))) H) (leftDerivedUpperStarTateObjectIso p 1)).1 this

-- the composites of derived functors on the three schemes `B`, `𝔸¹_B` and `𝔾_{m,B}` are large
include aB in
/-- Blueprint `sk-prop-a1-kummer`, clause (b) in degree one, for the twist `Λ(1) = μₙ ⊗ Λ`, over
an arbitrary field: for `B` separated and locally of finite type over a field `k`, the Kummer
class `κ(t) : Λ_B ⟶ (Rp_* Rj_* j^* Λ(1))[1]`
(`AlgebraicGeometry.Etale.kummerClassAffineLineDirectImage`) induces an isomorphism
`Λ_B ≅ R¹π_* Λ(1)`. Up to the composition isomorphism `Rp_* Rj_* ≅ Rπ_*`, `κ(t)` is the adjoint
of the Kummer class for `π = j ≫ p`, which is an isomorphism on `H⁰` by
`AlgebraicGeometry.Etale.isIso_homology_zero_homEquiv_kummerClass_of_field`. -/
theorem isIso_shiftMap_kummerClassAffineLineDirectImage_of_field :
    IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).shiftMap
      (kummerClassAffineLineDirectImage Λ B) 0 1 (by norm_num)) := by
  let p := 𝔸(ULift.{u} (Fin 1); B) ↘ B
  let j := (𝔸(ULift.{u} (Fin 1); B).basicOpen (AffineSpace.coord B (ULift.up 0))).ι
  let H := _root_.DerivedCategory.homologyFunctor (Sheaf B.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)) 0
  let adjp := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p
  let adjj := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j
  let adjπ := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (j ≫ p)
  let e := leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) j p
  have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin 1); B) := .of_hom p
  have : HasInvertibleExponent Λ
      (𝔸(ULift.{u} (Fin 1); B).basicOpen (AffineSpace.coord B (ULift.up 0))) := .of_hom j
  have hj := AffineSpace.range_basicOpen_ι_coord B
  let θp := leftDerivedUpperStarConstantComplexIso Λ p
  let θj := leftDerivedUpperStarConstantComplexIso Λ j
  let TI := leftDerivedUpperStarTateObjectIso (Λ := Λ) j 1
  let κ := kummerClass Λ (AffineSpace.unitLineCoord j hj)
  have hκ : kummerClass Λ (𝔸(ULift.{u} (Fin 1); B).basicOpenUnit
      (AffineSpace.coord B (ULift.up 0))) = κ := by
    congr 1
  let y := (L((j)^*[ModuleCat.{u + 1} Λ])).map θp.hom ≫ θj.hom ≫ κ ≫ TI.inv⟦(1 : ℤ)⟧'
  let β := e.app (constantComplex Λ B) ≪≫ (L((j)^*[ModuleCat.{u + 1} Λ])).mapIso θp ≪≫ θj
  have hP := isIso_homology_zero_homEquiv_kummerClass_of_field Λ aB j hj β
  have h₂ : e.hom.app _ ≫ y = β.hom ≫ κ ≫ TI.inv⟦(1 : ℤ)⟧' := by
    simp [β, y]
  have hn : (R((p)_*[ModuleCat.{u + 1} Λ])).map θp.hom ≫ (R((p)_*[ModuleCat.{u + 1} Λ])).map
      (adjj.unit.app (constantComplex Λ 𝔸(ULift.{u} (Fin 1); B))) =
      (R((p)_*[ModuleCat.{u + 1} Λ])).map (adjj.unit.app _) ≫
        (R((p)_*[ModuleCat.{u + 1} Λ])).map ((R((j)_*[ModuleCat.{u + 1} Λ])).map
          ((L((j)^*[ModuleCat.{u + 1} Λ])).map θp.hom)) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _ (adjj.unit_naturality θp.hom).symm
  have h₃ : kummerClassAffineLineDirectImage Λ B = (adjp.comp adjj).homEquiv _ _ y ≫
      (R((p)_*[ModuleCat.{u + 1} Λ])).map
        (((R((j)_*[ModuleCat.{u + 1} Λ])).commShiftIso (1 : ℤ)).hom.app _) ≫
      ((R((p)_*[ModuleCat.{u + 1} Λ])).commShiftIso (1 : ℤ)).hom.app _ := by
    rw [Adjunction.homEquiv_unit, Adjunction.comp_unit_app]
    simp only [kummerClassAffineLineDirectImage, kummerClassAdjoint, ShiftedHom.map,
      Functor.comp_map, Functor.map_comp, Category.assoc, hκ, y]
    erw [reassoc_of% hn]
  clear_value y
  have h₁ := AlgebraicGeometry.Etale.Adjunction.homEquiv_comp_conjugateEquiv_app
    (adjp.comp adjj) adjπ e.hom y
  have hy : IsIso (H.map ((adjp.comp adjj).homEquiv _ _ y)) := by
    have : IsIso (H.map ((adjp.comp adjj).homEquiv _ _ y) ≫
        H.map ((conjugateEquiv (adjp.comp adjj) adjπ e.hom).app _)) := by
      rw [← Functor.map_comp, h₁, h₂, ← Category.assoc, Adjunction.homEquiv_naturality_right,
        Functor.map_comp]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (H.map ((conjugateEquiv (adjp.comp adjj) adjπ e.hom).app _))
  have hκB : IsIso (H.map (kummerClassAffineLineDirectImage Λ B)) := by
    rw [h₃, Functor.map_comp, Functor.map_comp]
    infer_instance
  have := (NatIso.isIso_map_iff (H.isoShiftZero ℤ).symm _).1 hκB
  rw [Functor.shiftMap]
  infer_instance

end Etale

end AlgebraicGeometry
