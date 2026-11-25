/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.ProjectiveLineClass
public import WeilConjectures.EtaleCohomology.Purity.Smooth.SupportedClassMapRestriction
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.CupProductCoherence

/-!
# Gysin images as classes with supports

* The Gysin image of `a : Λ_Z ⟶ Ri^! L[n]` (`AlgebraicGeometry.Etale.gysinClass`) is the class
  with supports `Λ_X ⟶ (Ri_! Ri^! L)[n]` adjoint to `a`, with its supports forgotten
  (`AlgebraicGeometry.Etale.gysinClass_eq`).
* The class of a section generates: if the adjoint of a class `γ` supported on a closed
  immersion `x : Z ⟶ X` with `x ≫ a` an isomorphism is an isomorphism, so is
  `Λ_S ⟶ Ra_* Λ_X ⟶ Ra_* Rx_! Rx^! L`
  (`AlgebraicGeometry.Etale.isIso_unit_comp_map_of_isIso_supportedClassMap_of_isIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

section Gysin

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

omit [Finite Λ] in
variable (Λ) in
/-- The inverse of `Ri_! ≅ Ri_*` followed by the forget-supports map `Ri_! ⟶ Rc_* ⋙ Rg_*` of the
chosen compactification `(c, g)` of `i` is the inverse of the composition isomorphism
`Rc_* ⋙ Rg_* ≅ R(c ≫ g)_* = Ri_*`. -/
lemma rightDerivedLowerShriekIsoRightDerivedLowerStar_inv_app_comp
    (N : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) i).inv.app N ≫
        (rightDerivedLowerShriekToLowerStarComp (ModuleCat.{u + 1} Λ) i).app N =
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} Λ) _ _ ≪≫
        rightDerivedLowerStarCongr (ModuleCat.{u + 1} Λ)
          (HasCompactification.compactification i).comm.symm).inv.app N := by
  rw [← Iso.app_inv, Iso.inv_comp_eq, Iso.app_hom,
    rightDerivedLowerShriekIsoRightDerivedLowerStar_hom]
  simp only [Iso.trans_inv, NatTrans.comp_app, Category.assoc, Iso.hom_inv_id_app_assoc,
    Iso.hom_inv_id_app, Category.comp_id]

omit [Finite Λ] in
variable (Λ) in
/-- Transposing the unit of `Li^* ⊣ Ri_*`, followed by `Ri_* ≅ Rc_* ⋙ Rg_*`, under the composite
adjunction `Lg^* ⋙ Lc^* ⊣ Rc_* ⋙ Rg_*` of the chosen compactification `(c, g)` of `i` gives the
composition isomorphism `Li^* ≅ Lg^* ⋙ Lc^*`. -/
lemma homEquiv_symm_unit_app_comp_rightDerivedLowerStarComp_inv_app
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) _).comp
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) _)).homEquiv _ _).symm
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app K ≫
          (rightDerivedLowerStarComp (ModuleCat.{u + 1} Λ) _ _ ≪≫
            rightDerivedLowerStarCongr (ModuleCat.{u + 1} Λ)
              (HasCompactification.compactification i).comm.symm).inv.app _) =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) _ _ i
        (HasCompactification.compactification i).comm).inv.app K := by
  have hE := rightDerivedLowerStarComp_hom_comp_congr_hom (ModuleCat.{u + 1} Λ)
    (HasCompactification.compactification i).i (HasCompactification.compactification i).g i
    (HasCompactification.compactification i).comm
  apply (((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) _).comp
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) _)).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit, ← cancel_mono
    ((rightDerivedLowerStarComp (ModuleCat.{u + 1} Λ) _ _ ≪≫
      rightDerivedLowerStarCongr (ModuleCat.{u + 1} Λ)
        (HasCompactification.compactification i).comm.symm).hom.app _)]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [NatTrans.naturality, Iso.trans_hom, hE, ← Category.assoc, unit_conjugateEquiv,
    Category.assoc, ← Functor.map_comp]
  simp

omit [Finite Λ] in
variable (Λ) in
/-- The transpose (`AlgebraicGeometry.Etale.rightDerivedLowerShriekTranspose`) of
`K ⟶ Ri_* Li^* K ⟶ Ri_* N ≅ Ri_! N` is `Lc^* Lg^* K ≅ Li^* K ⟶ N`, for the chosen
compactification `(c, g)` of the closed immersion `i`. -/
lemma rightDerivedLowerShriekTranspose_unit_app_comp_map_comp_inv_app
    {K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {N : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (β : (L((i)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ N) :
    rightDerivedLowerShriekTranspose (ModuleCat.{u + 1} Λ) i
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app K ≫
          (R((i)_*[ModuleCat.{u + 1} Λ])).map β ≫
            (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) i).inv.app N) =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) _ _ i
        (HasCompactification.compactification i).comm).inv.app K ≫ β := by
  rw [rightDerivedLowerShriekTranspose, Category.assoc, Category.assoc,
    rightDerivedLowerShriekIsoRightDerivedLowerStar_inv_app_comp, NatTrans.naturality,
    ← Category.assoc, Adjunction.homEquiv_naturality_right_symm,
    homEquiv_symm_unit_app_comp_rightDerivedLowerStarComp_inv_app]

omit [Finite Λ] [IsClosedImmersion i] in
variable (Λ) in
/-- The identification `Lc^* Lg^* Λ_X ≅ Λ_Z` of the chosen compactification `(c, g)` of `i` is
`Lc^* Lg^* Λ_X ≅ Li^* Λ_X ≅ Λ_Z`. -/
@[reassoc]
lemma compactificationConstantComplexIso_inv_comp_leftDerivedUpperStarComp_inv_app
    [HasCompactification i] :
    (compactificationConstantComplexIso Λ i).inv ≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) _ _ i
          (HasCompactification.compactification i).comm).inv.app (constantComplex Λ X) ≫
          (leftDerivedUpperStarConstantComplexIso Λ i).hom = 𝟙 _ := by
  rw [leftDerivedUpperStarConstantComplexIso_comp Λ (HasCompactification.compactification i).i
    (HasCompactification.compactification i).g i (HasCompactification.compactification i).comm]
  simp [compactificationConstantComplexIso]

omit [Finite Λ] in
variable (Λ) in
/-- For a closed immersion `i : Z ⟶ X` and `a : Λ_Z ⟶ N`, the composite
`Λ_X ⟶ Ri_* Li^* Λ_X ≅ Ri_* Λ_Z ⟶ Ri_* N ≅ Ri_! N` is the restriction map followed by `Ri_!(a)`
(`AlgebraicGeometry.Etale.supportedRestrictionMap`). -/
lemma unit_comp_map_comp_inv_eq_supportedRestrictionMap_comp
    {N : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (a : constantComplex Λ Z ⟶ N) :
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app _ ≫
      (R((i)_*[ModuleCat.{u + 1} Λ])).map ((leftDerivedUpperStarConstantComplexIso Λ i).hom ≫ a) ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) i).inv.app N =
      supportedRestrictionMap Λ i ≫ (R(i)_![ModuleCat.{u + 1} Λ]).map a := by
  apply (supportedTranspose_bijective Λ i N).injective
  rw [supportedTranspose_comp, supportedTranspose_supportedRestrictionMap, Category.id_comp,
    supportedTranspose, rightDerivedLowerShriekTranspose_unit_app_comp_map_comp_inv_app]
  exact compactificationConstantComplexIso_inv_comp_leftDerivedUpperStarComp_inv_app_assoc Λ i a

omit [Finite Λ] in
variable (Λ) in
/-- `AlgebraicGeometry.Etale.unit_comp_map_comp_inv_eq_supportedRestrictionMap_comp`, followed by
an arbitrary morphism `h` and read as a morphism out of `Λ_X`. -/
lemma unit_comp_map_comp_inv_comp_eq_supportedRestrictionMap_comp
    {N : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {T : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (a : constantComplex Λ Z ⟶ N) (h : (R(i)_![ModuleCat.{u + 1} Λ]).obj N ⟶ T) :
    ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app _ ≫
      (R((i)_*[ModuleCat.{u + 1} Λ])).map ((leftDerivedUpperStarConstantComplexIso Λ i).hom ≫ a) ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) i).inv.app N ≫ h :
          constantComplex Λ X ⟶ T) =
      supportedRestrictionMap Λ i ≫ (R(i)_![ModuleCat.{u + 1} Λ]).map a ≫ h := by
  simp only [← Category.assoc]
  congr 1
  simp only [Category.assoc]
  apply (supportedTranspose_bijective Λ i N).injective
  rw [supportedTranspose_comp, supportedTranspose_supportedRestrictionMap, Category.id_comp,
    supportedTranspose, rightDerivedLowerShriekTranspose_unit_app_comp_map_comp_inv_app]
  exact compactificationConstantComplexIso_inv_comp_leftDerivedUpperStarComp_inv_app_assoc Λ i a

variable (Λ) in
/-- The Gysin image of `a : Λ_Z ⟶ (Ri^! L)[n]` along a closed immersion `i` is the class with
supports `Λ_X ⟶ Ri_! Λ_Z ⟶ Ri_!((Ri^! L)[n]) ≅ (Ri_! Ri^! L)[n]` adjoint to `a`, followed by the
counit of `Ri_! ⊣ Ri^!`. -/
lemma gysinClass_eq (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (n : ℤ) (a : constantComplex Λ Z ⟶ ((R(i)^![Λ]).obj L)⟦n⟧) :
    gysinClass Λ i L n a =
      (supportedRestrictionMap Λ i ≫ (R(i)_![ModuleCat.{u + 1} Λ]).map a ≫
        ((R(i)_![ModuleCat.{u + 1} Λ]).commShiftIso n).hom.app _) ≫
        ((rightDerivedUpperShriekAdjunction Λ i).counit.app L)⟦n⟧' := by
  rw [gysinClass, unit_comp_map_comp_inv_comp_eq_supportedRestrictionMap_comp]
  simp only [Category.assoc]

variable (Λ) in
/-- Forgetting the supports of a degree-`n` class read with coefficients `L[n]`
(`AlgebraicGeometry.Etale.shiftSupportedClass`) is forgetting its supports in degree `n`. -/
lemma shiftSupportedClass_comp_counit (n : ℤ)
    {K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (α : K ⟶ ((R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L))⟦n⟧) :
    shiftSupportedClass Λ i n α ≫ (rightDerivedUpperShriekAdjunction Λ i).counit.app (L⟦n⟧) =
      α ≫ ((rightDerivedUpperShriekAdjunction Λ i).counit.app L)⟦n⟧' := by
  have := (rightDerivedUpperShriekAdjunction Λ i).commShift_of_leftAdjoint ℤ
  have h := (rightDerivedUpperShriekAdjunction Λ i).commShiftIso_inv_app_counit_app ℤ n L
  simp only [Functor.commShiftIso_comp_inv_app, Category.assoc] at h
  rw [shiftSupportedClass, Category.assoc, Category.assoc, h]

variable (Λ) in
/-- The adjoint of the degree-`n` class `Λ_X ⟶ Ri_! Λ_Z ⟶ Ri_!((Ri^! L)[n]) ≅ (Ri_! Ri^! L)[n]`
of `a : Λ_Z ⟶ (Ri^! L)[n]`, read with coefficients `L[n]`, is `a` followed by the shift
compatibility of `Ri^!`. -/
lemma supportedClassMap_shiftSupportedClass_supportedRestrictionMap
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (n : ℤ) (a : constantComplex Λ Z ⟶ ((R(i)^![Λ]).obj L)⟦n⟧) :
    supportedClassMap Λ i (shiftSupportedClass Λ i n
        (supportedRestrictionMap Λ i ≫ (R(i)_![ModuleCat.{u + 1} Λ]).map a ≫
          ((R(i)_![ModuleCat.{u + 1} Λ]).commShiftIso n).hom.app _)) =
      a ≫ ((R(i)^![Λ]).commShiftIso n).inv.app L := by
  rw [supportedClassMap_eq_supportedTranspose, shiftSupportedClass]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp]
  rw [supportedTranspose_comp, supportedTranspose_supportedRestrictionMap, Category.id_comp]

end Gysin

section Section

variable {X S Z : Scheme.{u}} (a : X ⟶ S) (x : Z ⟶ X) [IsClosedImmersion x] [IsIso (x ≫ a)]

/-- **The class of a section generates.** Let `x : Z ⟶ X` be a closed immersion such that
`x ≫ a : Z ⟶ S` is an isomorphism, and `γ : Λ_X ⟶ Rx_! Rx^! L` a class supported on `x` whose
adjoint `Λ_Z ⟶ Rx^! L` (`AlgebraicGeometry.Etale.supportedClassMap`) is an isomorphism. Then its
image `U ⟶ Ra_* La^* U ≅ Ra_* Λ_X ⟶ Ra_* Rx_! Rx^! L` is an isomorphism, for every
identification `La^* U ≅ Λ_X`. -/
lemma isIso_unit_comp_map_of_isIso_supportedClassMap_of_isIso
    {L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {U : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (e : (L((a)^*[ModuleCat.{u + 1} Λ])).obj U ≅ constantComplex Λ X)
    (γ : constantComplex Λ X ⟶
      (R(x)_![ModuleCat.{u + 1} Λ]).obj ((R(x)^![Λ]).obj L))
    (h : IsIso (supportedClassMap Λ x γ)) :
    IsIso ((derivedUpperStarLowerStarAdjunction _ a).unit.app U ≫
      (R((a)_*[ModuleCat.{u + 1} Λ])).map (e.hom ≫ γ)) := by
  let c := HasCompactification.compactification x
  let adjGI := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) c.g).comp
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) c.i)
  let adjC := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a).comp adjGI
  have : (L((x ≫ a)^*[ModuleCat.{u + 1} Λ])).IsEquivalence := inferInstance
  have : (L((a)^*[ModuleCat.{u + 1} Λ]) ⋙ L((c.g)^*[ModuleCat.{u + 1} Λ]) ⋙
      L((c.i)^*[ModuleCat.{u + 1} Λ])).IsEquivalence :=
    Functor.isEquivalence_of_iso ((leftDerivedUpperStarComp _ x a (x ≫ a) rfl) ≪≫
      Functor.isoWhiskerLeft _ (leftDerivedUpperStarComp _ c.i c.g x c.comm))
  have hu : IsIso adjC.unit := adjC.unit_isIso_of_L_fully_faithful
  let F := (rightDerivedLowerShriekToLowerStarComp (ModuleCat.{u + 1} Λ) x).app
    ((R(x)^![Λ]).obj L)
  have hfc : γ ≫ F = adjGI.unit.app _ ≫
      (R((c.i)_*[ModuleCat.{u + 1} Λ]) ⋙ R((c.g)_*[ModuleCat.{u + 1} Λ])).map
        ((compactificationConstantComplexIso Λ x).hom ≫ supportedClassMap Λ x γ) := by
    rw [supportedClassMap, Iso.hom_inv_id_assoc, rightDerivedLowerShriekTranspose]
    exact ((Adjunction.homEquiv_unit _ _ _ _).symm.trans (Equiv.apply_symm_apply _ _)).symm
  have hn := adjGI.unit.naturality e.hom
  simp only [Functor.id_map, Functor.comp_map] at hn
  have inner : e.hom ≫ γ =
      adjGI.unit.app _ ≫
        (R((c.i)_*[ModuleCat.{u + 1} Λ]) ⋙ R((c.g)_*[ModuleCat.{u + 1} Λ])).map
          ((L((c.g)^*[ModuleCat.{u + 1} Λ]) ⋙ L((c.i)^*[ModuleCat.{u + 1} Λ])).map
            e.hom ≫
          (compactificationConstantComplexIso Λ x).hom ≫ supportedClassMap Λ x γ) ≫ inv F := by
    rw [← cancel_mono F]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [hfc]
    simp only [Functor.comp_map, Functor.map_comp] at hn ⊢
    rw [reassoc_of% hn]
  have key : (derivedUpperStarLowerStarAdjunction _ a).unit.app U ≫
      (R((a)_*[ModuleCat.{u + 1} Λ])).map (e.hom ≫ γ) =
      adjC.unit.app _ ≫ (R((a)_*[ModuleCat.{u + 1} Λ])).map
        ((R((c.i)_*[ModuleCat.{u + 1} Λ]) ⋙ R((c.g)_*[ModuleCat.{u + 1} Λ])).map
          ((L((c.g)^*[ModuleCat.{u + 1} Λ]) ⋙ L((c.i)^*[ModuleCat.{u + 1} Λ])).map
            e.hom ≫
          (compactificationConstantComplexIso Λ x).hom ≫ supportedClassMap Λ x γ) ≫ inv F) := by
    rw [inner]
    simp only [adjC, adjGI, Adjunction.comp_unit_app, Functor.map_comp, Category.assoc]
  rw [key]
  infer_instance

end Section

end Etale

end AlgebraicGeometry
