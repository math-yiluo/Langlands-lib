/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReduction
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ProjectiveLineCohomologyGysin
public import WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral

/-!
# The reduction of coefficients as a change of coefficients with supports

Let `ρ : Λ →+* Λ'` be a surjective morphism of finite coefficient rings with principal kernel, the
main case being the reduction `A_{E,n+1} → A_{E,n}`, and `Ψ` the derived extension of scalars
(`AlgebraicGeometry.Etale.derivedExtendScalars`). For a closed immersion `i : Z ⟶ X`, `Ψ`
commutes with `Ri_! ≅ Ri_*` (`AlgebraicGeometry.Etale.derivedExtendScalarsLowerShriekIso`): the
comparison is the mate of the commutation of `Ψ` with `Li^*`, and it is an isomorphism, as it
is one after `Li^*` (where `Li^* Ri_* ≅ 𝟭`) and after the restriction to the open complement
(where both sides vanish). Its mate is the comparison `Ψ Ri^! ⟶ Ri^! Ψ`.

Together with the identifications `Ψ Λ_X ≅ Λ'_X` pulled back from the terminal scheme and a
compatible family of identifications `Ψ(Λ_X(m)[2m]) ≅ Λ'_X(m)[2m]`
(`AlgebraicGeometry.Etale.DerivedExtendScalarsTateShiftData`), this makes `Ψ` a change of
coefficients with supports (`AlgebraicGeometry.Etale.reductionSupportedCoefficientChange`,
blueprint `proposition-compatibility-purity-change-coefficients`), to which
`AlgebraicGeometry.Etale.SupportedCoefficientChange.map_dualizingComplexTwistShiftIso` applies.

## Main definitions

- `AlgebraicGeometry.Etale.derivedExtendScalarsLowerShriekIso`: `Ri_! ⋙ Ψ ≅ Ψ ⋙ Ri_!`.
- `AlgebraicGeometry.Etale.derivedExtendScalarsUpperShriekMap`: `Ri^! ⋙ Ψ ⟶ Ψ ⋙ Ri^!`.
- `AlgebraicGeometry.Etale.derivedExtendScalarsConstantComplexIso`: `Ψ Λ_X ≅ Λ'_X`.
- `AlgebraicGeometry.Etale.reductionSupportedCoefficientChange`: the derived extension of scalars
  as a `SupportedCoefficientChange`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {ρ : Λ →+* Λ'} {a : Λ}
  (hρ : Function.Surjective ρ) (ha : RingHom.ker ρ = Ideal.span {a})

section ConstantComplex

/-- **The derived extension of scalars of the constant complex**, `Ψ Λ_X ≅ Λ'_X`: the
identification on the terminal scheme, pulled back along `X ⟶ ⊤_`. -/
noncomputable def derivedExtendScalarsConstantComplexIso (X : Scheme.{u}) :
    (derivedExtendScalars hρ ha X).obj (constantComplex Λ X) ≅ constantComplex Λ' X :=
  derivedExtendScalarsConstantComplexIsoOfPullback hρ ha
    (derivedExtendScalarsConstantComplexEtaIso hρ ha (⊤_ Scheme.{u}))
    (terminal.from X)

/-- The identifications `Ψ Λ_X ≅ Λ'_X` are compatible with the derived pullbacks. -/
lemma derivedExtendScalarsConstantComplexIso_hom_pullback
    {U X : Scheme.{u}} (e : U ⟶ X) :
    (derivedExtendScalars hρ ha U).map (leftDerivedUpperStarConstantComplexIso Λ e).hom ≫
        (derivedExtendScalarsConstantComplexIso hρ ha U).hom =
      (derivedExtendScalarsPullbackIso hρ ha e).hom.app _ ≫
        (L((e)^*[ModuleCat.{u + 1} Λ'])).map (derivedExtendScalarsConstantComplexIso hρ ha X).hom ≫
          (leftDerivedUpperStarConstantComplexIso Λ' e).hom :=
  derivedExtendScalarsConstantComplexIsoOfPullback_hom_pullback hρ ha _
    e _ _ (terminal.hom_ext _ _)

end ConstantComplex

section ClosedImmersion

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The comparison `Ψ_X(Ri_* N) ⟶ Ri_*(Ψ_Z N)` for a closed immersion `i`: the mate, under the
adjunctions `Li^* ⊣ Ri_*`, of the commutation `Ψ_X ⋙ Li^* ≅ Li^* ⋙ Ψ_Z`. -/
noncomputable def derivedExtendScalarsLowerStarMap :
    R((i)_*[ModuleCat.{u + 1} Λ]) ⋙ derivedExtendScalars hρ ha X ⟶
      derivedExtendScalars hρ ha Z ⋙ R((i)_*[ModuleCat.{u + 1} Λ']) :=
  (mateEquiv (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') i)
    (TwoSquare.mk _ _ _ _ (derivedExtendScalarsPullbackIso hρ ha i).inv))

omit [IsClosedImmersion i] in
/-- The comparison `Ψ Ri_* ⟶ Ri_* Ψ` followed by the counit of `Li^* ⊣ Ri_*`. -/
@[reassoc]
lemma map_derivedExtendScalarsLowerStarMap_app_comp_counit (N : 𝐃(Z, Λ)) :
    (L((i)^*[ModuleCat.{u + 1} Λ'])).map ((derivedExtendScalarsLowerStarMap hρ ha i).app N) ≫
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') i).counit.app
          ((derivedExtendScalars hρ ha Z).obj N) =
      (derivedExtendScalarsPullbackIso hρ ha i).inv.app _ ≫
        (derivedExtendScalars hρ ha Z).map
          ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).counit.app N) :=
  mateEquiv_counit _ _ _ N

omit [IsClosedImmersion i] in
/-- The unit of `Li^* ⊣ Ri_*` followed by the comparison `Ψ Ri_* ⟶ Ri_* Ψ`. -/
@[reassoc]
lemma map_unit_comp_derivedExtendScalarsLowerStarMap_app (K : 𝐃(X, Λ)) :
    (derivedExtendScalars hρ ha X).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app K) ≫
      (derivedExtendScalarsLowerStarMap hρ ha i).app _ =
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') i).unit.app _ ≫
        (R((i)_*[ModuleCat.{u + 1} Λ'])).map
          ((derivedExtendScalarsPullbackIso hρ ha i).inv.app K) :=
  unit_mateEquiv _ _ _ K

instance isIso_derivedExtendScalarsLowerStarMap :
    IsIso (derivedExtendScalarsLowerStarMap hρ ha i) := by
  have hc (Γ : Type (u + 1)) [CommRing Γ] :
      IsIso (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Γ) i).counit := by
    have := (fullyFaithfulRightDerivedLowerStarOfIsClosedImmersion (Λ := Γ) i).full
    have := (fullyFaithfulRightDerivedLowerStarOfIsClosedImmersion (Λ := Γ) i).faithful
    exact
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Γ) i).counit_isIso_of_R_fully_faithful
  have (N : 𝐃(Z, Λ)) : IsIso ((derivedExtendScalarsLowerStarMap hρ ha i).app N) := by
    have hd : Disjoint (Set.range i.base) (Set.range i.openComplement.ι.base) := by
      rw [i.range_eq_compl_range_openComplement_ι]
      exact disjoint_compl_left
    refine isIso_of_isIso_leftDerivedUpperStar_map (ModuleCat.{u + 1} Λ') i.openComplement.ι i
      i.range_eq_compl_range_openComplement_ι _ ?_ ?_
    · -- both sides vanish on the open complement of `Z`
      have := (derivedExtendScalarsAdjunction hρ ha i.openComplement).isLeftAdjoint
      have h₁ := (Functor.map_isZero (derivedExtendScalars hρ ha i.openComplement)
        (isZero_leftDerivedUpperStar_obj_rightDerivedLowerStar_obj i _ hd N)).of_iso
          ((derivedExtendScalarsPullbackIso hρ ha i.openComplement.ι).app _).symm
      have h₂ := isZero_leftDerivedUpperStar_obj_rightDerivedLowerStar_obj i _ hd
        ((derivedExtendScalars hρ ha Z).obj N)
      exact ⟨0, h₁.eq_of_src _ _, h₂.eq_of_src _ _⟩
    · -- after `Li^*`, the comparison is identified with `Ψ` of the counit `Li^* Ri_* ⟶ 𝟭`
      have := hc Λ
      have := hc Λ'
      have h : IsIso ((L((i)^*[ModuleCat.{u + 1} Λ'])).map
          ((derivedExtendScalarsLowerStarMap hρ ha i).app N) ≫
            (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') i).counit.app
              ((derivedExtendScalars hρ ha Z).obj N)) := by
        rw [map_derivedExtendScalarsLowerStarMap_app_comp_counit]
        infer_instance
      exact IsIso.of_isIso_comp_right _
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') i).counit.app _)
  exact NatIso.isIso_of_isIso_app _

/-- **The derived extension of scalars commutes with `Ri_!`** for a closed immersion `i`:
`Ψ_X(Ri_! N) ≅ Ψ_X(Ri_* N) ≅ Ri_*(Ψ_Z N) ≅ Ri_!(Ψ_Z N)`. -/
noncomputable def derivedExtendScalarsLowerShriekIso :
    R(i)_![ModuleCat.{u + 1} Λ] ⋙ derivedExtendScalars hρ ha X ≅
      derivedExtendScalars hρ ha Z ⋙ R(i)_![ModuleCat.{u + 1} Λ'] :=
  -- `asIso` of the composite, rather than a composite of isomorphisms, so that the components of
  -- the isomorphism are checked by the kernel without unfolding `Ψ`
  asIso (Functor.whiskerRight
      (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) i).hom
      (derivedExtendScalars hρ ha X) ≫ derivedExtendScalarsLowerStarMap hρ ha i ≫
    Functor.whiskerLeft (derivedExtendScalars hρ ha Z)
      (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ') i).inv)

lemma derivedExtendScalarsLowerShriekIso_hom :
    (derivedExtendScalarsLowerShriekIso hρ ha i).hom =
      Functor.whiskerRight
          (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) i).hom
          (derivedExtendScalars hρ ha X) ≫ derivedExtendScalarsLowerStarMap hρ ha i ≫
        Functor.whiskerLeft (derivedExtendScalars hρ ha Z)
          (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ') i).inv :=
  rfl

variable [Finite Λ] [Finite Λ']

/-- The comparison `Ψ_Z(Ri^! L) ⟶ Ri^!(Ψ_X L)` for a closed immersion `i`: the mate, under the
adjunctions `Ri_! ⊣ Ri^!`, of the commutation `Ψ ⋙ Ri_! ≅ Ri_! ⋙ Ψ`. -/
noncomputable def derivedExtendScalarsUpperShriekMap :
    R(i)^![Λ] ⋙ derivedExtendScalars hρ ha Z ⟶ derivedExtendScalars hρ ha X ⋙ R(i)^![Λ'] :=
  (mateEquiv (rightDerivedUpperShriekAdjunction Λ i) (rightDerivedUpperShriekAdjunction Λ' i)
    (TwoSquare.mk _ _ _ _ (derivedExtendScalarsLowerShriekIso hρ ha i).inv))

/-- The comparison `Ψ Ri^! ⟶ Ri^! Ψ` is compatible with the counits of `Ri_! ⊣ Ri^!`. -/
lemma map_derivedExtendScalarsUpperShriekMap_app_comp_counit (L : 𝐃(X, Λ)) :
    (R(i)_![ModuleCat.{u + 1} Λ']).map ((derivedExtendScalarsUpperShriekMap hρ ha i).app L) ≫
        (rightDerivedUpperShriekAdjunction Λ' i).counit.app ((derivedExtendScalars hρ ha X).obj L) =
      (derivedExtendScalarsLowerShriekIso hρ ha i).inv.app ((R(i)^![Λ]).obj L) ≫
        (derivedExtendScalars hρ ha X).map ((rightDerivedUpperShriekAdjunction Λ i).counit.app L) :=
  mateEquiv_counit (rightDerivedUpperShriekAdjunction Λ i) (rightDerivedUpperShriekAdjunction Λ' i)
    (TwoSquare.mk _ _ _ _ (derivedExtendScalarsLowerShriekIso hρ ha i).inv) L

omit [Finite Λ] [Finite Λ'] in
/-- **The derived extension of scalars carries the restriction map `Λ_X ⟶ Ri_! Λ_Z` to the
restriction map.** The restriction map is `Λ_X ⟶ Ri_* Li^* Λ_X ≅ Ri_* Λ_Z ≅ Ri_! Λ_Z`
(`AlgebraicGeometry.Etale.unit_comp_map_comp_inv_eq_supportedRestrictionMap_comp`), and each step
is compatible with `Ψ`: the unit by the definition of `Ψ Ri_* ≅ Ri_* Ψ` as a mate, and
`Li^* Λ_X ≅ Λ_Z` by
`AlgebraicGeometry.Etale.derivedExtendScalarsConstantComplexIso_hom_pullback`.
-/
lemma map_supportedRestrictionMap_comp_derivedExtendScalarsLowerShriekIso_hom_app :
    (derivedExtendScalars hρ ha X).map (supportedRestrictionMap Λ i) ≫
        (derivedExtendScalarsLowerShriekIso hρ ha i).hom.app _ ≫
          (R(i)_![ModuleCat.{u + 1} Λ']).map (derivedExtendScalarsConstantComplexIso hρ ha Z).hom =
      (derivedExtendScalarsConstantComplexIso hρ ha X).hom ≫ supportedRestrictionMap Λ' i := by
  have hr (Γ : Type (u + 1)) [CommRing Γ] := unit_comp_map_comp_inv_eq_supportedRestrictionMap_comp
    Γ i (𝟙 (constantComplex Γ Z))
  simp only [Category.comp_id, CategoryTheory.Functor.map_id] at hr
  have hc := derivedExtendScalarsConstantComplexIso_hom_pullback
    hρ ha i
  have hc' : (derivedExtendScalarsPullbackIso hρ ha i).inv.app (constantComplex Λ X) ≫
      (derivedExtendScalars hρ ha Z).map (leftDerivedUpperStarConstantComplexIso Λ i).hom ≫
        (derivedExtendScalarsConstantComplexIso hρ ha Z).hom =
      (L((i)^*[ModuleCat.{u + 1} Λ'])).map (derivedExtendScalarsConstantComplexIso hρ ha X).hom ≫
        (leftDerivedUpperStarConstantComplexIso Λ' i).hom := by
    rw [hc, Iso.inv_hom_id_app_assoc]
  have hβ := (derivedExtendScalarsLowerStarMap hρ ha i).naturality
    (leftDerivedUpperStarConstantComplexIso Λ i).hom
  have hu := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') i).unit.naturality
    (derivedExtendScalarsConstantComplexIso hρ ha X).hom
  have hi :=
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ') i).inv.naturality
      (derivedExtendScalarsConstantComplexIso hρ ha Z).hom
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at hβ hu hi
  rw [← hr Λ, ← hr Λ', derivedExtendScalarsLowerShriekIso_hom, NatTrans.comp_app,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc (derivedExtendScalars hρ ha X)
      ((rightDerivedLowerShriekIsoRightDerivedLowerStar _ i).inv.app _),
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp, reassoc_of% hβ,
    map_unit_comp_derivedExtendScalarsLowerStarMap_app_assoc, ← hi, reassoc_of% hu,
    ← Functor.map_comp_assoc, ← Functor.map_comp_assoc (R((i)_*[ModuleCat.{u + 1} Λ'])),
    Category.assoc, hc', Functor.map_comp_assoc]

end ClosedImmersion

section Structure

variable [HasTateTwist Λ] [HasTateTwist Λ']

variable (Λ Λ') in
/-- A family of identifications `Ψ(Λ_X(m)[2m]) ≅ Λ'_X(m)[2m]` of the derived extension of scalars
of the shifted twisting objects with the shifted twisting objects over `Λ'`, compatible with the
identifications `Le^*(Λ_X(m)[2m]) ≅ Λ_U(m)[2m]`. For the reduction `A_{E,n+1} → A_{E,n}` it comes
from `μ_{ℓ^{n+1}} ⊗ A_{E,n} ≅ μ_{ℓⁿ}`. -/
structure DerivedExtendScalarsTateShiftData where
  /-- The identification `Ψ(Λ_X(m)[2m]) ≅ Λ'_X(m)[2m]`. -/
  iso (X : Scheme.{u}) [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ' X] (m : ℤ) :
    (derivedExtendScalars hρ ha X).obj ((tateObject Λ X m)⟦2 * m⟧) ≅ (tateObject Λ' X m)⟦2 * m⟧
  /-- Compatibility with `Le^*(Λ_X(m)[2m]) ≅ Λ_U(m)[2m]`. -/
  map_leftDerivedUpperStarTateShiftIso {U X : Scheme.{u}} [HasInvertibleExponent Λ U]
    [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ' U] [HasInvertibleExponent Λ' X]
    (e : U ⟶ X) (m : ℤ) :
    (derivedExtendScalars hρ ha U).map (leftDerivedUpperStarTateShiftIso Λ e m).hom ≫
        (iso U m).hom =
      (derivedExtendScalarsPullbackIso hρ ha e).hom.app _ ≫
        (L((e)^*[ModuleCat.{u + 1} Λ'])).map (iso X m).hom ≫
          (leftDerivedUpperStarTateShiftIso Λ' e m).hom

variable [Finite Λ] [Finite Λ']

/-- Blueprint `proposition-compatibility-purity-change-coefficients`: change of coefficients in
purity

**The reduction of coefficients as a change of coefficients with supports.** For a surjective
morphism `ρ : Λ →+* Λ'` of finite coefficient rings with principal kernel (for instance
`A_{E,n+1} → A_{E,n}`) and compatible identifications `τ` of the shifted twisting objects, the
derived extension of scalars `Ψ = - ⊗ᴸ_Λ Λ'`, with its commutations with `Le^*`
(`AlgebraicGeometry.Etale.derivedExtendScalarsPullbackIso`), with `Ri_!`
(`AlgebraicGeometry.Etale.derivedExtendScalarsLowerShriekIso`) and with `Ri^!`
(`AlgebraicGeometry.Etale.derivedExtendScalarsUpperShriekMap`) and the identifications
`Ψ Λ_X ≅ Λ'_X` (`AlgebraicGeometry.Etale.derivedExtendScalarsConstantComplexIso`), is a change of
coefficients with supports. -/
noncomputable def reductionSupportedCoefficientChange
    (τ : DerivedExtendScalarsTateShiftData Λ Λ' hρ ha) : SupportedCoefficientChange Λ Λ' where
  functor X := derivedExtendScalars hρ ha X
  constantComplexIso X := derivedExtendScalarsConstantComplexIso hρ ha X
  tateShiftIso X _ _ m := τ.iso X m
  pullbackIso e := derivedExtendScalarsPullbackIso hρ ha e
  lowerShriekIso i _ := derivedExtendScalarsLowerShriekIso hρ ha i
  upperShriekMap i _ := derivedExtendScalarsUpperShriekMap hρ ha i
  map_counit i _ L := map_derivedExtendScalarsUpperShriekMap_app_comp_counit hρ ha i L
  map_supportedRestrictionMap i _ :=
    map_supportedRestrictionMap_comp_derivedExtendScalarsLowerShriekIso_hom_app hρ ha i
  map_leftDerivedUpperStarConstantComplexIso e :=
    derivedExtendScalarsConstantComplexIso_hom_pullback
      hρ ha e
  map_leftDerivedUpperStarTateShiftIso e m := τ.map_leftDerivedUpperStarTateShiftIso e m

end Structure

end Etale

end AlgebraicGeometry
