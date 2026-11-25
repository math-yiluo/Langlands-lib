/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationCoefficients
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeStalk
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionHom
public import WeilConjectures.SixFunctors.Etale.Derived.Stalks.Basic

/-!
# The reduction of coefficients and the derived pullback

Let `ρ : Λ →+* Λ'` be a surjective morphism of commutative rings with principal kernel, the main
case being the reduction `A_{E,n+1} → A_{E,n}`, and write `Ψ_X : D(X_ét, Λ) ⥤ D(X_ét, Λ')` for the
derived extension of scalars `K ↦ K ⊗ᴸ_Λ Λ'` (`AlgebraicGeometry.Etale.derivedExtendScalars`),
left adjoint to the restriction of scalars `Res`. This file shows that `Ψ` commutes with the
derived pullbacks (blueprint `proposition-compatibility-purity-change-coefficients`):

* `Lf^*` carries derived base changes to derived base changes
  (`AlgebraicGeometry.Etale.isDerivedBaseChange_leftDerivedUpperStar_map_comp'`): this is checked
  on the geometric points, where it is
  `AlgebraicGeometry.Etale.isDerivedBaseChange_leftDerivedUpperStar_map_comp`;
* hence the transpose `Lf^* ⋙ Ψ ⟶ Ψ ⋙ Lf^*` of the commutation `Res ⋙ Lf^* ≅ Lf^* ⋙ Res` is an
  isomorphism (`AlgebraicGeometry.Etale.derivedExtendScalarsPullbackIso`), compatible with the
  composition of the derived pullbacks
  (`AlgebraicGeometry.Etale.derivedExtendScalarsPullbackMap_comp`) and with the identity
  (`AlgebraicGeometry.Etale.derivedExtendScalarsPullbackMap_id`);
* an identification `Ψ Λ_S ≅ Λ'_S` pulled back along morphisms `X ⟶ S` gives identifications
  `Ψ Λ_X ≅ Λ'_X` compatible with the derived pullbacks
  (`AlgebraicGeometry.Etale.derivedExtendScalarsConstantComplexIsoOfPullback_hom_pullback`).

## Main definitions

- `AlgebraicGeometry.Etale.derivedExtendScalarsPullbackIso`: `Lf^* ⋙ Ψ ≅ Ψ ⋙ Lf^*`.
- `AlgebraicGeometry.Etale.derivedExtendScalarsConstantComplexIsoOfPullback`: the identification
  `Ψ Λ_X ≅ Λ'_X` pulled back from `S`.
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

section Pullback

variable {U X : Scheme.{u}} (e : U ⟶ X)

/-- **The derived pullback carries derived base changes to derived base changes.** If
`η : K ⟶ Res K'` exhibits `K'` as `K ⊗ᴸ_Λ Λ'`, then `Le^* η` followed by the commutation
`Le^* Res ≅ Res Le^*` exhibits `Le^* K'` as `Le^* K ⊗ᴸ_Λ Λ'`. The comparison map
`Le^* K ⊗ᴸ_Λ Λ' ⟶ Le^* K'` is an isomorphism, as it is one on every geometric point `s`, where
`Ls^*` and `L(s ≫ e)^*` carry derived base changes to derived base changes
(`AlgebraicGeometry.Etale.isDerivedBaseChange_leftDerivedUpperStar_map_comp`). -/
lemma isDerivedBaseChange_leftDerivedUpperStar_map_comp' (hρ : Function.Surjective ρ)
    (ha : RingHom.ker ρ = Ideal.span {a}) {K : 𝐃(X, Λ)} {K' : 𝐃(X, Λ')}
    {η : K ⟶ (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).obj K'}
    (hη : Sheaf.IsDerivedBaseChange η) :
    Sheaf.IsDerivedBaseChange ((L((e)^*[ModuleCat.{u + 1} Λ])).map η ≫
      (leftDerivedUpperStarRestrictScalarsIso ρ e).hom.app K') := by
  let ηe := (L((e)^*[ModuleCat.{u + 1} Λ])).map η ≫
    (leftDerivedUpperStarRestrictScalarsIso ρ e).hom.app K'
  let t := ((derivedExtendScalarsAdjunction hρ ha U).homEquiv _ _).symm ηe
  have ht : (derivedExtendScalarsAdjunction hρ ha U).unit.app _ ≫
      (Sheaf.derivedRestrictScalars U.smallEtaleTopology ρ).map t = ηe :=
    ((derivedExtendScalarsAdjunction hρ ha U).homEquiv_unit _ _ t).symm.trans
      (Equiv.apply_symm_apply _ _)
  have hν := isDerivedBaseChange_derivedExtendScalarsAdjunction_unit hρ ha U
    ((L((e)^*[ModuleCat.{u + 1} Λ])).obj K)
  have : IsIso t := by
    rw [isIso_iff_forall_isIso_leftDerivedUpperStar_map Λ' t]
    intro Ω _ _ s
    refine Sheaf.IsDerivedBaseChange.isIso (η' := (L((s)^*[ModuleCat.{u + 1} Λ])).map ηe ≫
      (leftDerivedUpperStarRestrictScalarsIso ρ s).hom.app _)
      (isDerivedBaseChange_leftDerivedUpperStar_map_comp ρ s hν) ?_ _ ?_
    · -- the pullback of `ηe` along `s` is the pullback of `η` along `s ≫ e`
      have hc := leftDerivedUpperStarRestrictScalarsIso_comp_hom_app ρ s e K'
      have hn := (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) s e).hom.naturality η
      have h := ((isDerivedBaseChange_leftDerivedUpperStar_map_comp ρ (s ≫ e) hη).of_iso
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) s e).app K).symm).comp_map_iso
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ') s e).app K')
      have heq : (L((s)^*[ModuleCat.{u + 1} Λ])).map ηe ≫
          (leftDerivedUpperStarRestrictScalarsIso ρ s).hom.app _ =
            (((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) s e).app K).symm.hom ≫
              (L((s ≫ e)^*[ModuleCat.{u + 1} Λ])).map η ≫
                (leftDerivedUpperStarRestrictScalarsIso ρ (s ≫ e)).hom.app K') ≫
              (Sheaf.derivedRestrictScalars _ ρ).map
                ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ') s e).app K').hom := by
        simp only [ηe, Functor.map_comp, Category.assoc, Iso.symm_hom, Iso.app_inv, Iso.app_hom]
        rw [hc, reassoc_of% hn, Iso.inv_hom_id_app_assoc]
      rw [heq]
      exact h
    · have hn := (leftDerivedUpperStarRestrictScalarsIso ρ s).hom.naturality t
      simp only [Functor.comp_obj, Functor.comp_map] at hn
      rw [Category.assoc, ← hn, ← Functor.map_comp_assoc]
      exact congrArg (fun f ↦ (L((s)^*[ModuleCat.{u + 1} Λ])).map f ≫ _) ht
  have h := hν.comp_map_iso (asIso t)
  rwa [asIso_hom, ht] at h

/-- The comparison `Ψ_U(Le^* K) ⟶ Le^*(Ψ_X K)` of the derived extension of scalars with the
derived pullback: the transpose, under `Ψ ⊣ Res`, of the commutation
`Res ⋙ Le^* ≅ Le^* ⋙ Res` (`AlgebraicGeometry.Etale.leftDerivedUpperStarRestrictScalarsIso`). -/
noncomputable def derivedExtendScalarsPullbackMap :
    L((e)^*[ModuleCat.{u + 1} Λ]) ⋙ derivedExtendScalars hρ ha U ⟶
      derivedExtendScalars hρ ha X ⋙ L((e)^*[ModuleCat.{u + 1} Λ']) :=
  ((mateEquiv (derivedExtendScalarsAdjunction hρ ha X)
    (derivedExtendScalarsAdjunction hρ ha U)).symm
      (leftDerivedUpperStarRestrictScalarsIso ρ e).hom)

/-- The defining property of `derivedExtendScalarsPullbackMap`: its transpose is
`Le^*(K ⟶ Res Ψ K) ≫ (Le^* Res ≅ Res Le^*)`. -/
@[reassoc]
lemma unit_app_comp_map_derivedExtendScalarsPullbackMap_app (K : 𝐃(X, Λ)) :
    (derivedExtendScalarsAdjunction hρ ha U).unit.app ((L((e)^*[ModuleCat.{u + 1} Λ])).obj K) ≫
        (Sheaf.derivedRestrictScalars U.smallEtaleTopology ρ).map
          ((derivedExtendScalarsPullbackMap hρ ha e).app K) =
      (L((e)^*[ModuleCat.{u + 1} Λ])).map ((derivedExtendScalarsAdjunction hρ ha X).unit.app K) ≫
        (leftDerivedUpperStarRestrictScalarsIso ρ e).hom.app _ :=
  (unit_mateEquiv_symm (derivedExtendScalarsAdjunction hρ ha X)
    (derivedExtendScalarsAdjunction hρ ha U) (leftDerivedUpperStarRestrictScalarsIso ρ e).hom
    K).symm

instance isIso_derivedExtendScalarsPullbackMap :
    IsIso (derivedExtendScalarsPullbackMap hρ ha e) := by
  have (K : 𝐃(X, Λ)) : IsIso ((derivedExtendScalarsPullbackMap hρ ha e).app K) :=
    Sheaf.IsDerivedBaseChange.isIso
      (isDerivedBaseChange_derivedExtendScalarsAdjunction_unit hρ ha U _)
      (isDerivedBaseChange_leftDerivedUpperStar_map_comp' e hρ ha
        (isDerivedBaseChange_derivedExtendScalarsAdjunction_unit hρ ha X K)) _
      (unit_app_comp_map_derivedExtendScalarsPullbackMap_app hρ ha e K)
  exact NatIso.isIso_of_isIso_app _

/-- **The derived extension of scalars commutes with the derived pullback**:
`Ψ_U(Le^* K) ≅ Le^*(Ψ_X K)`, the transpose of `Res ⋙ Le^* ≅ Le^* ⋙ Res`. -/
noncomputable def derivedExtendScalarsPullbackIso :
    L((e)^*[ModuleCat.{u + 1} Λ]) ⋙ derivedExtendScalars hρ ha U ≅
      derivedExtendScalars hρ ha X ⋙ L((e)^*[ModuleCat.{u + 1} Λ']) :=
  asIso (derivedExtendScalarsPullbackMap hρ ha e)

@[simp]
lemma derivedExtendScalarsPullbackIso_hom :
    (derivedExtendScalarsPullbackIso hρ ha e).hom = derivedExtendScalarsPullbackMap hρ ha e :=
  rfl

/-- Morphisms out of `Ψ M` are determined by their transposes `M ⟶ Res N`. -/
lemma derivedExtendScalars_hom_ext {X : Scheme.{u}} {M : 𝐃(X, Λ)} {N : 𝐃(X, Λ')}
    {f g : (derivedExtendScalars hρ ha X).obj M ⟶ N}
    (h : (derivedExtendScalarsAdjunction hρ ha X).unit.app M ≫
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map f =
      (derivedExtendScalarsAdjunction hρ ha X).unit.app M ≫
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map g) : f = g :=
  ((derivedExtendScalarsAdjunction hρ ha X).homEquiv M N).injective
    (by rwa [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit])

end Pullback

section Comp

/-- **The commutation of `Ψ` with the derived pullbacks is compatible with composition**: for
`g₁₂ = g₁ ≫ g₂`, the composite `Ψ L(g₁₂)^* ≅ Ψ Lg₁^* Lg₂^* ≅ Lg₁^* Ψ Lg₂^* ≅ Lg₁^* Lg₂^* Ψ` is
`Ψ L(g₁₂)^* ≅ L(g₁₂)^* Ψ ≅ Lg₁^* Lg₂^* Ψ`. Both are determined by their transposes, which agree
by the corresponding compatibility of `Res ⋙ Lg^* ≅ Lg^* ⋙ Res`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarRestrictScalarsIso_comp_hom_app'`). -/
@[reassoc]
lemma derivedExtendScalarsPullbackMap_comp {T S R : Scheme.{u}} (g₁ : T ⟶ S) (g₂ : S ⟶ R)
    (g₁₂ : T ⟶ R) (h : g₁₂ = g₁ ≫ g₂) (K : 𝐃(R, Λ)) :
    (derivedExtendScalars hρ ha T).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) g₁ g₂ g₁₂ h).hom.app K) ≫
      (derivedExtendScalarsPullbackMap hρ ha g₁).app ((L((g₂)^*[ModuleCat.{u + 1} Λ])).obj K) ≫
        (L((g₁)^*[ModuleCat.{u + 1} Λ'])).map ((derivedExtendScalarsPullbackMap hρ ha g₂).app K) =
      (derivedExtendScalarsPullbackMap hρ ha g₁₂).app K ≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ') g₁ g₂ g₁₂ h).hom.app
          ((derivedExtendScalars hρ ha R).obj K) := by
  apply derivedExtendScalars_hom_ext hρ ha
  have hu := (derivedExtendScalarsAdjunction hρ ha T).unit.naturality
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) g₁ g₂ g₁₂ h).hom.app K)
  have hι := (leftDerivedUpperStarRestrictScalarsIso ρ g₁).hom.naturality
    ((derivedExtendScalarsPullbackMap hρ ha g₂).app K)
  have hc := (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) g₁ g₂ g₁₂ h).hom.naturality
    ((derivedExtendScalarsAdjunction hρ ha R).unit.app K)
  simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] at hu hι hc
  simp only [Functor.map_comp]
  rw [← reassoc_of% hu, unit_app_comp_map_derivedExtendScalarsPullbackMap_app_assoc,
    unit_app_comp_map_derivedExtendScalarsPullbackMap_app_assoc,
    leftDerivedUpperStarRestrictScalarsIso_comp_hom_app' ρ g₁ g₂ g₁₂ h, reassoc_of% hc, ← hι,
    ← Functor.map_comp_assoc, unit_app_comp_map_derivedExtendScalarsPullbackMap_app,
    Functor.map_comp_assoc]

/-- The commutation of `Ψ` with the derived pullback along the identity is the identity, through
`L(𝟙 X)^* ≅ 𝟭`. -/
@[reassoc]
lemma derivedExtendScalarsPullbackMap_id {X : Scheme.{u}} (K : 𝐃(X, Λ)) :
    (derivedExtendScalarsPullbackMap hρ ha (𝟙 X)).app K ≫
        (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ') X).hom.app _ =
      (derivedExtendScalars hρ ha X).map
        ((leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).hom.app K) := by
  apply derivedExtendScalars_hom_ext hρ ha
  have hu := (derivedExtendScalarsAdjunction hρ ha X).unit.naturality
    ((leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).hom.app K)
  have hi := (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).hom.naturality
    ((derivedExtendScalarsAdjunction hρ ha X).unit.app K)
  simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] at hu hi
  rw [Functor.map_comp, unit_app_comp_map_derivedExtendScalarsPullbackMap_app_assoc,
    leftDerivedUpperStarRestrictScalarsIso_id_hom_app, hi, hu]

/-- The commutation of `Ψ` with the derived pullbacks is compatible with the isomorphism
`Ls^* Lp^* ≅ 𝟭` of a section `s` of `p`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarCompSectionIso`). -/
@[reassoc]
lemma derivedExtendScalarsPullbackMap_compSection {X Y : Scheme.{u}} (s : Y ⟶ X) (p : X ⟶ Y)
    (h : s ≫ p = 𝟙 Y) (K : 𝐃(Y, Λ)) :
    (derivedExtendScalarsPullbackMap hρ ha s).app ((L((p)^*[ModuleCat.{u + 1} Λ])).obj K) ≫
        (L((s)^*[ModuleCat.{u + 1} Λ'])).map ((derivedExtendScalarsPullbackMap hρ ha p).app K) ≫
          (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} Λ') s p h).hom.app _ =
      (derivedExtendScalars hρ ha Y).map
        ((leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} Λ) s p h).hom.app K) := by
  have hc := derivedExtendScalarsPullbackMap_comp hρ ha s p (𝟙 Y) h.symm K
  simp only [leftDerivedUpperStarCompSectionIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.map_comp]
  have hc' : (derivedExtendScalarsPullbackMap hρ ha s).app ((L((p)^*[ModuleCat.{u + 1} Λ])).obj K) ≫
      (L((s)^*[ModuleCat.{u + 1} Λ'])).map ((derivedExtendScalarsPullbackMap hρ ha p).app K) =
      (derivedExtendScalars hρ ha Y).map
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) s p (𝟙 Y) h.symm).inv.app K) ≫
        (derivedExtendScalarsPullbackMap hρ ha (𝟙 Y)).app K ≫
          (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ') s p (𝟙 Y) h.symm).hom.app _ := by
    rw [← hc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp]
  rw [reassoc_of% hc', Iso.hom_inv_id_app_assoc, derivedExtendScalarsPullbackMap_id]

end Comp

section ConstantComplex

/-- The derived extension of scalars of the constant complex is the constant complex,
`Ψ Λ_X ≅ Λ'_X`: the counit `η` of the oplax monoidal structure of the left derived functor of the
strong monoidal extension of scalars
(`CategoryTheory.Functor.isIso_leftDerivedFunctorOplaxMonoidal_η`). -/
noncomputable def derivedExtendScalarsConstantComplexEtaIso (X : Scheme.{u}) :
    (derivedExtendScalars hρ ha X).obj (constantComplex Λ X) ≅ constantComplex Λ' X :=
  haveI := preservesKFlatQuasiIso_extendScalars hρ ha X
  letI := (Sheaf.extendScalars X.smallEtaleTopology ρ).leftDerivedFunctorOplaxMonoidal
  haveI := (Sheaf.extendScalars X.smallEtaleTopology ρ).isIso_leftDerivedFunctorOplaxMonoidal_η
  asIso (Functor.OplaxMonoidal.η (Sheaf.extendScalars X.smallEtaleTopology ρ).leftDerivedFunctor)

/-- `Ψ Λ_X ≅ Λ'_X` exists (`derivedExtendScalarsConstantComplexEtaIso`). -/
lemma nonempty_derivedExtendScalars_obj_constantComplex_iso (X : Scheme.{u}) :
    Nonempty ((derivedExtendScalars hρ ha X).obj (constantComplex Λ X) ≅
      constantComplex Λ' X) :=
  ⟨derivedExtendScalarsConstantComplexEtaIso hρ ha X⟩

variable {S : Scheme.{u}} (c : (derivedExtendScalars hρ ha S).obj (constantComplex Λ S) ≅
  constantComplex Λ' S)

/-- The identification `Ψ Λ_X ≅ Λ'_X` pulled back along `t : X ⟶ S` from an identification
`c : Ψ Λ_S ≅ Λ'_S`: `Ψ Λ_X ≅ Ψ Lt^* Λ_S ≅ Lt^* Ψ Λ_S ≅ Lt^* Λ'_S ≅ Λ'_X`. -/
noncomputable def derivedExtendScalarsConstantComplexIsoOfPullback {X : Scheme.{u}}
    (t : X ⟶ S) :
    (derivedExtendScalars hρ ha X).obj (constantComplex Λ X) ≅ constantComplex Λ' X :=
  (derivedExtendScalars hρ ha X).mapIso (leftDerivedUpperStarConstantComplexIso Λ t).symm ≪≫
    (derivedExtendScalarsPullbackIso hρ ha t).app _ ≪≫
      (L((t)^*[ModuleCat.{u + 1} Λ'])).mapIso c ≪≫ leftDerivedUpperStarConstantComplexIso Λ' t

/-- The identifications `Ψ Λ ≅ Λ'` pulled back from `S` are compatible with the derived
pullbacks: for `tU = e ≫ tX`, the square
```
Ψ Le^* Λ_X ──Ψ(≅)──▶ Ψ Λ_U
    │ ≅                 │ ≅
    ▼                   ▼
Le^* Ψ Λ_X ──≅──▶ Le^* Λ'_X ──≅──▶ Λ'_U
```
commutes. -/
lemma derivedExtendScalarsConstantComplexIsoOfPullback_hom_pullback
    {U X : Scheme.{u}} (e : U ⟶ X) (tU : U ⟶ S) (tX : X ⟶ S) (h : tU = e ≫ tX) :
    (derivedExtendScalars hρ ha U).map (leftDerivedUpperStarConstantComplexIso Λ e).hom ≫
        (derivedExtendScalarsConstantComplexIsoOfPullback hρ ha c tU).hom =
      (derivedExtendScalarsPullbackMap hρ ha e).app _ ≫
        (L((e)^*[ModuleCat.{u + 1} Λ'])).map
          (derivedExtendScalarsConstantComplexIsoOfPullback hρ ha c tX).hom ≫
          (leftDerivedUpperStarConstantComplexIso Λ' e).hom := by
  have hΛ := leftDerivedUpperStarConstantComplexIso_comp Λ e tX tU h
  have hΛ' := leftDerivedUpperStarConstantComplexIso_comp Λ' e tX tU h
  have hp := derivedExtendScalarsPullbackMap_comp hρ ha e tX tU h (constantComplex Λ S)
  have hn₁ := (derivedExtendScalarsPullbackMap hρ ha e).naturality
    (leftDerivedUpperStarConstantComplexIso Λ tX).inv
  have hn₂ := (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ') e tX tU h).inv.naturality c.hom
  simp only [Functor.comp_obj, Functor.comp_map] at hn₁ hn₂
  -- `Ψ(c_Λ⁻¹) ≫ (Ψ L(tU)^* ≅ L(tU)^* Ψ) = (Ψ Le^* L(tX)^* ≅ Le^* L(tX)^* Ψ) ≫ c_Λ'⁻¹`
  have hp' : (derivedExtendScalars hρ ha U).map
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) e tX tU h).inv.app (constantComplex Λ S)) ≫
        (derivedExtendScalarsPullbackMap hρ ha tU).app (constantComplex Λ S) =
      (derivedExtendScalarsPullbackMap hρ ha e).app _ ≫
        (L((e)^*[ModuleCat.{u + 1} Λ'])).map
          ((derivedExtendScalarsPullbackMap hρ ha tX).app (constantComplex Λ S)) ≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ') e tX tU h).inv.app _ := by
    rw [← cancel_epi ((derivedExtendScalars hρ ha U).map
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) e tX tU h).hom.app _)),
      ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp, reassoc_of% hp, Iso.hom_inv_id_app, Category.comp_id]
  simp only [derivedExtendScalarsConstantComplexIsoOfPullback, hΛ, hΛ', Iso.trans_hom,
    Iso.symm_hom, Iso.trans_inv, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, derivedExtendScalarsPullbackIso_hom, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp,
    reassoc_of% hp', ← reassoc_of% hn₂, Iso.inv_hom_id_app_assoc, reassoc_of% hn₁]

end ConstantComplex

end Etale

end AlgebraicGeometry
