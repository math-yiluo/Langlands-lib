/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedScalarRestrictionDirectImage
import all WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedScalarRestrictionDirectImage
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantExact

/-!
# Direct image and restriction of scalars for arbitrary coefficient rings

The derived direct image commutes with restriction of scalars along an arbitrary morphism of
commutative rings `φ: A →+* B`: the canonical comparison
`AlgebraicGeometry.ProEtale.fixedScalarRestrictionDirectImageMap` is invertible without any
finiteness assumption on `A` and `B`
(`AlgebraicGeometry.ProEtale.isIso_fixedScalarRestrictionDirectImageMap`). The only input of
the finite-coefficient proof using finiteness is the identification of the inverse image of a
constant ring sheaf with the constant ring sheaf, which holds for every ring
(`AlgebraicGeometry.ProEtale.isIso_proEtaleConstantInverseImageMap_commRing`).

## References

* Stacks, Tags 0D6E and 07A6
* Stacks Tags 0H7J and 09A5
* Stacks Tag 03D2
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
-- Avoid an unrelated derived-adjoint search while elaborating the mate identities.
-- Restore the imported instance at the end of this module.
attribute [-instance] AlgebraicGeometry.ProEtale.pbcRestriction_isRightAdjoint

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStar

/-- The direct-image comparison is the mate of the canonical inverse-image comparison. -/
theorem fixedScalarRestrictionDirectImageMap_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    fixedScalarRestrictionDirectImageMap φ f =
      mateEquiv (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
        (fixedScalarRestrictionPullback φ f).hom := by
  rw [fixedScalarRestrictionDirectImageMap]

/-- The inverse image of a constant sheaf of commutative rings is the constant sheaf, for an
arbitrary ring: both are left adjoint to the global sections, as the base change of the
terminal object is terminal. -/
theorem isIso_proEtaleConstantInverseImageMap_commRing {U V : Scheme.{u}} (f : U ⟶ V)
    (Λ : Type (u + 1)) [CommRing Λ] :
    IsIso (Scheme.proEtaleConstantInverseImageMap f CommRingCat.{u + 1}
      (CommRingCat.of Λ)) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.defeqAttrib.useBackward true in
  let G := Scheme.proEtaleBaseChange f
  let hV : IsTerminal (⊤_ V.ProEt) := terminalIsTerminal
  let hU := hV.isTerminalObj G _
  let aV := constantSheafAdj (Scheme.ProEt.topology V) CommRingCat.{u + 1} hV
  let adj := Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}
  let a := (aV.comp adj).ofNatIsoRight (Iso.refl _)
  let b := constantSheafAdj (Scheme.ProEt.topology U) CommRingCat.{u + 1} hU
  let e := a.leftAdjointUniq b
  have he : Scheme.proEtaleConstantInverseImageMap f CommRingCat.{u + 1}
      (CommRingCat.of Λ) = e.hom.app (CommRingCat.of Λ) := by
    apply (a.homEquiv _ _).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    simp only [a, Adjunction.homEquiv_ofNatIsoRight_apply, Iso.refl_hom,
      NatTrans.id_app, Category.comp_id, Adjunction.comp_homEquiv]
    dsimp [Scheme.proEtaleConstantInverseImageMap]
    rw [← Adjunction.homEquiv_counit]
    dsimp only [adj]
    rw [Equiv.apply_symm_apply]
    dsimp only [Scheme.proEtaleConstantDirectImageMap, aV, constantSheafAdj]
    rw [Adjunction.comp_homEquiv]
    change (constantPresheafAdj CommRingCat.{u + 1} hV).homEquiv _ _
      (((sheafificationAdjunction (Scheme.ProEt.topology V) CommRingCat.{u + 1}).homEquiv
        _ _)
        (((sheafificationAdjunction (Scheme.ProEt.topology V) CommRingCat.{u + 1}).homEquiv
          _ _).symm _)) = _
    rw [Equiv.apply_symm_apply]
    rfl
  rw [he]
  infer_instance

section ScalarModels
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The inverse image of the constant ring sheaf is the constant ring sheaf. -/
private noncomputable def scalarPullbackIso' {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type (u + 1)) [CommRing A] :
    (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
        (scalarRing (Scheme.ProEt.topology Y) A) ≅
      scalarRing (Scheme.ProEt.topology X) A :=
  have := isIso_proEtaleConstantInverseImageMap_commRing f A
  asIso (Scheme.proEtaleConstantInverseImageMap f CommRingCat.{u + 1} (CommRingCat.of A))

private theorem scalarDirectImage_unit' {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type (u + 1)) [CommRing A] :
    scalarUnit (Scheme.ProEt.topology Y) A ≫
      Functor.whiskerRight (Scheme.proEtaleRingDirectImageMap f
        (scalarRing (Scheme.ProEt.topology Y) A) (scalarRing (Scheme.ProEt.topology X) A)
        (scalarPullbackIso' f A)).hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) =
      Functor.whiskerLeft (Scheme.proEtaleBaseChange f).op
        (scalarUnit (Scheme.ProEt.topology X) A) := by
  have hr : Scheme.proEtaleRingDirectImageMap f
      (scalarRing (Scheme.ProEt.topology Y) A) (scalarRing (Scheme.ProEt.topology X) A)
      (scalarPullbackIso' f A) =
      Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (CommRingCat.of A) :=
    ((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _
  rw [hr]
  have h := Equiv.apply_symm_apply
    ((sheafificationAdjunction (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of A))
      ((Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
        (scalarRing (Scheme.ProEt.topology X) A)))
    (Functor.whiskerLeft (Scheme.proEtaleBaseChange f).op
      (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))))
  exact congrArg (fun t ↦ Functor.whiskerRight t
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) h

private theorem fixedRestriction_resolution_quasiIso'
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)) ℤ)
    [I.IsKInjective]
    (J : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ℤ)
    [J.IsKInjective]
    (j : ((Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).mapHomologicalComplex
      (.up ℤ)).obj I ⟶ J) [QuasiIso j] :
    QuasiIso (((lowerStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).map j) := by
  let RX := scalarRing (Scheme.ProEt.topology X) A
  let SX := scalarRing (Scheme.ProEt.topology X) B
  let RY := scalarRing (Scheme.ProEt.topology Y) A
  let ax := scalarChange X φ
  let c := scalarPullbackIso' f A
  let H := Sheaf.restrictScalars (Scheme.ProEt.topology X) φ
  let G := lowerStar (ModuleCat.{u + 1} A) f
  let r := Scheme.proEtaleRingRestrictScalars ax
  let p := Scheme.proEtaleRingModuleDirectImage f RY RX c
  have hEM : (scalarSectionsAt X B).IsEquivalence := scalarSectionsAt_equiv X B
  have hEA : (scalarSectionsAt X A).IsEquivalence := scalarSectionsAt_equiv X A
  have hEB : (scalarSectionsAt Y A).IsEquivalence := scalarSectionsAt_equiv Y A
  let EM := (scalarSectionsAt X B).inv
  let EA := (scalarSectionsAt X A).inv
  let EB := (scalarSectionsAt Y A).inv
  have : EM.IsEquivalence := inferInstance
  have : EA.IsEquivalence := inferInstance
  have : EB.IsEquivalence := inferInstance
  have : EM.Additive := EM.additive_of_preserves_binary_products
  have : EA.Additive := EA.additive_of_preserves_binary_products
  have : EB.Additive := EB.additive_of_preserves_binary_products
  have : EA.PreservesHomology := inferInstance
  have : EB.PreservesHomology := inferInstance
  have : EB.ReflectsIsomorphisms := inferInstance
  have : EM.PreservesKInjectiveComplexes := inferInstance
  have : EA.PreservesKInjectiveComplexes := inferInstance
  have : H.Additive := inferInstanceAs (Sheaf.restrictScalars _ φ).Additive
  have : G.Additive := inferInstanceAs (lowerStar (ModuleCat.{u + 1} A) f).Additive
  have : r.Additive := inferInstanceAs (Scheme.proEtaleRingRestrictScalars ax).Additive
  have : p.Additive := inferInstanceAs
    (Scheme.proEtaleRingModuleDirectImage f RY RX c).Additive
  let α₀ : r ⋙ scalarSectionsAt X A ≅ scalarSectionsAt X B ⋙ H :=
    scalarRestrictionIso (Scheme.ProEt.topology X) φ _ _ _ _ _ (scalarChange_unit X φ)
  let α : EM ⋙ r ≅ H ⋙ EA :=
    inverseSquare (scalarSectionsAt X B) (scalarSectionsAt X A) r H α₀
  let β₀ : p ⋙ scalarSectionsAt Y A ≅ scalarSectionsAt X A ⋙ G :=
    scalarDirectImageIso (Scheme.ProEt.topology X) (Scheme.ProEt.topology Y)
      (Scheme.proEtaleBaseChange f) A _ _ _ _ _ (scalarDirectImage_unit' f A)
  let β : EA ⋙ p ≅ G ⋙ EB :=
    inverseSquare (scalarSectionsAt X A) (scalarSectionsAt Y A) p G β₀
  apply Scheme.quasiIso_map_of_models EM EA EB r p H G α β ?_ I J j
  intro I' hI J' hJ j' hj
  have : I'.IsKInjective := hI
  have : J'.IsKInjective := hJ
  have : QuasiIso j' := hj
  exact Scheme.restriction_directImage_quasiIso f RY RX SX ax c I' J' j'

end ScalarModels

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restriction of scalars along an arbitrary morphism of commutative rings commutes with the
unbounded derived direct image: the canonical mate comparison is invertible. -/
theorem isIso_fixedScalarRestrictionDirectImageMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (fixedScalarRestrictionDirectImageMap φ f) := by
  apply derived_mate_isIso
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (upperStarRestrictScalarsIso φ f) (fixedScalarRestrictionDirectImageMap φ f)
    (𝟙 _) (restriction_mate_eq φ f) (restriction_underived_mate φ f)
  intro I hI J hJ j hj
  have : I.IsKInjective := hI
  have : J.IsKInjective := hJ
  have : QuasiIso j := hj
  exact fixedRestriction_resolution_quasiIso' φ f I J j

end AlgebraicGeometry.ProEtale

attribute [instance] AlgebraicGeometry.ProEtale.pbcRestriction_isRightAdjoint
