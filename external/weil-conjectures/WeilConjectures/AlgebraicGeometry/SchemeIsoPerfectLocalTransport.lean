/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
import all WeilConjectures.AlgebraicGeometry.DerivedPullbackPerfect
import all WeilConjectures.AlgebraicGeometry.SchemeIsoDerivedRestrictionSquare

@[expose] public section

universe u w₁ w₂

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency true in
/-- The derived equivalence on corresponding open sites commutes with restriction.
Source: Stacks Project, Tag 09IR; restriction-comparison part of step 1 of
lem-pc-affine-derived-open-transport.
(blueprint: lem-pc-scheme-iso-derived-restriction-square).

Proof: Restrict s to the isomorphism s.hom.preimageIso U between the open subschemes.
Pushforward along this isomorphism and its inverse gives an exact equivalence on
module sheaves. Compose with Modules.overEquiv on each side to obtain an exact
module-sheaf equivalence on the two localized open sites. Apply its termwise
complex functor and localize to obtain the displayed equivalence eU.
The global module-sheaf pushforward along s is isomorphic to restriction along
s.inv, since both are left adjoint to pushforward along s.inv. Similarly identify
the open isomorphism pushforward with restriction along its inverse. Compose
Modules.overFunctorEquiv, restrictFunctorComp and restrictFunctorCongr with the
identity s.hom.preimageIso_hom_ι (or its inverse version). These identify the two
composites of underived functors, by restriction to the same opens with the same
structure-ring maps. Their termwise natural comparison descends by localization.
The given he identifies e.functor with the derived isomorphism pushforward by
uniqueness of localization. Composing this comparison with the localized module
restriction comparison yields the displayed square. The argument needs no
quasi-coherence, perfection or nonempty points and includes empty and full U. -/
private theorem localRestrictionSquare {X Y : Scheme.{u}} (s : X ≅ Y)
    [HasDerivedCategory.{w₁} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w₂} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ V : X.Opens, HasDerivedCategory.{w₁}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))]
    [∀ U : Y.Opens, HasDerivedCategory.{w₂}
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (e : schemeDerivedCategory X ≌ schemeDerivedCategory Y)
    (he : DerivedCategory.Q ⋙ e.functor ≅
      (@Functor.mapHomologicalComplex ℤ
        (SheafOfModules.{u} (moduleRings X.toRingedSpace))
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) _ _ _ _
        (SheafOfModules.pushforward s.hom.toRingCatSheafHom)
        ⟨fun _ _ ↦ rfl⟩ (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q)
    (U : Y.Opens) :
    ∃ eO : SheafOfModules.{u}
        ((moduleRings X.toRingedSpace).over (s.hom ⁻¹ᵁ U)) ≌
      SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U),
      ∃ (_ : eO.functor.Additive) (_ : eO.inverse.Additive),
      Nonempty (e.functor ⋙ (SheafOfModules.overFunctor.{u}
        (moduleRings Y.toRingedSpace) U).mapDerivedCategory ≅
        (SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) (s.hom ⁻¹ᵁ U)).mapDerivedCategory ⋙
            eO.functor.mapDerivedCategory) ∧
      Nonempty (eO.inverse ≅ Modules.localizedPullback s.hom U) := by
  let V := s.hom ⁻¹ᵁ U
  let i := s.hom.preimageIso U
  let e₀ := moduleIsoEquivalence s
  let eI := moduleIsoEquivalence i
  let EV := Modules.overEquiv V
  let EU := Modules.overEquiv U
  let eO := (EV.trans eI).trans EU.symm
  have : e₀.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : eI.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : eO.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : eO.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let LX := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) V
  let LY := SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) U
  let cG : e₀.functor ≅ Modules.restrictFunctor s.inv :=
    Adjunction.leftAdjointUniq e₀.toAdjunction (Modules.restrictAdjunction s.inv)
  let cI : eI.functor ≅ Modules.restrictFunctor i.inv :=
    Adjunction.leftAdjointUniq eI.toAdjunction (Modules.restrictAdjunction i.inv)
  have fac : U.ι ≫ s.inv = i.inv ≫ V.ι := by
    apply (cancel_mono s.hom).mp
    simp only [Category.assoc, s.inv_hom_id, Category.comp_id]
    exact (Scheme.Hom.preimageIso_inv_ι s.hom U).symm
  let h0 : (e₀.functor ⋙ LY) ⋙ EU.functor ≅ (LX ⋙ EV.functor) ⋙ eI.functor :=
    Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ (Modules.overFunctorEquiv U) ≪≫
      isoWhiskerRight cG _ ≪≫
      (Modules.restrictFunctorComp U.ι s.inv).symm ≪≫
      Modules.restrictFunctorCongr fac ≪≫
      Modules.restrictFunctorComp i.inv V.ι ≪≫
      isoWhiskerRight (Modules.overFunctorEquiv V).symm _ ≪≫
      isoWhiskerLeft _ cI.symm
  let h1 : e₀.functor ⋙ LY ≅ LX ⋙ eO.functor :=
    (Functor.rightUnitor _).symm ≪≫ isoWhiskerLeft _ EU.unitIso ≪≫
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight h0 EU.inverse ≪≫
      isoWhiskerRight (Functor.associator _ _ _) _ ≪≫ Functor.associator _ _ _
  let : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ))
      (e₀.functor.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      e.functor := ⟨he⟩
  let beta : e.functor ≅ e₀.functor.mapDerivedCategory :=
    Localization.liftNatIso DerivedCategory.Q
      (HomologicalComplex.quasiIso
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ))
      (e₀.functor.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (e₀.functor.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      e.functor e₀.functor.mapDerivedCategory (Iso.refl _)
  let d := eO.mapDerivedCategory
  refine ⟨eO, inferInstance, inferInstance, ⟨?_⟩, ⟨?_⟩⟩
  · exact isoWhiskerRight beta LY.mapDerivedCategory ≪≫
    Functor.mapDerivedCategoryCompIso e₀.functor LY ≪≫
      Functor.mapDerivedCategoryNatIso h1 ≪≫ (Functor.mapDerivedCategoryCompIso LX eO.functor).symm
  · let cInv : eI.inverse ≅ Modules.restrictFunctor i.hom :=
      Adjunction.leftAdjointUniq eI.symm.toAdjunction (Modules.restrictAdjunction i.hom)
    change EU.functor ⋙ eI.inverse ⋙ EV.inverse ≅
      EU.functor ⋙ Modules.pullback (s.hom.resLE U V le_rfl) ⋙ EV.inverse
    have hi : i.hom = s.hom.resLE U V le_rfl := by
      apply (cancel_mono U.ι).mp
      exact (s.hom.preimageIso_hom_ι U).trans (s.hom.resLE_comp_ι le_rfl).symm
    exact isoWhiskerLeft EU.functor
      (isoWhiskerRight (cInv ≪≫ Modules.restrictFunctorIsoPullback i.hom ≪≫
        Modules.pullbackCongr hi) EV.inverse)

set_option backward.isDefEq.respectTransparency true in
/-- Local transport of a perfect model along a scheme isomorphism. The proof follows the
localization comparison, restriction compatibility, and transport of strictly perfect
complexes described in Stacks Project, perfect.tex, Tag 08EB.
(blueprint: lem-pc-scheme-iso-perfect-local-transport) -/
theorem scheme_iso_local_perfect_transport {X Y : Scheme.{u}}
    (s : X ≅ Y)
    [HasDerivedCategory.{w₁} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w₂} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w₁} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [∀ V : Y.Opens,
      HasDerivedCategory.{w₂} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V))]
    (e : schemeDerivedCategory X ≌ schemeDerivedCategory Y)
    (he : DerivedCategory.Q ⋙ e.functor ≅
      (@Functor.mapHomologicalComplex ℤ
        (SheafOfModules.{u} (moduleRings X.toRingedSpace))
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) _ _ _ _
        (SheafOfModules.pushforward s.hom.toRingCatSheafHom)
        ⟨fun _ _ ↦ rfl⟩ (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q)
    (E : schemeDerivedCategory Y) (x : X)
    (V : Y.Opens) (hx : s.hom.base x ∈ V)
    (K : CochainComplex
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V)) ℤ)
    (hK : IsStrictlyPerfect Y V K)
    (hE : Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings Y.toRingedSpace) V).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj K)) :
    ∃ U : X.Opens, x ∈ U ∧
      ∃ K' : CochainComplex
          (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ,
        IsStrictlyPerfect X U K' ∧
        Nonempty ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj (e.inverse.obj E) ≅
          DerivedCategory.Q.obj K') := by
  obtain ⟨eO, hA, hB, ⟨square⟩, ⟨inverseIso⟩⟩ := localRestrictionSquare s e he V
  have : eO.functor.Additive := hA
  have : eO.inverse.Additive := hB
  let d := eO.mapDerivedCategory
  let RX := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) (s.hom ⁻¹ᵁ V)
  let RY := SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) V
  let F := Modules.localizedPullback s.hom V
  let K' := (F.mapHomologicalComplex (.up ℤ)).obj K
  refine ⟨s.hom ⁻¹ᵁ V, hx, K',
    AlgebraicGeometry.localizedPullbackStrictlyPerfect s.hom V K hK, ?_⟩
  obtain ⟨hE⟩ := hE
  let a : RX.mapDerivedCategory.obj (e.inverse.obj E) ≅
      d.inverse.obj (RY.mapDerivedCategory.obj E) :=
    d.unitIso.app _ ≪≫ d.inverse.mapIso (square.app (e.inverse.obj E)).symm ≪≫
      d.inverse.mapIso (RY.mapDerivedCategory.mapIso (e.counitIso.app E))
  exact ⟨a ≪≫ d.inverse.mapIso hE ≪≫
    eO.inverse.mapDerivedCategoryFactors.app K ≪≫
    DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex inverseIso (.up ℤ)).app K)⟩

end AlgebraicGeometry.Scheme
