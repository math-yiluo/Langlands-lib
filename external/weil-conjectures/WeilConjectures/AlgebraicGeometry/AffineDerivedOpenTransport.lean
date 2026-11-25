/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import WeilConjectures.AlgebraicGeometry.SchemeIsoDerivedLocalizations
import WeilConjectures.AlgebraicGeometry.SchemeIsoDerivedOpenAdjunction
import WeilConjectures.AlgebraicGeometry.SchemeIsoDerivedQCoh
import WeilConjectures.AlgebraicGeometry.SchemeIsoPerfectTransport
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Transport of derived open restriction along an affine presentation
Source: Stacks Project, Tags 079W and 09IR.
(blueprint: lem-pc-affine-derived-open-transport).
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private noncomputable def moduleIsoEquivalence {S T : Scheme.{u}} (s : S ≅ T) :
    SheafOfModules.{u} (moduleRings S.toRingedSpace) ≌
      SheafOfModules.{u} (moduleRings T.toRingedSpace) :=
  CategoryTheory.Equivalence.mk (SheafOfModules.pushforward s.hom.toRingCatSheafHom)
    (SheafOfModules.pushforward s.inv.toRingCatSheafHom)
    ((Scheme.Modules.pushforwardComp s.hom s.inv ≪≫
      Scheme.Modules.pushforwardCongr s.hom_inv_id ≪≫ Scheme.Modules.pushforwardId S).symm)
    (Scheme.Modules.pushforwardComp s.inv s.hom ≪≫
      Scheme.Modules.pushforwardCongr s.inv_hom_id ≪≫ Scheme.Modules.pushforwardId T)

set_option backward.isDefEq.respectTransparency false in
/-- An isomorphism with a spectrum transports derived restriction, its right adjoint,
quasi-coherence, perfection, support, and the shift structure. No detector assertion is
part of this statement: it holds for every derived object on the spectrum.
Source: Stacks Project, Tag 079W (derived adjunction), and Tag 09IR (affine presentation).
(blueprint: lem-pc-affine-derived-open-transport).

Proof: Pullback and pushforward along a scheme isomorphism are mutually inverse exact
functors on module sheaves. Apply them termwise and localize at quasi-isomorphisms.
The displayed localization comparison specifies its functor as termwise restriction
along a.inv, so the object transport is fixed by a, rather than by mere existence.
The resulting equivalence also transports the chosen localization, supplying derived
categories with the same morphism universe on the spectrum and on all its opens.
The restriction square commutes by the identification of sections on corresponding
opens. Open restriction is exact and its underived right adjoint is direct image;
K-injective resolutions of module sheaves yield its unbounded derived right adjoint
and adjunction (Tag 079W). Conjugate this adjunction by the two equivalences to obtain
the adjunction on X. Its unit is the transported unit followed by the invertible
restriction comparison; hence the units are invertible at corresponding objects
simultaneously. Exactness gives compatibility with homology and shifts. Stalks at
corresponding points are isomorphic, so quasi-coherence and vanishing transfer in
both directions. Finite free local representatives and their retractions transfer,
which preserves perfection. The termwise functors commute with cochain shifts.
Their canonical shift isomorphisms
descend through localization and satisfy the zero and addition coherence identities,
supplying the displayed CommShift structure. All constructions
apply to the empty scheme and to the empty and full opens as well. -/
theorem affine_derived_open_transport
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (A : Type u) [CommRing A] (a : Spec (.of A) ≅ X) (U : X.Opens) :
    ∃ hD : HasDerivedCategory.{w}
        (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)),
    letI := hD
    ∃ hO : ∀ V : (Spec (.of A)).Opens, HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over V)),
    letI := hO
    ∃ (F : schemeDerivedCategory (Spec (.of A)) ≌ schemeDerivedCategory X)
      (RS : DerivedCategory
        (SheafOfModules.{u}
          ((moduleRings (Spec (.of A)).toRingedSpace).over (a.hom ⁻¹ᵁ U))) ⥤
        schemeDerivedCategory (Spec (.of A)))
      (RX : DerivedCategory
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ⥤
        schemeDerivedCategory X)
      (adjS : (SheafOfModules.overFunctor.{u}
        (moduleRings (Spec (.of A)).toRingedSpace) (a.hom ⁻¹ᵁ U)).mapDerivedCategory ⊣ RS)
      (adjX : (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) U).mapDerivedCategory ⊣ RX),
      Nonempty (DerivedCategory.Q ⋙ F.functor ≅
        (@Functor.mapHomologicalComplex ℤ
          (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) _ _ _ _
          (Scheme.Modules.restrictFunctor a.inv)
          ⟨fun M N ↦ (Scheme.Modules.restrictFunctor a.inv).map_zero M N⟩
          (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q) ∧
      (∀ Q, schemeDerivedQCohProperty (Spec (.of A)) Q →
        schemeDerivedQCohProperty X (F.functor.obj Q)) ∧
      (∀ K, schemeDerivedQCohProperty X K →
        schemeDerivedQCohProperty (Spec (.of A)) (F.inverse.obj K)) ∧
      (∀ Q, Scheme.IsPerfect (Spec (.of A)) Q →
        Scheme.IsPerfect X (F.functor.obj Q)) ∧
      (∀ Q, (∀ (n : ℤ) (x : Spec (.of A)), x ∈ a.hom ⁻¹ᵁ U →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) n).obj
            Q).val.presheaf x))) →
        ∀ (n : ℤ) (x : X), x ∈ U →
          Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj
              (F.functor.obj Q)).val.presheaf x))) ∧
      Nonempty (F.functor.CommShift ℤ) ∧
      (∀ K, IsIso (adjS.unit.app (F.inverse.obj K)) ↔ IsIso (adjX.unit.app K)) := by
  obtain ⟨hD, ⟨hO⟩⟩ := Scheme.exists_scheme_iso_derived_localizations a
  let := hD
  let := hO
  let e₀ := moduleIsoEquivalence a
  have : e₀.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : e₀.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let e := e₀.mapDerivedCategory
  have hf : e.functor = e₀.functor.mapDerivedCategory := rfl
  let he := e₀.functor.mapDerivedCategoryFactors
  let hi := e₀.inverse.mapDerivedCategoryFactors
  let c : e₀.functor ≅ Scheme.Modules.restrictFunctor a.inv :=
    Adjunction.leftAdjointUniq e₀.toAdjunction (Scheme.Modules.restrictAdjunction a.inv)
  let : (Scheme.Modules.restrictFunctor a.inv).PreservesZeroMorphisms :=
    ⟨fun M N ↦ (Scheme.Modules.restrictFunctor a.inv).map_zero M N⟩
  let hc := he ≪≫ Functor.isoWhiskerRight (NatIso.mapHomologicalComplex c (ComplexShape.up ℤ))
    DerivedCategory.Q
  obtain ⟨RS, RX, adjS, adjX, hu⟩ :=
    Scheme.exists_scheme_iso_derived_open_adjunction a e he U
  refine ⟨hD, hO, e, RS, RX, adjS, adjX, ⟨hc⟩, ?_, ?_, ?_, ?_, ?_, hu⟩
  · intro Q hQ
    exact Scheme.scheme_iso_derived_inverse_preserves_qcoh a.symm e.symm hi ⟨Q, hQ⟩
  · intro K hK
    exact Scheme.scheme_iso_derived_inverse_preserves_qcoh a e he ⟨K, hK⟩
  · intro Q hQ
    exact Scheme.scheme_iso_derived_inverse_preserves_perfect a.symm e.symm hi Q hQ
  · intro Q hQ n x hx
    rw [hf]
    let H := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) n).obj Q
    let h := (e₀.functor.mapDerivedCategoryHomologyFunctorIso n).app Q
    let T := Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} x
    let st := (T.mapIso h).symm ≪≫ T.mapIso (c.app H) ≪≫
      (Scheme.Modules.restrictStalkNatIso a.inv x).app H
    have hs := hQ n (a.inv x) (by simpa using hx)
    have : Subsingleton ↑((Scheme.Modules.toPresheaf (Spec (.of A)) ⋙
        TopCat.Presheaf.stalkFunctor Ab.{u} (a.inv x)).obj H) := by
      simpa only [H, Functor.comp_obj, Scheme.Modules.presheaf, Scheme.Modules.toPresheaf_obj,
        TopCat.Presheaf.stalkFunctor_obj] using hs
    simpa only [T, Functor.comp_obj, Scheme.Modules.presheaf, Scheme.Modules.toPresheaf_obj,
      TopCat.Presheaf.stalkFunctor_obj] using
      Function.Injective.subsingleton (ConcreteCategory.bijective_of_isIso st.hom).1
  · change Nonempty (e₀.functor.mapDerivedCategory.CommShift ℤ)
    exact ⟨inferInstance⟩

end AlgebraicGeometry
