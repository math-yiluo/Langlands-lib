/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Equivalence

/-! # Transport of chosen derived localizations along a scheme isomorphism

Source: Stacks Project, Tags 05RU and 09IR.
(blueprint: lem-pc-scheme-iso-derived-localizations).
-/

@[expose] public section

universe u v w
open CategoryTheory CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
private noncomputable def moduleIsoEquivalence {S T : Scheme.{u}} (s : S ≅ T) :
    SheafOfModules.{u} (moduleRings S.toRingedSpace) ≌
      SheafOfModules.{u} (moduleRings T.toRingedSpace) :=
  CategoryTheory.Equivalence.mk (SheafOfModules.pushforward s.hom.toRingCatSheafHom)
    (SheafOfModules.pushforward s.inv.toRingCatSheafHom)
    ((Modules.pushforwardComp s.hom s.inv ≪≫
      Modules.pushforwardCongr s.hom_inv_id ≪≫ Modules.pushforwardId S).symm)
    (Modules.pushforwardComp s.inv s.hom ≪≫
      Modules.pushforwardCongr s.inv_hom_id ≪≫ Modules.pushforwardId T)

private theorem hasDerivedCategory_of_equivalence {C D : Type v}
    [Category.{u} C] [Category.{u} D] [Abelian C] [Abelian D]
    (e : C ≌ D) [HasDerivedCategory.{w} D] : Nonempty (HasDerivedCategory.{w} C) := by
  have : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : e.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let eC := e.mapHomologicalComplex (ComplexShape.up ℤ)
  let L := eC.functor ⋙ (DerivedCategory.Q (C := D))
  have : L.IsLocalization (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) := by
    refine Functor.IsLocalization.of_equivalence_source
      (DerivedCategory.Q (C := D)) (HomologicalComplex.quasiIso D (ComplexShape.up ℤ))
      L (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) eC.symm ?_ ?_ ?_
    · intro K M f hf
      have : QuasiIso f := hf
      exact (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)).le_isoClosure _
        (show QuasiIso (eC.inverse.map f) from
          (show QuasiIso ((e.inverse.mapHomologicalComplex (ComplexShape.up ℤ)).map f)
            from inferInstance))
    · intro K M f hf
      have : QuasiIso f := hf
      have : QuasiIso (eC.functor.map f) :=
        (show QuasiIso ((e.functor.mapHomologicalComplex (ComplexShape.up ℤ)).map f)
          from inferInstance)
      exact inferInstanceAs (IsIso (DerivedCategory.Q.map (eC.functor.map f)))
    · exact (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight eC.counitIso _ ≪≫ Functor.leftUnitor _
  exact ⟨{ D := DerivedCategory D, L := L }⟩

set_option backward.isDefEq.respectTransparency false in
/-- A scheme isomorphism transfers the existence of chosen derived localizations,
including the localized open sites, without increasing the morphism universe.
Source: Stacks Project, Tags 05RU and 09IR; the localization-existence part of
step 1 of lem-pc-affine-derived-open-transport.
(blueprint: lem-pc-scheme-iso-derived-localizations).

Proof: Pushforward along s.hom and s.inv gives inverse exact equivalences of
module-sheaf categories. Apply these functors degreewise to cochain complexes;
exactness identifies homology and hence identifies quasi-isomorphisms in both
directions. Compose the forward complex equivalence with the supplied localization
on Y. The universal property of localization, transported through the inverse
complex equivalence, proves that this composite is a localization on X. Its target
is the chosen derived category of Y, so its morphisms remain in universe w.
For an open V of X, let W be its image under the homeomorphism s.hom. The
isomorphism identifies the localized sites at V and W, including their structure
ring sheaves. The same argument with this module-sheaf equivalence and the chosen
localization at W supplies the localization at V. Carry this out for all V.
The equivalences use the structure maps of s, and the construction applies also to
empty schemes and empty opens; no choice of a nonempty point is involved. -/
theorem exists_scheme_iso_derived_localizations {X Y : Scheme.{u}} (s : X ≅ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))] :
    ∃ _ : HasDerivedCategory.{w}
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)),
      Nonempty (∀ V : X.Opens, HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V)))  := by
  obtain ⟨hD⟩ := hasDerivedCategory_of_equivalence (moduleIsoEquivalence s)
  refine ⟨hD, ?_⟩
  have hO : ∀ V : X.Opens, Nonempty (HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))) := by
    intro V
    let W := s.hom ''ᵁ V
    let e := (Modules.overEquiv V).trans
      ((moduleIsoEquivalence (s.hom.isoImage V)).trans (Modules.overEquiv W).symm)
    exact hasDerivedCategory_of_equivalence e
  exact ⟨fun V ↦ Classical.choice (hO V)⟩

end AlgebraicGeometry.Scheme
