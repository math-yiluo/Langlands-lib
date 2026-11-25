/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Locally.LocallyClosedModuleExtensionData
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleIdentifiedOpenClosed
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# A fixed closed-then-open model for locally closed extension

The functors here are composites of closed direct image and open extension.

## Implementation details

`ModelPresentation` records the closed-then-open functor together with an equality fixing its
data; its nominal type keeps kernel reduction of module objects small.

## References

* Stacks, Tag 01IO
* Stacks, Tags 03DI--03DJ
* Stacks, Tags 09AA, 09BN
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

namespace LocallyClosedCoefficientImmersion

/-- A closed-then-open factorization of a coefficient immersion, with its coefficient
identification. -/
structure ExtensionFactorization {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) where
  middle : LocallyClosedCoefficients.{u}
  closed : LocallyClosedCoefficientImmersion S middle
  openMap : LocallyClosedCoefficientImmersion middle X
  isClosed : IsClosedImmersion closed.hom
  isOpen : IsOpenImmersion openMap.hom
  composite : openMap.comp closed = a
  closedIsOpen : IsOpenImmersion a.hom → IsOpenImmersion closed.hom
  openIsClosed : IsClosedImmersion a.hom → IsClosedImmersion openMap.hom

attribute [instance] ExtensionFactorization.isClosed ExtensionFactorization.isOpen

/-- Existence of a coefficient-compatible closed-then-open factorization. -/
theorem factorization_nonempty {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) : Nonempty (ExtensionFactorization a) := by
  rcases a with ⟨f, hf, cf⟩
  have hfactor : ∃ (V : Scheme.{u}) (c : S.scheme ⟶ V) (v : V ⟶ X.scheme),
      IsClosedImmersion c ∧ IsOpenImmersion v ∧ c ≫ v = f ∧
        (IsOpenImmersion f → IsOpenImmersion c) ∧
        (IsClosedImmersion f → IsClosedImmersion v) := by
    by_cases hc : IsClosedImmersion f
    · exact ⟨X.scheme, f, 𝟙 _, hc, inferInstance, Category.comp_id _,
        fun h ↦ h, fun _ ↦ inferInstance⟩
    by_cases ho : IsOpenImmersion f
    · exact ⟨S.scheme, 𝟙 _, f, inferInstance, ho, Category.id_comp _,
        fun _ ↦ inferInstance, fun h ↦ h⟩
    obtain ⟨V, c, v, hc', hv, h⟩ := IsImmersion.isImmersion_iff_exists.mp hf
    exact ⟨V, c, v, hc', hv, h, fun h ↦ (ho h).elim, fun h ↦ (hc h).elim⟩
  obtain ⟨V, c, v, hc, hv, h, hco, hvc⟩ := hfactor
  subst f
  let := hc
  let := hv
  let : IsNoetherian X.scheme := ⟨⟩
  let : IsLocallyNoetherian V := isLocallyNoetherian_of_isOpenImmersion v
  let : NoetherianSpace V := v.isOpenEmbedding.isInducing.noetherianSpace
  let B : LocallyClosedCoefficients.{u} :=
    { scheme := V
      locallyNoetherian := inferInstance
      compact := inferInstance
      ring := (proEtaleSheafInverseImage v CommRingCat.{u + 1}).obj X.ring }
  let vv : LocallyClosedCoefficientImmersion B X :=
    { hom := v
      immersion := inferInstance
      coefficient := Iso.refl _ }
  let cc : LocallyClosedCoefficientImmersion S B :=
    { hom := c
      immersion := inferInstance
      coefficient := ((proEtaleRingInverseImageComp c v).app X.ring).symm ≪≫ cf }
  refine ⟨⟨B, cc, vv, hc, hv, ?_, hco, hvc⟩⟩
  dsimp [LocallyClosedCoefficientImmersion.comp, vv, cc,
    proEtaleRingCompositeCoefficients]
  congr 1
  simp

/-- A chosen closed-then-open factorization of a coefficient immersion. -/
def extensionFactorization {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) : ExtensionFactorization a :=
  Classical.choice (factorization_nonempty a)

/-- An open coefficient immersion admits an exact left adjoint open extension with invertible
adjunction unit. -/
theorem open_extension_exists {S X : LocallyClosedCoefficients.{u}}
    (v : LocallyClosedCoefficientImmersion S X) (hv : IsOpenImmersion v.hom) :
    ∃ F : proEtaleRingModules S.scheme S.ring ⥤ proEtaleRingModules X.scheme X.ring,
      F.Additive ∧ PreservesFiniteLimits F ∧ PreservesFiniteColimits F ∧
        ∃ adj : F ⊣ v.pull, IsIso adj.unit := by
  let := hv
  let : IsNoetherian X.scheme := ⟨⟩
  let : NoetherianSpace S.scheme := v.hom.isOpenEmbedding.isInducing.noetherianSpace
  let Z : TopologicalSpace.Closeds X.scheme :=
    ⟨(Set.range v.hom)ᶜ, v.hom.isOpenEmbedding.isOpen_range.isClosed_compl⟩
  let I := IdealSheafData.vanishingIdeal Z
  have hZ : Set.range v.hom = (Set.range I.subschemeι)ᶜ := by
    rw [I.range_subschemeι, IdealSheafData.coe_support_vanishingIdeal]
    exact (compl_compl (Set.range v.hom)).symm
  let U : X.scheme.ProEt := ProEt.mk v.hom
  have : IsOpenImmersion U.hom := hv
  have : QuasiCompact U.hom := inferInstanceAs (QuasiCompact v.hom)
  obtain ⟨_, _, _, F, ha, hl, hc, adj, hu, _⟩ :=
    proEtaleIdentifiedOpenClosed I.subschemeι U hZ X.ring
      ((proEtaleSheafInverseImage I.subschemeι CommRingCat.{u + 1}).obj X.ring) S.ring
      (Iso.refl _) v.coefficient
  exact ⟨F, ha, hl, hc, adj, hu⟩

/-- The chosen open extension functor along an open coefficient immersion. -/
def modelOpenExtension {S X : LocallyClosedCoefficients.{u}}
    (v : LocallyClosedCoefficientImmersion S X) (hv : IsOpenImmersion v.hom) :=
  (open_extension_exists v hv).choose

/-- The adjunction between the chosen open extension and pullback. -/
def modelOpenAdjunction {S X : LocallyClosedCoefficients.{u}}
    (v : LocallyClosedCoefficientImmersion S X) (hv : IsOpenImmersion v.hom) :
    modelOpenExtension v hv ⊣ v.pull :=
  (open_extension_exists v hv).choose_spec.2.2.2.choose

instance modelOpenAdjunction_unit_isIso {S X : LocallyClosedCoefficients.{u}}
    (v : LocallyClosedCoefficientImmersion S X) (hv : IsOpenImmersion v.hom) :
    IsIso (modelOpenAdjunction v hv).unit :=
  (open_extension_exists v hv).choose_spec.2.2.2.choose_spec

private theorem closed_properties {S X : LocallyClosedCoefficients.{u}}
    (c : LocallyClosedCoefficientImmersion S X) (hc : IsClosedImmersion c.hom) :
    PreservesFiniteLimits c.push ∧ PreservesFiniteColimits c.push ∧
      IsIso (proEtaleRingModuleAdjunction c.hom X.ring S.ring c.coefficient).counit := by
  let := hc
  let : IsNoetherian X.scheme := ⟨⟩
  let W : X.scheme.Opens :=
    ⟨(Set.range c.hom)ᶜ, c.hom.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let : NoetherianSpace W.toScheme := W.ι.isOpenEmbedding.isInducing.noetherianSpace
  let U : X.scheme.ProEt := ProEt.mk W.ι
  have : IsOpenImmersion U.hom := inferInstanceAs (IsOpenImmersion W.ι)
  have : QuasiCompact U.hom := inferInstanceAs (QuasiCompact W.ι)
  obtain ⟨hl, he, hu, _⟩ := proEtaleIdentifiedOpenClosed c.hom U W.range_ι X.ring S.ring
    ((proEtaleSheafInverseImage W.ι CommRingCat.{u + 1}).obj X.ring)
    c.coefficient (Iso.refl _)
  exact ⟨hl, he, hu⟩

instance modelClosed_counit_isIso {S X : LocallyClosedCoefficients.{u}}
    (c : LocallyClosedCoefficientImmersion S X) [hc : IsClosedImmersion c.hom] :
    IsIso (proEtaleRingModuleAdjunction c.hom X.ring S.ring c.coefficient).counit :=
  (closed_properties c hc).2.2

/-- A presentation of the closed-then-open functor: a functor together with an equality to
the closed direct image followed by the open extension. -/
structure ModelPresentation {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) where
  functor : proEtaleRingModules S.scheme S.ring ⥤ proEtaleRingModules X.scheme X.ring
  agreement : functor = a.extensionFactorization.closed.push ⋙
    modelOpenExtension a.extensionFactorization.openMap a.extensionFactorization.isOpen

/-- The presentation has the explicitly constructed composite as a witness. -/
theorem modelPresentation_nonempty {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) : Nonempty (ModelPresentation a) :=
  ⟨⟨_, rfl⟩⟩

/-- Choose a presentation whose equality field determines its functor exactly. -/
@[irreducible] def modelPresentation {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) : ModelPresentation a :=
  Classical.choice (modelPresentation_nonempty a)

/-- The model locally closed extension: closed direct image followed by the constructed open
extension. -/
@[irreducible] def modelExtension {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) :
    proEtaleRingModules S.scheme S.ring ⥤ proEtaleRingModules X.scheme X.ring :=
  a.modelPresentation.functor

/-- The model extension equals the closed direct image followed by the open extension. -/
theorem modelExtension_eq {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) :
    a.modelExtension = a.extensionFactorization.closed.push ⋙
      modelOpenExtension a.extensionFactorization.openMap a.extensionFactorization.isOpen := by
  unfold modelExtension
  exact a.modelPresentation.agreement

/-- Restriction for the chosen model, using exactly the open inverse unit and closed counit. -/
@[irreducible] def modelRestriction {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) : a.modelExtension ⋙ a.pull ≅ 𝟭 _ := by
  rw [modelExtension_eq]
  let c := a.extensionFactorization.closed
  let v := a.extensionFactorization.openMap
  let O := modelOpenExtension v a.extensionFactorization.isOpen
  let rO : O ⋙ v.pull ≅ 𝟭 _ := (asIso (modelOpenAdjunction v _).unit).symm
  let rG : c.push ⋙ c.pull ≅ 𝟭 _ :=
    asIso (proEtaleRingModuleAdjunction c.hom _ _ c.coefficient).counit
  exact Functor.isoWhiskerLeft (c.push ⋙ O)
      (eqToIso (congrArg LocallyClosedCoefficientImmersion.pull
        a.extensionFactorization.composite.symm) ≪≫ v.pullComp c) ≪≫
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft c.push (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerLeft c.push (Functor.isoWhiskerRight rO _) ≪≫
          Functor.isoWhiskerLeft c.push (Functor.leftUnitor _) ≪≫ rG

end LocallyClosedCoefficientImmersion

end AlgebraicGeometry.Scheme
