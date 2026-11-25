/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # K-injective resolutions with independent site universes

Source: Stacks Project, Section 07A5 and Theorem 079P
(auxiliary; not a blueprint node).
The free lifted Yoneda sheaves are precisely the sheafifications of the localized
rank-one extension presheaves. Their use preserves the generator in the source statement.
-/

@[expose] public section

set_option autoImplicit false

universe c v r

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- Grothendieck abelianness, the specified free-sheaf generator, and functorial
K-injective resolutions with injective terms, without equating site universes.
Source: Stacks Project, Section 07A5 and Theorem 079P
(auxiliary; not a blueprint node).
Proof:
1. Form the free module on the lifted representable at each site object. Its
sections are finite linear combinations of arrows into that object, exactly the
extension-by-zero presheaf of the localized unit. Sheafification makes these a
separating family, by the free-Yoneda/sheafification adjunction. Their coproduct
is a separator. Kernels and filtered colimits are computed on underlying abelian
sheaves, where filtered colimits are exact. All index sets fit max c v r.
2. Apply the small-object construction of the source library to this Grothendieck
abelian category: factor each map M→0 functorially by the monomorphic
quasi-isomorphisms. The resulting target is K-injective, and its terms are
injective by the degreewise lifting criterion. The first factor supplies the
natural quasi-isomorphism; the construction is functorial on chain maps. -/
theorem grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r}) :
    IsGrothendieckAbelian.{max c v r}
      (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ∧
    IsSeparator (∐ fun U : C ↦
      (PresheafOfModules.sheafification.{max c v r} (𝟙 ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).obj)).obj
        ((PresheafOfModules.free ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).obj).obj
          (uliftYoneda.{max c v r}.obj U))) ∧
    ∃ (I : CochainComplex (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ ⥤
        CochainComplex (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
      (η : 𝟭 (CochainComplex (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ) ⟶ I),
      ∀ M : CochainComplex (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ,
        QuasiIso (η.app M) ∧ (I.obj M).IsKInjective ∧
          ∀ n : ℤ, Injective ((I.obj M).X n) := by
  classical
  let S := (sheafCompose J
    (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R
  let A := SheafOfModules.{max c v r} S
  have hsep : ObjectProperty.IsSeparating (.ofObj fun U : C ↦
      (PresheafOfModules.sheafification.{max c v r} (𝟙 S.obj)).obj
        ((PresheafOfModules.free S.obj).obj (uliftYoneda.{max c v r}.obj U))) := by
    let adj := (PresheafOfModules.freeAdjunction S.obj).comp
      (PresheafOfModules.sheafificationAdjunction.{max c v r} (𝟙 S.obj))
    intro M N f g h
    apply ((SheafOfModules.forget S ⋙ PresheafOfModules.restrictScalars (𝟙 S.obj)) ⋙
      PresheafOfModules.toPresheaf S.obj ⋙
        (Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget Ab)).map_injective
    apply hom_ext_uliftYoneda.{max c v r}
    intro U a
    apply (adj.homEquiv _ _).symm.injective
    simpa only [← Adjunction.homEquiv_naturality_right_symm] using
      h _ (ObjectProperty.ofObj_apply _ U) ((adj.homEquiv _ _).symm a)
  have hgen := hsep.isSeparator_coproduct
  have : HasFilteredColimitsOfSize.{max c v r, max c v r} A :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  have : AB5OfSize.{max c v r, max c v r} A :=
    ⟨fun K _ _ ↦ HasExactColimitsOfShape.domain_of_functor K (toSheaf.{max c v r} S)⟩
  have : HasSeparator A := ⟨_, hgen⟩
  have hGroth : IsGrothendieckAbelian.{max c v r} A := {}
  let _ := hGroth
  refine ⟨hGroth, hgen, CochainComplex.kInjectiveResolutionFunctor.{max c v r} A,
    CochainComplex.toKInjectiveResolution.{max c v r} A, ?_⟩
  intro M
  exact ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v r} A M).2,
    inferInstance, fun n ↦ inferInstance⟩

end SheafOfModules
