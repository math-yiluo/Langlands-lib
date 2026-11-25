/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian

/-!
# Functorial K-injective resolutions on small ringed sites

Source: Stacks Project, Cohomology on Sites, Section 07A5, first paragraph,
and Injectives, Theorem 079P (blueprint: prop-pur-kinjective-resolutions-exist).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

local instance {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (O : Sheaf J CommRingCat.{u}) : HasColimitsOfShape (Discrete C)
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
  inferInstance

/-- The module category on a small commutative ringed site is Grothendieck abelian,
with the coproduct of the localized rank-one extensions as a generator. Every
integer-indexed cochain complex has a functorial K-injective resolution whose
terms are injective.

Source: Stacks Project, Section 07A5 and Theorem 079P
(blueprint: prop-pur-kinjective-resolutions-exist).

Proof:
1. Apply `lem-pur-ringed-site-grothendieck-abelian` to obtain the Grothendieck
   property and the stated generator: sheafify the extension-by-zero presheaf
   of the unit module on each localized site and take their coproduct.
2. Use the source-library `kInjectiveResolutionFunctor` and `toKInjectiveResolution`
   on this Grothendieck abelian category. `monoQuasiIso_toKInjectiveResolution_app`
   supplies the quasi-isomorphisms, and the source instances give K-injectivity
   and injective terms. These realize `lem-pur-kinjective-degreewise-existence`
   without its separate statement module. Naturality of the transformation and
   the functor's action on chain maps give precisely the asserted functoriality. -/
theorem grothendieckAbelian_and_functorial_kInjective_resolutions
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (O : Sheaf J CommRingCat.{u}) :
    IsGrothendieckAbelian.{u}
        (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) ∧
      IsSeparator (∐ fun U : C ↦
        (PresheafOfModules.sheafification.{u}
          (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj)).obj
          ((extensionByZeroPresheaf.{u}
            ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) U).obj
            (unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).over U)))) ∧
      ∃ (I : CochainComplex
          (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) ℤ ⥤
          CochainComplex
          (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) ℤ)
        (η : 𝟭 (CochainComplex
          (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) ℤ) ⟶ I),
        ∀ (M : CochainComplex
          (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) ℤ),
          QuasiIso (η.app M) ∧ (I.obj M).IsKInjective ∧
            ∀ n : ℤ, Injective ((I.obj M).X n) := by
  obtain ⟨hGrothendieck, hGenerator⟩ :=
    grothendieckAbelian_with_localized_generator J O
  let _ := hGrothendieck
  let A := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  refine ⟨hGrothendieck, hGenerator, CochainComplex.kInjectiveResolutionFunctor.{u} A,
    CochainComplex.toKInjectiveResolution.{u} A, ?_⟩
  intro M
  exact ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A M).2,
    inferInstance, fun n ↦ inferInstance⟩

end SheafOfModules
