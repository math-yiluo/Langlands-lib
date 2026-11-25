/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.SecondLocalizationMap
public import Mathlib.RingTheory.Localization.Basic
import WeilConjectures.Algebra.Homology.DerivedTensorFlatSecondLocalization
import WeilConjectures.Algebra.Homology.SecondLocalizationIsoAux
/-! # Invertibility of the second localization map
Source: Stacks Project, Tags 06Y6 and 0DJ8.
(blueprint: lem-pc-second-localization-iso). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
open scoped TensorProduct ChangeOfRings
attribute [local instance] Algebra.TensorProduct.rightAlgebra
namespace RingTensorCohomology

variable (R A B Bp D : Type u)
  [CommRing R] [CommRing A] [CommRing B] [CommRing Bp] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra B Bp] [Algebra R Bp]
  [tRB : IsScalarTower R B Bp]
  [Algebra (A ⊗[R] B) D] [Algebra (A ⊗[R] Bp) D]
  [Algebra A D] [Algebra B D] [Algebra Bp D]
  [tAD : IsScalarTower A (A ⊗[R] B) D]
  [tBD : IsScalarTower B (A ⊗[R] B) D]
  [tApD : IsScalarTower A (A ⊗[R] Bp) D]
  [tBpD : IsScalarTower Bp (A ⊗[R] Bp) D]
  [tBBpD : IsScalarTower B Bp D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]
  [HasDerivedCategory.{w} (ModuleCat.{u} Bp)]

include tRB tAD tBD tApD tBpD tBBpD in
/-- The characterized coefficient map becomes invertible after extension to D.
Source: Stacks Project, Tag 0DJ8 affine localization identity; Tag 06Y6.
(blueprint: lem-pc-second-localization-iso).

Proof: compute both universal derived functors on an R-K-flat resolution of Q.
Extension along the flat localization B to Bp is exact, so its homology is
extension of B-homology. The ordinary associator identifies the extended
resolution with extension from R to Bp. Its counit square identifies the derived
lift in secondLocalizationDerivedMap with this associator, by uniqueness of
left derived lifts. Thus the cohomology map is the standard flat base change
isomorphism after extension to Bp. Naturality with multiplication by A on Q and
the cohomologyIso_smul equations prove A-linearity; Bp-linearity is built in.
Tensor induction therefore gives linearity over A tensor_R Bp. Tensor
associativity extends this isomorphism to D and supplies the generator formula.
Every localization denominator is a unit in D. No flatness of D is required.
If T contains zero, Bp and D are zero and both extended modules are zero.
Identity localization gives the unique counit-compatible model transport. -/
theorem exists_secondLocalization_iso
    (T : Submonoid B) [IsLocalization T Bp] (hflat : (algebraMap B Bp).Flat) (i : ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel R A Bp Q D) :
    ∃ e : (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj (L.cohomology i) ≅
      (ModuleCat.extendScalars (algebraMap (A ⊗[R] Bp) D)).obj (K.cohomology i),
      IsSecondLocalizationMap R A B Bp D hflat Q L K i e.hom := by
  obtain ⟨f, hf⟩ := exists_secondLocalization_hom R A B Bp D T hflat i Q L K
  let : IsIso f := secondLocalization_hom_isIso R A B Bp D T hflat i Q L K f hf
  exact ⟨asIso f, hf⟩

end RingTensorCohomology
