/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KInjectiveMayerVietorisData
import WeilConjectures.AlgebraicGeometry.OpenModuleImageAmalgamation
import WeilConjectures.AlgebraicGeometry.OpenModuleImageSeparated

/-! # Gluing the concrete open restriction/direct-image units

Source: Stacks Project, Cohomology, Tag 08BV, kernel of the displayed sequence.
(blueprint: lem-pc-open-module-image-gluing).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

set_option autoImplicit false

namespace AlgebraicGeometry

/-- The restriction units for a two-open cover form a pullback, for every module sheaf.
Source: Stacks Project, Cohomology, Tag 08BV (lemma-exact-sequence-j-star),
and the sheaf gluing argument of Tag 01EB (lemma-mayer-vietoris).
(blueprint: lem-pc-open-module-image-gluing).

Proof: Evaluate the underlying presheaves of abelian groups at any test open T.
Transport the restriction/direct-image objects along overFunctorEquiv to the
ordinary restriction functors. Their sections identify with M(T ∩ U), M(T ∩ V),
and M(T ∩ U ∩ V); the transported units are restrictions from M(T).
The composition comparison for nested opens, followed by the counit, identifies
both right-hand arrows with restriction to T ∩ U ∩ V. In this calculation the
inverse comparison restricts twice, the counit cancels the repeated restriction,
and the forward comparison identifies the resulting restriction to the smaller open.
Since U and V cover X, T ∩ U and T ∩ V cover T. The sheaf axiom gives a unique
section of M(T) for any pair agreeing on the intersection. This is the pullback
universal property on sections. Uniqueness makes these amalgamations commute
with further restriction in T, so it is a pullback of presheaves. The fully
faithful inclusion of module sheaves into module presheaves reflects limits.
Limits of module presheaves are computed sectionwise; forgetting the module
structure preserves and reflects these limits. Thus the underlying abelian
presheaf pullback gives the module-sheaf pullback.
No injectivity or cochain complex is needed. The empty test open, empty scheme,
empty covering member, and repeated covering members obey the same sheaf axiom.
-/
theorem schemeOpenModuleImage_isPullback
    (X : Scheme.{u}) (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
    IsPullback ((schemeOpenModuleAdjunction X U).unit.app M)
      ((schemeOpenModuleAdjunction X V).unit.app M)
      ((schemeOpenModuleImageRestriction X (homOfLE (inf_le_left : U ⊓ V ≤ U))).app M)
      ((schemeOpenModuleImageRestriction X (homOfLE (inf_le_right : U ⊓ V ≤ V))).app M) := by
  have comm :
      (schemeOpenModuleAdjunction X U).unit.app M ≫
          (schemeOpenModuleImageRestriction X
            (homOfLE (inf_le_left : U ⊓ V ≤ U))).app M =
        (schemeOpenModuleAdjunction X V).unit.app M ≫
          (schemeOpenModuleImageRestriction X
            (homOfLE (inf_le_right : U ⊓ V ≤ V))).app M := by
    rw [schemeOpenModuleImage_unit_restriction X
      (homOfLE (inf_le_left : U ⊓ V ≤ U)) M]
    rw [schemeOpenModuleImage_unit_restriction X
      (homOfLE (inf_le_right : U ⊓ V ≤ V)) M]
  refine IsPullback.of_isLimit' ⟨comm⟩ ?_
  let lift : ∀ s : PullbackCone
      ((schemeOpenModuleImageRestriction X
        (homOfLE (inf_le_left : U ⊓ V ≤ U))).app M)
      ((schemeOpenModuleImageRestriction X
        (homOfLE (inf_le_right : U ⊓ V ≤ V))).app M),
      s.pt ⟶ M := fun s ↦
    (schemeOpenModuleImage_pullback_exists X U V hcover M s.fst s.snd
      s.condition).choose
  apply PullbackCone.IsLimit.mk comm lift
  · intro s
    exact (schemeOpenModuleImage_pullback_exists X U V hcover M s.fst s.snd
      s.condition).choose_spec.1
  · intro s
    exact (schemeOpenModuleImage_pullback_exists X U V hcover M s.fst s.snd
      s.condition).choose_spec.2
  · intro s m hm₁ hm₂
    apply schemeOpenModuleImage_pullback_unique X U V hcover M
      (hm₁.trans ((schemeOpenModuleImage_pullback_exists X U V hcover M s.fst s.snd
        s.condition).choose_spec.1).symm)
      (hm₂.trans ((schemeOpenModuleImage_pullback_exists X U V hcover M s.fst s.snd
        s.condition).choose_spec.2).symm)

end AlgebraicGeometry
