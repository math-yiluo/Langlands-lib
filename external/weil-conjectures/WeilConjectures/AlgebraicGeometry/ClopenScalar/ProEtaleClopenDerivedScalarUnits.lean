/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClopenScalar.ProEtaleClopenDerivedScalarData

import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-! # Normalized clopen scalar comparison

Source: Stacks Project, Tags 06YY and 0D6D.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t u w
open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules SheafOfModules.SuccessiveDerivedQuotient
namespace AlgebraicGeometry.Scheme.ProEt.ClopenScalar
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] ClopenLocalization.modulesAbelian ClopenLocalization.hasDerived
attribute [-instance] AlgebraicGeometry.ProEtale.surjectiveTower_hasSheafify
  AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective

attribute [local irreducible] HasDerivedCategory.standard
open scoped ChangeOfRings

private def scalarRestrictionId {Z : Scheme.{t}}
    (R : Sheaf (topology Z) CommRingCat.{max u (t + 1)}) :
    restriction.{t + 1, t, max u (t + 1)} (𝟙 R) ≅ 𝟭 (Mods.{t, u} R) :=
  NatIso.ofComponents (fun M ↦ {
    hom := { val := {
      app := fun U ↦ ModuleCat.ofHom {
        toFun := fun x ↦ x
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
      naturality := by intros; ext; rfl } }
    inv := { val := {
      app := fun U ↦ ModuleCat.ofHom {
        toFun := fun x ↦ x
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
      naturality := by intros; ext; rfl } }
    hom_inv_id := by ext; rfl
    inv_hom_id := by ext; rfl
  }) (by intros; ext; rfl)

private def ordinaryUnit {Z : Scheme.{t}} {p : Presentations.{t, u} Z}
    (n : Normalization.{t + 1, t, max u (t + 1), max (u + 1) (t + 2)}
      (C := Z.ProEt) (J := topology Z) (hD := derived.{t, u} Z) @p)
    (R : Sheaf (topology Z) CommRingCat.{max u (t + 1)}) :
    ext (Z := Z) (p (𝟙 R)) ≅ 𝟭 (Mods.{t, u} R) :=
  ((n.ordinaryAdjunction (𝟙 R)).ofNatIsoRight (scalarRestrictionId R)).leftAdjointUniq
    Adjunction.id

private def identityHomotopyIso {Z : Scheme.{t}} {p : Presentations.{t, u} Z}
    (n : Normalization.{t + 1, t, max u (t + 1), max (u + 1) (t + 2)}
      (C := Z.ProEt) (J := topology Z) (hD := derived.{t, u} Z) @p)
    (R : Sheaf (topology Z) CommRingCat.{max u (t + 1)}) :
    (p (𝟙 R)).ordinary.mapHomotopyCategory (.up ℤ) ≅
      𝟭 (HomotopyCategory (Mods.{t, u} R) (.up ℤ)) :=
  NatIso.ofComponents (fun H ↦
    (HomotopyCategory.quotient _ _).mapIso
      ((NatIso.mapHomologicalComplex (ordinaryUnit n R) (.up ℤ) ≪≫
        Functor.mapHomologicalComplexIdIso (Mods.{t, u} R) (.up ℤ)).app H.as))
    (by
      rintro ⟨P⟩ ⟨Q⟩ ⟨f⟩
      simpa only [Iso.app_hom, Functor.map_comp, Functor.mapIso_hom, Functor.id_map,
        HomotopyCategory.quot_mk_eq_quotient_map, Functor.mapHomotopyCategory_map] using
        congrArg ((HomotopyCategory.quotient _ _).map)
          ((NatIso.mapHomologicalComplex (ordinaryUnit n R) (.up ℤ) ≪≫
            Functor.mapHomologicalComplexIdIso (Mods.{t, u} R) (.up ℤ)).hom.naturality f))

private def unitFactors {Z : Scheme.{t}} {p : Presentations.{t, u} Z}
    (n : Normalization.{t + 1, t, max u (t + 1), max (u + 1) (t + 2)}
      (C := Z.ProEt) (J := topology Z) (hD := derived.{t, u} Z) @p)
    (R : Sheaf (topology Z) CommRingCat.{max u (t + 1)}) :
    DerivedCategory.Qh ⋙ 𝟭 (DerivedCategory (Mods.{t, u} R)) ≅
      (p (𝟙 R)).ordinary.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
  DerivedCategory.Qh.rightUnitor ≪≫ DerivedCategory.Qh.leftUnitor.symm ≪≫
    (Functor.isoWhiskerRight (identityHomotopyIso n R) DerivedCategory.Qh).symm

private def derivedUnit {Z : Scheme.{t}} {p : Presentations.{t, u} Z}
    (n : Normalization.{t + 1, t, max u (t + 1), max (u + 1) (t + 2)}
      (C := Z.ProEt) (J := topology Z) (hD := derived.{t, u} Z) @p)
    (R : Sheaf (topology Z) CommRingCat.{max u (t + 1)}) :
    extD (Z := Z) (p (𝟙 R)) ≅ 𝟭 (DerivedCategory (Mods.{t, u} R)) := by
  let ε := unitFactors n R
  let := (p (𝟙 R)).universal
  let := Functor.isLeftDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso (Mods.{t, u} R) (.up ℤ))
    (𝟭 (DerivedCategory (Mods.{t, u} R))) ε
  exact Functor.leftDerivedUnique (𝟭 _) (p (𝟙 R)).derived
    (p (𝟙 R)).counit ε.hom (HomotopyCategory.quasiIso _ (.up ℤ))

end AlgebraicGeometry.Scheme.ProEt.ClopenScalar
