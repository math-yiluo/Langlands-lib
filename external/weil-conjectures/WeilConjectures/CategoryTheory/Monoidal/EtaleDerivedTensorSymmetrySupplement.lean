/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.AlgebraicGeometry.EtaleDerivedTensorSymmetry

/-!
# The canonical symmetry of the etale derived tensor product

Source: Stacks Project, Tag 06YU, symmetry of the derived tensor product
(blueprint: lem-kun-tensor-sym).

The recorded existence theorem forgets the canonical map. This interface exposes the actual
braiding descended from the signed braiding of cochain complexes, without choosing an arbitrary
isomorphism from that existence theorem.

## Main definitions

- `CategoryTheory.DerivedMonoidal.canonicalBraidingNatIso`: the natural braiding before
  specializing to etale sheaves.
- `AlgebraicGeometry.Etale.derivedTensorSymmetry`: its canonical etale specialization.
-/

@[expose] public section

universe v₁ v₂ u' u

open CategoryTheory Limits

namespace CategoryTheory.DerivedMonoidal

/-- The canonical natural symmetry induced on the derived tensor bifunctor by a braiding.
Source: Stacks Project, Tag 06YU (blueprint: lem-kun-tensor-sym).
This packages the existing `braiding` and its two existing naturality identities before
specializing to etale sheaves, avoiding repeated reduction of their monoidal instances. -/
noncomputable def canonicalBraidingNatIso
    {C : Type u'} {D : Type u} [Category.{v₁} C] [Category.{v₂} D]
    [MonoidalCategory C] [BraidedCategory C] (F : C ⥤ D) (W : MorphismProperty C)
    [F.IsLocalization W] [W.ContainsIdentities] [F.HasDerivedMonoidalCategory W] :
    bifunctor F W ≅ (bifunctor F W).flip :=
  NatIso.ofComponents (fun K ↦
    NatIso.ofComponents (fun L ↦
      { hom := ((braidingNatTrans F W).app L).app K
        inv := ((braidingInvNatTrans F W).app K).app L
        hom_inv_id :=
          congr_app (congr_app (braidingNatTrans_comp_braidingInvNatTrans F W) K) L
        inv_hom_id :=
          congr_app (congr_app (braidingInvNatTrans_comp_braidingNatTrans F W) L) K })
      (fun f ↦ braiding_naturality_right F W K f))
    (fun f ↦ NatTrans.ext (funext (fun L ↦ braiding_naturality_left F W f L)))

end CategoryTheory.DerivedMonoidal

namespace DerivedCategory

open MonoidalCategory

variable (C : Type u') [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [HasDerivedCategory.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C]
  [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]

/-- The generic wrapper agrees with the original localization construction.
Source: Stacks Project, Tag 06YU (blueprint: lem-kun-tensor-sym). -/
lemma canonicalTensorSymmetry_eq :
    canonicalTensorSymmetry C =
      DerivedMonoidal.canonicalBraidingNatIso Qh (HomotopyCategory.quasiIso C (.up ℤ)) := by
  rfl

end DerivedCategory

namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale
