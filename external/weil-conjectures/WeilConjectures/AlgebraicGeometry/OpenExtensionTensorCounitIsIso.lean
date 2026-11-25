/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import WeilConjectures.AlgebraicGeometry.OpenExtensionDerivedUnitIsIso
import all WeilConjectures.AlgebraicGeometry.DerivedOpenTensorHomBijective

/-! # Open extension counit on a derived tensor
Source: Stacks Project, Tags 00A7, 08BS and 06YB.
(blueprint: lem-pc-open-extension-tensor-counit-isiso). -/

@[expose] public section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
  TopologicalSpace
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

noncomputable section
universe u w

local instance standardDerivedOpenExtensionTensorCounitIsIso (X : Scheme.{u}) (U : X.Opens) :
    HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) :=
  HasDerivedCategory.standard _

/-- The counit of open extension is invertible on a tensor with an extended object.
Source: Stacks Project, Cohomology Tags 08BS, 06YB and 06YH; Modules Tag 01AK.
Proof: use the proved support lemmas in DerivedOpenTensorHomBijective (imported
with `all` because they are private). Construct the exact canonical extension-by-zero
left adjoint to restriction and derive it. At a point outside U its value has acyclic
stalk; on U restriction
of extension is the identity. By uniqueness of left adjoints the same stalk
properties hold for any J ⊣ R. Compute the derived tensor with K-flat
representatives. Stalks commute with total tensor, and K-flatness is stalkwise.
Outside U an acyclic stalk of J(A) tensored with the K-flat stalk of K is acyclic;
thus J(A) tensor K has zero cohomology stalks outside U. The counit on any such
supported object is invertible: inside U its restriction is the inverse of the
unit, by the triangle identity and invertibility of the unit; outside U its source
and target have zero cohomology stalks. The cone therefore has acyclic stalks at
all points, so is zero in the derived category. This proves the actual counit
component invertible. The empty open makes both objects zero; for the total open
the adjunction is an equivalence. No monoidal structure on R is used.
(blueprint: lem-pc-open-extension-tensor-counit-isiso). -/
theorem openExtension_tensor_counit_isIso (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    let E := (Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)).mapDerivedCategory
    let R := (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory ⋙ E
    ∀ (J : schemeDerivedCategory U.toScheme ⥤ schemeDerivedCategory X)
      (adj : J ⊣ R) (A : schemeDerivedCategory U.toScheme)
      (K : schemeDerivedCategory X), IsIso (adj.counit.app (J.obj A ⊗ K)) := by
  dsimp
  intro J adj A K
  let F := (SheafOfModules.overFunctor.{u}
    (moduleRings X.toRingedSpace) U).mapDerivedCategory
  let eU : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U) ≌
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) := Scheme.Modules.overEquiv U
  let E := eU.mapDerivedCategory
  have he (B L : schemeDerivedCategory X) :
      Function.Bijective (fun f : B ⟶ L ↦ (F ⋙ E.functor).map f) ↔
        Function.Bijective (fun f : B ⟶ L ↦ F.map f) :=
    (Functor.FullyFaithful.ofFullyFaithful E.functor).homEquiv.bijective
      |>.of_comp_iff' (fun f : B ⟶ L ↦ F.map f)
  have (B : schemeDerivedCategory U.toScheme) : IsIso (adj.unit.app B) :=
    openExtension_derived_unit_isIso X U J adj B
  have : IsIso adj.unit := NatIso.isIso_of_isIso_app adj.unit
  have hJ := adj.fullyFaithfulLOfIsIsoUnit
  have := hJ.full
  have := hJ.faithful
  have hB : ∀ L : schemeDerivedCategory X,
      Function.Bijective (fun f : J.obj A ⟶ L ↦ F.map f) := by
    intro L
    exact (he (J.obj A) L).mp
      ((Scheme.hom_bijective_iff_counit adj (J.obj A)).mpr inferInstance L)
  have hs := (Scheme.raw_derived_hom_support X U (J.obj A)).mp hB
  have ht := (Scheme.raw_derived_hom_support X U (J.obj A ⊗ K)).mpr
    (fun x hx ↦ Scheme.tensor_stalk_vanishing X (J.obj A) K x (hs x hx))
  exact (Scheme.hom_bijective_iff_counit adj (J.obj A ⊗ K)).mp
    (fun L ↦ (he (J.obj A ⊗ K) L).mpr (ht L))

end
end AlgebraicGeometry
