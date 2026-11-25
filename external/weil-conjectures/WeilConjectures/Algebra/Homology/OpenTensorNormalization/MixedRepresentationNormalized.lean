/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.MixedRepForward.MixedRepresentationGeneral

/-! Mixed localization representative normalization, for an arbitrary coefficient category. -/

@[expose] public section
set_option autoImplicit false
universe u' u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped AlgebraicGeometry.ProEtale CategoryTheory.Functor
namespace SheafOfModules.OpenTensorNormalization

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [ProEtale.UpperStarPreservesFlat A]

/-- Normalizes the published mixed tensor representative equation to the model aliases used
by the restriction square. Source: Stacks Tag 07A4, clause (3) of
`finiteOpenMixedTensorRepresentative`. The proof expands the canonical map-derived tensor
comparison, transports the inverse of the oplax map by `Functor.map_inv`, and identifies the
derived tensor map with tensoring by the identity; see `mixed_representation_general`.
(blueprint: lem-sf-mixed-representation-normalized) -/
theorem mixed_representation_normalized
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (P Q : CochainComplex (Sheaf (Scheme.ProEt.topology X) A) ℤ) :
    let F := (j)^*[A]
    let a := F.mapDerivedCategoryFactors.hom
    let muX := Functor.LaxMonoidal.μ
      (DerivedCategory.Q (C := Sheaf (Scheme.ProEt.topology X) A)) P Q
    let fc := F.mapHomologicalComplex (.up ℤ)
    let muU := Functor.LaxMonoidal.μ (DerivedCategory.Q (C := Sheaf (Scheme.ProEt.topology U) A))
      (fc.obj P) (fc.obj Q)
    let c := ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app P).app Q
    let delta := ((ProEtale.mapDerivedCategoryUpperStarDerivedTensorIso A j).hom.app
      (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj Q)
    let n := a.app P ⊗ₘ (F.leftDerivedFunctorIsoMapDerivedCategory.hom.app
      (DerivedCategory.Q.obj Q) ≫ a.app Q)
    delta ≫ F.mapDerivedCategory.map muX ≫ a.app (HomologicalComplex.mapBifunctor P Q
      (curriedTensor (Sheaf (Scheme.ProEt.topology X) A)) (.up ℤ)) =
      n ≫ muU ≫ DerivedCategory.Q.map (inv c) :=
  AlgebraicGeometry.ProEtale.MixedRepForward.mixed_representation_general A j P Q

end SheafOfModules.OpenTensorNormalization
