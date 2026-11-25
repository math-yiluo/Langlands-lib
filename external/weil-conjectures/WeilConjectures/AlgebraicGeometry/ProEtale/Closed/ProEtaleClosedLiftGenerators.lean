/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.WeaklyContractibleCohomology
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Free generators on affine closed-specialization neighbourhoods
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- The canonical augmentation `∐ A[U] ⟶ M`, indexed by all affine weakly contractible
pro-etale objects `U` whose points specialize into the closed fibre over `Z` together with
all morphisms `A[U] ⟶ M`. -/
noncomputable def closedLiftGeneratorAugmentation
    (A : Type u) [CommRing A] {X Z : Scheme.{u}} (z : Z ⟶ X)
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :
    Arrow (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) := by
  let F := ProEtale.freeSheaf (ULift.{u + 1, u} A) X
  let J := { t : Σ U : X.ProEt, F.obj U ⟶ M //
    IsAffine t.1.left ∧
      (∀ (P Q : Sheaf (ProEt.topology X) (Type (u + 1))) (φ : P ⟶ Q),
        Epi φ → Function.Surjective (φ.hom.app (op t.1))) ∧
      (∀ x : t.1.left, ∃ y : ↥(pullback t.1.hom z),
        Specializes x ((pullback.fst t.1.hom z) y)) }
  exact Arrow.mk (Sigma.desc (f := fun t : J ↦ F.obj t.val.1) (fun t ↦ t.val.2))

end AlgebraicGeometry.Scheme
