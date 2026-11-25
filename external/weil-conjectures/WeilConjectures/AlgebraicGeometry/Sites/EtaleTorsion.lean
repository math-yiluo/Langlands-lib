/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.Point.Torsion
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfSize
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Torsion étale sheaves are detected on geometric stalks

A sheaf of abelian groups on the small étale site of a scheme `X` is torsion
(`CategoryTheory.Sheaf.IsTorsion`: every section is locally torsion) if and only if its stalk
at every geometric point of `X` is a torsion group [Stacks 03SA]. This is the specialization
of `CategoryTheory.Sheaf.isTorsion_iff_isAddTorsion_sheafFiber` to the conservative family of
geometric points `X.algClosurePoint x`.

## Main results

- `AlgebraicGeometry.Scheme.isTorsion_iff_isAddTorsion_sheafFiber`: a sheaf of abelian groups
  on `X_ét` is torsion if and only if all its geometric stalks are torsion groups.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- A sheaf of abelian groups on the small étale site of `X` is torsion if and only if its
stalk at every geometric point of `X` is a torsion group. -/
@[stacks 03SA]
lemma isTorsion_iff_isAddTorsion_sheafFiber {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    F.IsTorsion ↔ ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
      IsAddTorsion (((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj F) := by
  refine ⟨fun hF Ω _ _ s ↦ ?_, fun h ↦ ?_⟩
  · have := ((pointSmallEtale s).ulift.{u + 1}).isAddTorsion_sheafFiber hF
    exact IsAddTorsion.of_surjective
      (f := ((((pointSmallEtale s).uliftSheafFiberIso AddCommGrpCat.{u + 1}).app F).hom).hom)
      (ConcreteCategory.bijective_of_isIso _).2 this
  · refine Sheaf.IsTorsion.of_isAddTorsion_sheafFiber
      (isConservativeFamilyOfPoints_ulift_pointSmallEtale X) ?_
    rintro ⟨-, ⟨x⟩⟩
    exact IsAddTorsion.of_surjective
      (f := ((((pointSmallEtale (X.algClosurePoint x)).uliftSheafFiberIso
        AddCommGrpCat.{u + 1}).app F).inv).hom)
      (ConcreteCategory.bijective_of_isIso _).2 (h _ _)

end AlgebraicGeometry.Scheme
