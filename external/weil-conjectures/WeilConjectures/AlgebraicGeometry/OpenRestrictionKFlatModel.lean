/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.KFlat
import WeilConjectures.Algebra.Homology.KFlatPullback
import WeilConjectures.AlgebraicGeometry.TensorPullback

/-! # K-flat models under open restriction

Source: Stacks Project, Tag 08DX, proof of (1).
(blueprint: lem-pc-open-restriction-kflat-model).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- The recorded sheaf tensor, used for total complexes. Source: Stacks, Tag 06Y7
(blueprint: lem-pc-open-restriction-kflat-model). -/
noncomputable local instance openRestrictionKFlatModelTensor (X : Scheme.{u}) :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.sheaf

/-- Open restriction preserves K-flatness for the canonical over-site restriction.
Source: Stacks Project, Tag 06YC, specialized to the open inclusion; Tag 08DX(1).
Proof: K-flatness is detected on stalks (Tag 06YB). For a point x of U, the
stalk ring and stalk module of the restricted sheaf identify with the corresponding
stalks at the image of x in X. The cofinal neighborhoods contained in U induce these
identifications; they are natural in module maps, so they also identify differentials
of the stalk complexes. Transport tensor products and acyclicity through the stalk-ring
isomorphism. K-flatness of P supplies the stalkwise K-flatness on X, hence that of its
restriction on U. Apply the stalk criterion on U to conclude. No condition on the
terms or boundedness is used. For the empty open the stalk condition is vacuous.
(blueprint: lem-pc-open-restriction-kflat-model). -/
theorem openRestriction_isKFlat (X : Scheme.{u}) (U : X.Opens)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlatTensor (R := X.sheaf) P) :
    let R :=
    SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv U)
    CochainComplex.IsKFlatTensor (R := U.toScheme.sheaf)
      ((R.mapHomologicalComplex (.up ℤ)).obj P) := by
  classical
  -- Tensor pullback and restriction are left adjoints to the same pushforward.
  let T := Scheme.Modules.tensorPullback U.ι
  have : T.IsLeftAdjoint := ⟨_, Scheme.Modules.nonempty_tensorPullbackAdjunction U.ι⟩
  have : T.Additive := CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _
    (by rw [CategoryTheory.rightExactFunctor_iff]; infer_instance)
  let e : T ≅ Scheme.Modules.restrictFunctor U.ι :=
    (Scheme.Modules.nonempty_tensorPullbackAdjunction U.ι).some.leftAdjointUniq
      (Scheme.Modules.restrictAdjunction U.ι)
  let R := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
    Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)
  let c : T ≅ R := e ≪≫ (Scheme.Modules.overFunctorEquiv U).symm
  have : R.Additive := Functor.additive_of_iso c
  -- The explicit pullback complex has exactly the termwise tensor-pullback formula.
  have hT : CochainComplex.IsKFlatTensor (R := U.toScheme.sheaf)
      ((T.mapHomologicalComplex (.up ℤ)).obj P) := by
    have h := CochainComplex.isKFlat_pullback U.ι.base U.toScheme.sheaf X.sheaf
      ⟨U.ι.c⟩ P hP
    convert h using 1
    rfl
  change CochainComplex.IsKFlatTensor (R := U.toScheme.sheaf)
    ((R.mapHomologicalComplex (.up ℤ)).obj P)
  let := SheafOfModules.monoidalCategory U.toScheme.sheaf
  -- Total tensor with any fixed acyclic complex preserves this chain isomorphism.
  intro F hF i
  exact (hT F hF i).of_iso
    (((curriedTensor _).map₂CochainComplex.obj F).mapIso
      ((NatIso.mapHomologicalComplex c (.up ℤ)).app P))

end AlgebraicGeometry
