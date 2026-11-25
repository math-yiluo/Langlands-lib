/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits

/-! # Comparison before evaluation at a base test object

Source: Stacks Project, Sites Tags 03CB and 03CC, and Étale Cohomology Tag 09YQ.
(blueprint: def-weil-pbc-sets-sheaf-comparison).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- The unit followed by the unit-compatible composition isomorphism, as a morphism
of sheaves on the intermediate scheme. Unlike the section comparison, its evaluation
has not yet been transported along the iterated-base-change isomorphism.

Source: Stacks Project, Sites Tags 03CB and 03CC; Étale Cohomology Tag 09YQ.
(blueprint: def-weil-pbc-sets-sheaf-comparison). -/
noncomputable def etaleSetSheafComparison
    {R S T : Scheme.{u}} (h : T ⟶ S) (f : S ⟶ R) (k : T ⟶ R) (hk : h ≫ f = k)
    (G : Sheaf R.smallEtaleTopology (Type (u + 1))) :
    (Scheme.etaleSetPullback f).obj G ⟶
      ((MorphismProperty.Over.pullback @Etale ⊤ h).sheafPushforwardContinuous
        (Type (u + 1)) (S.smallGrothendieckTopology @Etale)
        (T.smallGrothendieckTopology @Etale)).obj
          ((Scheme.etaleSetPullback k).obj G) :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ h) (Type (u + 1))
      (S.smallGrothendieckTopology @Etale) (T.smallGrothendieckTopology @Etale)).unit.app
        ((Scheme.etaleSetPullback f).obj G) ≫
    ((MorphismProperty.Over.pullback @Etale ⊤ h).sheafPushforwardContinuous
      (Type (u + 1)) (S.smallGrothendieckTopology @Etale) (T.smallGrothendieckTopology @Etale)).map
        (((Classical.choose etaleSetInverseImageCompositionUnits.2.2 R S T f h).hom.app G) ≫
          eqToHom (congrArg (fun a : T ⟶ R ↦ (Scheme.etaleSetPullback a).obj G) hk))

end AlgebraicGeometry
