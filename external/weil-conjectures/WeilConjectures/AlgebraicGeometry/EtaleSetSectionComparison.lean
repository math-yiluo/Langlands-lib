/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits

/-! # Canonical comparison maps on sections of étale inverse images
Source: Stacks Project, Tag 09YQ and Sites Tags 03CB and 03CC. -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- The section comparison for a commuting triangle `T ⟶ S ⟶ R`: first use the
inverse-image unit, then the composition isomorphism from
`etaleSetInverseImageCompositionUnits`, and finally restrict along the canonical
iterated-fibre-product isomorphism. This defines the transition maps and limit legs
in the continuity statement.

Source: Stacks Project, Étale Cohomology, Tag 09YQ, degree-zero section comparison;
Sites, Tags 03CB and 03CC
(blueprint: def-weil-pbc-sets-section-comparison). -/
noncomputable def etaleSetSectionComparison
    {R S T : Scheme.{u}} (h : T ⟶ S) (f : S ⟶ R) (k : T ⟶ R) (hk : h ≫ f = k)
    (G : Sheaf R.smallEtaleTopology (Type (u + 1))) (U : R.Etale) :
    ((Scheme.etaleSetPullback f).obj G).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U)) ⟶
      ((Scheme.etaleSetPullback k).obj G).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ k).obj U)) :=
  ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ h) (Type (u + 1))
      (S.smallGrothendieckTopology @Etale) (T.smallGrothendieckTopology @Etale)).unit.app
        ((Scheme.etaleSetPullback f).obj G)).hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U)) ≫
    ((Classical.choose etaleSetInverseImageCompositionUnits.2.2 R S T f h).hom.app G).hom.app
      (op ((MorphismProperty.Over.pullback @Etale ⊤ h).obj
        ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U))) ≫
    (eqToHom (congrArg (fun a : T ⟶ R ↦ (Scheme.etaleSetPullback a).obj G) hk)).hom.app
      (op ((MorphismProperty.Over.pullback @Etale ⊤ h).obj
        ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U))) ≫
    ((Scheme.etaleSetPullback k).obj G).obj.map
      ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) h f k hk.symm).hom.app U).op

end AlgebraicGeometry
