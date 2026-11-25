/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction

/-! # Restriction comparison for tensor pullback on an open cover

Source: Stacks Project, Sheaves of Modules, Tags 0095 and 0096.
(blueprint: def-pc-open-cover-tensor-pullback-comparison).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- Restricting then pulling back agrees with pulling back then restricting.
The comparison is constructed from ordinary pullback composition and the unique
comparison between the tensor and ordinary left adjoints to pushforward.
Source: Stacks Project, Tags 0095 and 0096.
(blueprint: def-pc-open-cover-tensor-pullback-comparison). -/
noncomputable def openCoverTensorPullbackComparison
    {X Y : Scheme.{u}} (p : Y ⟶ X) (U : X.OpenCover.{u}) (a : U.I₀) :
    pullback (U.f a) ⋙ pullback (U.pullbackHom p a) ≅
      tensorPullback p ⋙ pullback ((U.pullback₁ p).f a) :=
  pullbackComp (U.pullbackHom p a) (U.f a) ≪≫
    pullbackCongr (U.pullbackHom_map p a) ≪≫
    (pullbackComp ((U.pullback₁ p).f a) p).symm ≪≫
    Functor.isoWhiskerRight
      (Adjunction.leftAdjointUniq
        (Classical.choose (exists_tensorPullbackAdjunction p))
        (pullbackPushforwardAdjunction p)).symm
      (pullback ((U.pullback₁ p).f a))

end AlgebraicGeometry.Scheme.Modules
