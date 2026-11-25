/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OpenCoverTensorPullbackComparison

/-! # The explicit pulled-back local map family

Source: Stacks Project, Tag 01ZR, first proof, Zariski gluing.
(blueprint: def-pc-local-map-pullback-family). -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Pull back a local family and compose it with two prescribed global maps.
The definition is the composite of restriction of κ, the inverse tensor restriction
comparison, the ordinary pullback of r₀, the forward comparison, and restriction of ρ.
It chooses no object or map and uses no existence statement.
Source: Stacks Project, Tag 01ZR, first proof, Zariski gluing.
(blueprint: def-pc-local-map-pullback-family). -/
noncomputable def localMapPullbackFamily
    {X Y : Scheme.{u}} (q : Y ⟶ X) (U₀ : X.OpenCover.{u})
    (F G : X.Modules) (F' G' : Y.Modules)
    (κ : F' ⟶ (Scheme.Modules.tensorPullback q).obj F)
    (ρ : (Scheme.Modules.tensorPullback q).obj G ⟶ G')
    (r₀ : ∀ α, (Scheme.Modules.pullback (U₀.f α)).obj F ⟶
      (Scheme.Modules.pullback (U₀.f α)).obj G) :
    ∀ α, (Scheme.Modules.pullback ((U₀.pullback₁ q).f α)).obj F' ⟶
      (Scheme.Modules.pullback ((U₀.pullback₁ q).f α)).obj G' := fun α ↦
  let U := U₀.pullback₁ q
  let t := Scheme.Modules.openCoverTensorPullbackComparison q U₀ α
  (Scheme.Modules.pullback (U.f α)).map κ ≫ t.inv.app F ≫
    (Scheme.Modules.pullback (U₀.pullbackHom q α)).map (r₀ α) ≫
    t.hom.app G ≫ (Scheme.Modules.pullback (U.f α)).map ρ

end AlgebraicGeometry

attribute [irreducible] AlgebraicGeometry.localMapPullbackFamily
