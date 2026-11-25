/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetTerminalTransport
public import WeilConjectures.AlgebraicGeometry.EtaleSetTerminalRestriction
public import WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparison
import WeilConjectures.AlgebraicGeometry.EtaleSetTerminalCone

/-! # Compatibility of terminal section identifications

Source: Stacks Project, Tags 03S2, 03CB and 03CC.
(blueprint: lem-weil-pbc-sets-terminal-transition).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false in
private lemma terminalRestriction_unit
    {R : Scheme.{u}} (H : Sheaf R.smallEtaleTopology (Type (u + 1)))
    (U V : R.Etale) (f : V ⟶ U) :
    let : (MorphismProperty.Over.pullback @Etale ⊤ V.hom).IsContinuous
      (R.smallGrothendieckTopology @Etale) (V.left.smallGrothendieckTopology @Etale) :=
      Etale.isContinuous_overPullback V.hom
    (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ V.hom) (Type (u + 1))
      (R.smallGrothendieckTopology @Etale)
      (V.left.smallGrothendieckTopology @Etale)).unit.app H).hom.app (op U)) ≫
        ((Scheme.etaleSetPullback V.hom).obj H).obj.map
          (MorphismProperty.Over.homMk
            (B := (MorphismProperty.Over.pullback @Etale ⊤ V.hom).obj U)
            (pullback.lift f.left (𝟙 _) (by simp))
            (pullback.lift_snd _ _ _)).op =
      H.obj.map f.op ≫ (etaleSetTerminalRestriction H V).hom := by
  let : (MorphismProperty.Over.pullback @Etale ⊤ V.hom).IsContinuous
      (R.smallGrothendieckTopology @Etale) (V.left.smallGrothendieckTopology @Etale) :=
      Etale.isContinuous_overPullback V.hom
  let ρ := Classical.choose (etaleSetInverseImageRestriction V.hom)
  let d : Scheme.Etale.mk (𝟙 V.left) ⟶
      (MorphismProperty.Over.pullback @Etale ⊤ V.hom).obj U :=
    MorphismProperty.Over.homMk
      (pullback.lift f.left (𝟙 _) (by simp))
      (pullback.lift_snd _ _ _)
  let F := (Scheme.etaleSetPullback V.hom).obj H
  let K := (Etale.localizationRestriction (Type (u + 1)) V.hom inferInstance).obj H
  let η := ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ V.hom) (Type (u + 1))
    (R.smallGrothendieckTopology @Etale)
    (V.left.smallGrothendieckTopology @Etale)).unit.app H).hom.app (op U)
  let e : (MorphismProperty.Over.map (P := @Etale) ⊤ V.prop).obj
      (Scheme.Etale.mk (𝟙 V.left)) ≅ V :=
    MorphismProperty.Over.isoMk (Iso.refl V.left) (by simp)
  change η ≫ F.obj.map d.op = H.obj.map f.op ≫
    H.obj.map e.hom.op ≫ inv ((ρ.hom.app H).hom.app (op (Scheme.Etale.mk (𝟙 V.left))))
  apply (cancel_mono ((ρ.hom.app H).hom.app (op (Scheme.Etale.mk (𝟙 V.left))))).1
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  calc
    η ≫ F.obj.map d.op ≫ (ρ.hom.app H).hom.app (op (Scheme.Etale.mk (𝟙 V.left))) =
        η ≫ (ρ.hom.app H).hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤ V.hom).obj U)) ≫
          K.obj.map d.op := by rw [(ρ.hom.app H).hom.naturality d.op]
    _ = H.obj.map ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ V.hom
          inferInstance trivial).counit.app U).op ≫ K.obj.map d.op := by
        rw [← Category.assoc]
        congr 1
        ext s
        exact Classical.choose_spec (etaleSetInverseImageRestriction V.hom) H U s
    _ = H.obj.map f.op ≫ H.obj.map e.hom.op := by
        change H.obj.map _ ≫ H.obj.map _ = _
        rw [← H.obj.map_comp, ← H.obj.map_comp]
        congr 1
        apply Quiver.Hom.unop_inj
        simp only [unop_comp, Quiver.Hom.unop_op, Functor.op_map]
        apply MorphismProperty.Over.Hom.ext
        simp [d, e, MorphismProperty.Over.mapPullbackAdj]
        rfl

/-- Source: Stacks Project, Tag 03S2 and Sites Tags 03CB and 03CC.
(blueprint: lem-weil-pbc-sets-terminal-transition).

Proof: First prove the restriction-unit equation for an arbitrary site morphism
`f : V ⟶ U`. Postcompose with the restriction isomorphism at the terminal object
of `V`. Its naturality at the diagonal lift moves it past diagonal restriction.
The restriction-unit equation then replaces the unit with restriction along the
first pullback projection. This projection composed with the diagonal lift is
`f.left`, by `pullback.lift_fst`. The terminal-object identification has identity
underlying map, so functoriality of `H` gives `H.obj.map f.op`. Cancel the terminal
restriction isomorphism. Finally apply `etaleSetTerminalCone` with `T = V.left`,
`p = V.hom`, `t = f.left`, `t₀ = r.left`, using the over-morphism equations for
both structure maps. Substitute the proved restriction-unit equation and
reassociate. This gives the displayed equation, including identities and empty
schemes. -/
theorem etaleSetTerminalTransition
    {R : Scheme.{u}} (H : Sheaf R.smallEtaleTopology (Type (u + 1)))
    (U V W : R.Etale) (f : V ⟶ U) (q : U ⟶ W) (r : V ⟶ W)
    (hr : f.left ≫ q.left = r.left) :
    H.obj.map f.op ≫
        (etaleSetTerminalRestriction H V ≪≫
          etaleSetTerminalTransport W.hom r.left V.hom (MorphismProperty.Over.w r) H).hom =
      (etaleSetTerminalRestriction H U ≪≫
          etaleSetTerminalTransport W.hom q.left U.hom (MorphismProperty.Over.w q) H).hom ≫
        etaleSetSectionComparison f.left q.left r.left hr
          ((Scheme.etaleSetPullback W.hom).obj H) (Scheme.Etale.mk (𝟙 W.left)) := by
  have hc := etaleSetTerminalCone H U W q V.hom f.left r.left hr
    (MorphismProperty.Over.w f) (MorphismProperty.Over.w r)
  erw [← Category.assoc, terminalRestriction_unit H U V f] at hc
  simpa only [Iso.trans_hom, Category.assoc] using hc

end AlgebraicGeometry
