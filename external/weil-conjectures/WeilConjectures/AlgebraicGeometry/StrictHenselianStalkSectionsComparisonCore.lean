/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.AlgebraicGeometry.Sites.AffineEtale

/-! # Same-universe inverse image of abelian etale sheaves -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

/-- Direct image on abelian etale sheaves admits an inverse-image left adjoint,
without increasing the universe of the coefficient groups.
Source: Stacks Project, Sites and Sheaves, Proposition 7.44.3, and Modules on Sites,
Tag 03D3, the abelian-sheaf adjunction in its proof.
(blueprint: new-strict-henselian-stalk-sections-comparison-functor)

Proof: For each scheme choose the site of affine etale schemes of finite presentation,
encoded by finite presentations over the coordinate rings of an affine open cover.
The presentations and their morphisms form sets in the scheme universe. These affine
objects form a dense subsite: affine opens cover each etale object, and an affine object
has a finite affine refinement of each covering. The comparison lemma identifies sheaves
on the full etale site with sheaves on this small site, with the same coefficient groups.
Base change along g is continuous and preserves finite limits, hence defines a morphism
of topoi. On the small presentations its inverse image is the left Kan extension followed
by sheafification; both use colimits indexed by sets in the coefficient universe. Inverse
image of sets preserves finite products, so it transports the zero, addition and negation
of each abelian sheaf and their equations to an abelian sheaf. The set-sheaf adjunction
restricts to homomorphisms, since its unit and counit respect these operations. Transport
this adjunction back through the dense-subsite equivalences. Its right adjoint evaluates
at the base-changed object, exactly the displayed direct image. This constructs a left
adjoint H with the required adjunction. Only adjunction existence is asserted; no arbitrary
witness from this theorem is used as the data of a definition. -/
theorem strictHenselian_stalkSections_comparison_functor
    {X Y : Scheme.{u + 1}} (g : Y ⟶ X) :
    ∃ H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
        Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1},
      Nonempty (H ⊣ g.Etale.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        X.smallEtaleTopology Y.smallEtaleTopology) := by
  let e := (equivSmallModel X.AffineEtale).inverse
  let J := e.inducedTopology (Scheme.AffineEtale.topology X)
  have : e.IsContinuous J (Scheme.AffineEtale.topology X) := by
    dsimp [e, J]
    infer_instance
  let i := e ⋙ Scheme.AffineEtale.Spec X
  have : i.IsContinuous J X.smallEtaleTopology :=
    Functor.isContinuous_comp _ _ _ (Scheme.AffineEtale.topology X) _
  have : (i ⋙ g.Etale).IsContinuous J Y.smallEtaleTopology :=
    Functor.isContinuous_comp _ _ _ X.smallEtaleTopology _
  have : ((i ⋙ g.Etale).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      J Y.smallEtaleTopology).IsRightAdjoint := by infer_instance
  have : (e.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      J (Scheme.AffineEtale.topology X)).IsEquivalence := by
    dsimp [e, J]
    infer_instance
  have : (i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      J X.smallEtaleTopology).IsEquivalence := by
    exact Functor.isEquivalence_of_iso
      (Functor.sheafPushforwardContinuousComp e (Scheme.AffineEtale.Spec X)
        AddCommGrpCat.{u + 1} J (Scheme.AffineEtale.topology X) X.smallEtaleTopology)
  have : (g.Etale.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      X.smallEtaleTopology Y.smallEtaleTopology).IsRightAdjoint := by
    apply (Functor.isRightAdjoint_comp_iff_left _
      (i.sheafPushforwardContinuous AddCommGrpCat.{u + 1} J X.smallEtaleTopology)).mp
    exact Functor.isRightAdjoint_of_iso
      (Functor.sheafPushforwardContinuousComp i g.Etale AddCommGrpCat.{u + 1}
        J X.smallEtaleTopology Y.smallEtaleTopology).symm
  exact Functor.IsRightAdjoint.exists_leftAdjoint
