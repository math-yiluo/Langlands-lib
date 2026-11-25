/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
import WeilConjectures.CategoryTheory.Sites.EtaleTorsorH1Functoriality
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageJointRepresentatives


/-!
# Equivariant morphisms for scheme torsor inverse image

Source: Stacks Project Tags 03Q1 (4), 03AG and 0A5G.
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Etale

/-- Unit-equivariant maps from an inverse-image torsor sheaf are invertible.
Source: Stacks Project Section 03AG (morphisms of torsors), and Tag 03Q1 (4).
(blueprint: lem-weil-pbc-scheme-torsor-pullback-equivariant-hom-is-iso)

Proof: Inverse image preserves the torsor action and local nonemptiness, since it
preserves finite limits and covering epimorphisms. The displayed equation on units
implies equivariance on arbitrary local sections: sections of both inverse images
are locally represented by source-site sections, by the sheafification construction
of inverse image; refine the two representing covers to a common one and use
naturality, followed by separatedness. An equivariant map between torsors is locally
bijective. Locally choose a section of the source torsor. Translation identifies
both torsors with the coefficient group, and the map becomes the identity on that
group. Hence it is locally injective and locally surjective, and is an isomorphism
of sheaves. This argument also covers empty site objects and the trivial group:
local nonemptiness is the torsor axiom, not a global section assumption. -/
theorem scheme_torsor_pullback_equivariant_hom_isIso
    {Y Y₀ : Scheme.{u}} (i : Y₀ ⟶ Y)
    (M : Type (u + 1)) [AddCommGroup M] [Finite M]
    (t : Scheme.EtaleTorsor M Y)
    (R : Sheaf.Torsor ((upperStar AddCommGrpCat.{u + 1} i).obj
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of M))))
    (f : (Scheme.etaleSetPullback i).obj t.toSheafTorsor.sheaf ⟶ R.sheaf)
    (hf :
      let G := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of M)
      (∀ (W : Y.Etale) (g : G.obj.obj (op W)) (x : t.toSheafTorsor.sheaf.obj.obj (op W)),
      f.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj W))
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (u + 1))
          (Y.smallGrothendieckTopology @Etale)
          (Y₀.smallGrothendieckTopology @Etale)).unit.app t.toSheafTorsor.sheaf).hom.app (op W)
            (t.toSheafTorsor.vadd (op W) g x)) =
      R.vadd (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj W))
        (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit.app G).hom.app
          (op W) g)
        (f.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj W))
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (u + 1))
            (Y.smallGrothendieckTopology @Etale)
            (Y₀.smallGrothendieckTopology @Etale)).unit.app t.toSheafTorsor.sheaf).hom.app
              (op W) x)))) : IsIso f := by
  let G := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of M)
  obtain ⟨T, e, he, _⟩ := Sheaf.Torsor.etale_torsor_h1_functoriality.1
    Y Y₀ i G t.toSheafTorsor
  let q := e.inv ≫ f
  have hq : ∀ (U : Y₀.Etaleᵒᵖ)
      (a : ((upperStar AddCommGrpCat.{u + 1} i).obj G).obj.obj U)
      (x : T.sheaf.obj.obj U),
      q.hom.app U (T.vadd U a x) = R.vadd U a (q.hom.app U x) := by
    intro U a x
    obtain ⟨S, hS, hrep⟩ := etaleInverseImage_joint_representatives i G
      t.toSheafTorsor.sheaf U a (e.inv.hom.app U x)
    apply ((isSheaf_iff_isSheaf_of_type _ _).mp R.sheaf.property _ hS).isSeparatedFor.ext
    intro V j hj
    obtain ⟨W, k, g, s, ha, hx⟩ := hrep V j hj
    let b := MorphismProperty.Over.pullback @Etale ⊤ i
    let η := (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous b
      (Type (u + 1)) (Y.smallGrothendieckTopology @Etale)
      (Y₀.smallGrothendieckTopology @Etale)).unit.app t.toSheafTorsor.sheaf
    let ηG := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit.app G
    have hcancel (Z : Y₀.Etaleᵒᵖ) (z : T.sheaf.obj.obj Z) :
        e.hom.hom.app Z (e.inv.hom.app Z z) = z := by
      exact congrArg (fun r ↦ r.hom.app Z z) e.inv_hom_id
    have hcancel' (Z : Y₀.Etaleᵒᵖ)
        (z : ((Scheme.etaleSetPullback i).obj t.toSheafTorsor.sheaf).obj.obj Z) :
        e.inv.hom.app Z (e.hom.hom.app Z z) = z := by
      exact congrArg (fun r ↦ r.hom.app Z z) e.hom_inv_id
    have hx' : T.sheaf.obj.map j.op x =
        T.sheaf.obj.map k.op (e.hom.hom.app (op (b.obj W))
          (η.hom.app (op W) s)) := by
      have h := congrArg (e.hom.hom.app (op V)) hx
      rw [NatTrans.naturality_apply e.hom.hom j.op,
        NatTrans.naturality_apply e.hom.hom k.op, hcancel] at h
      exact h
    have hunit : q.hom.app (op (b.obj W))
        (T.vadd (op (b.obj W)) (ηG.hom.app (op W) g)
          (e.hom.hom.app (op (b.obj W)) (η.hom.app (op W) s))) =
        R.vadd (op (b.obj W)) (ηG.hom.app (op W) g)
          (q.hom.app (op (b.obj W))
            (e.hom.hom.app (op (b.obj W)) (η.hom.app (op W) s))) := by
      change f.hom.app _ (e.inv.hom.app _ _) =
        R.vadd _ _ (f.hom.app _ (e.inv.hom.app _ _))
      rw [← he W g s, hcancel', hcancel']
      exact hf W g s
    rw [← NatTrans.naturality_apply q.hom j.op, T.map_vadd j.op,
      R.map_vadd j.op, ← NatTrans.naturality_apply q.hom j.op, ha, hx',
      ← T.map_vadd k.op, NatTrans.naturality_apply q.hom k.op,
      hunit, R.map_vadd k.op, ← NatTrans.naturality_apply q.hom k.op]
  let E := Sheaf.Torsor.Iso.ofHom q hq
  have : IsIso q := by
    change IsIso E.iso.hom
    infer_instance
  have h : f = e.hom ≫ q := by
    simp [q]
  rw [h]
  infer_instance

end AlgebraicGeometry.Etale
