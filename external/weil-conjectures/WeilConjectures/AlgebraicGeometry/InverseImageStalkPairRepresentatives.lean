/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Stalks
import Mathlib.CategoryTheory.Sites.LocallySurjective

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace TopCat

/-- Two inverse-image stalk elements are unit germs on a common neighbourhood.
Source: Stacks Project, Sheaves, Tags 008H, 008G and 007Z.
(blueprint: lem-weil-pbc-inverse-image-stalk-pair-representatives).

Proof: every stalk element is a colimit coprojection of a section of the
inverse-image sheaf on a neighbourhood N. The sheafification unit is locally
surjective: its locally generated image is a subsheaf R, and the universal
property of sheafification gives a map back to R whose composite with inclusion
is the identity. Therefore the section on N lifts through the unit on a smaller
neighbourhood V of z. The pointwise left Kan extension is a colimit, so the lift
comes from a section a on an open W of X, with V contained in f^{-1}W. Thus W
contains f(z). The constructed adjunction unit is the presheaf Kan-extension
unit followed by sheafification. Naturality and the neighbourhood-colimit
relations show that the germ of its value on a equals the original element.
Do this for both elements; restrict their representatives to W1 intersect W2.
Naturality of the unit and the colimit relations preserve their germs.
This argument allows the value universe to be larger than the space universe.
For empty Z there is no z and hence no instance. -/
theorem inverse_image_stalk_pair_representatives
    {X Z : TopCat.{u}} (f : Z ⟶ X) (A : X.Sheaf (Type (max u w))) (z : Z)
    (s t : colimit ((OpenNhds.inclusion z).op ⋙
      ((Functor.sheafPullbackConstruction.sheafPullback
        (Opens.map f) (Type (max u w))
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)).obj A).obj)) :
    ∃ (W : Opens X) (hzW : f z ∈ W) (a b : A.obj.obj (op W)),
      colimit.ι ((OpenNhds.inclusion z).op ⋙
        ((Functor.sheafPullbackConstruction.sheafPullback
          (Opens.map f) (Type (max u w))
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)).obj A).obj)
        (op ⟨(Opens.map f).obj W, hzW⟩)
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (Opens.map f) (Type (max u w))
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)).unit.app A).hom.app
            (op W) a) = s ∧
      colimit.ι ((OpenNhds.inclusion z).op ⋙
        ((Functor.sheafPullbackConstruction.sheafPullback
          (Opens.map f) (Type (max u w))
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)).obj A).obj)
        (op ⟨(Opens.map f).obj W, hzW⟩)
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (Opens.map f) (Type (max u w))
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)).unit.app A).hom.app
            (op W) b) = t := by
  classical
  let P := (Opens.map f).op.leftKanExtension A.obj
  let H := (Functor.sheafPullbackConstruction.sheafPullback
    (Opens.map f) (Type (max u w))
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)).obj A
  let eta := (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map f) (Type (max u w))
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)).unit.app A
  let theta := toSheafify (Opens.grothendieckTopology Z) P
  let D := (OpenNhds.inclusion z).op ⋙ H.obj
  have hloc : CategoryTheory.Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology Z) theta := by
    let J := Opens.grothendieckTopology Z
    let G := sheafify J P
    have hG : CategoryTheory.Presheaf.IsSheaf J G :=
      (presheafToSheaf J (Type (max u w))).obj P |>.property
    have hG' := (isSheaf_iff_isSheaf_of_type J G).mp hG
    let R := (Subfunctor.range theta).sheafify J
    have hR : CategoryTheory.Presheaf.IsSheaf J R.toFunctor :=
      (isSheaf_iff_isSheaf_of_type J R.toFunctor).mpr
        ((Subfunctor.range theta).sheafify_isSheaf hG')
    let l := sheafifyLift J (Subfunctor.toRangeSheafify J theta) hR
    have hl : l ≫ R.ι = 𝟙 G := by
      apply sheafify_hom_ext J _ _ hG
      dsimp [l]
      rw [← Category.assoc, toSheafify_sheafifyLift]
      simp [Subfunctor.toRangeSheafify, R, theta, G, J]
    rw [CategoryTheory.Presheaf.isLocallySurjective_iff_range_sheafify_eq_top']
    apply le_antisymm le_top
    intro U a _
    have e : (l.app U a).val = a := by
      have := congrArg (fun t ↦ t.app U a) hl
      simpa [G, J] using this
    exact e ▸ (l.app U a).property
  have single (t : colimit D) : ∃ (W : Opens X) (hzW : f z ∈ W)
      (a : A.obj.obj (op W)),
      colimit.ι D (op ⟨(Opens.map f).obj W, hzW⟩) (eta.hom.app (op W) a) = t := by
    obtain ⟨n, a, rfl⟩ := Types.jointly_surjective D (colimit.isColimit D) t
    have hcover := CategoryTheory.Presheaf.imageSieve_mem
      (Opens.grothendieckTopology Z) theta a
    obtain ⟨V, g, ⟨p, hp⟩, hzV⟩ := hcover z n.unop.property
    obtain ⟨j, b, hb⟩ := Types.jointly_surjective _
      ((Opens.map f).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit A.obj (op V)) p
    let W := j.left.unop
    have hzW : f z ∈ W := leOfHom j.hom.unop hzV
    refine ⟨W, hzW, b, ?_⟩
    have hpb : P.map j.hom
        (((Opens.map f).op.leftKanExtensionUnit A.obj).app j.left b) = p := hb
    have hu : eta.hom.app (op W) b =
        theta.app (op ((Opens.map f).obj W))
          (((Opens.map f).op.leftKanExtensionUnit A.obj).app (op W) b) := by
      rfl
    have he : H.obj.map j.hom (eta.hom.app (op W) b) = H.obj.map g.op a := by
      rw [hu]
      have hn := theta.naturality_apply j.hom
        (((Opens.map f).op.leftKanExtensionUnit A.obj).app (op W) b)
      exact hn.symm.trans ((congrArg (theta.app (op V)) hpb).trans hp)
    let m : (OpenNhds z)ᵒᵖ := op ⟨V, hzV⟩
    let k : (OpenNhds z)ᵒᵖ := op ⟨(Opens.map f).obj W, hzW⟩
    let q : k ⟶ m := (homOfLE (leOfHom j.hom.unop)).op
    let r : n ⟶ m := (homOfLE (leOfHom g)).op
    have hq := congrArg (fun h ↦ h (eta.hom.app (op W) b))
      (congrArg ConcreteCategory.hom (colimit.w D q))
    have hr := congrArg (fun h ↦ h a)
      (congrArg ConcreteCategory.hom (colimit.w D r))
    exact hq.symm.trans ((congrArg (colimit.ι D m) he).trans hr)
  obtain ⟨W1, hz1, a, ha⟩ := single s
  obtain ⟨W2, hz2, b, hb⟩ := single t
  let W := W1 ⊓ W2
  let g1 : W ⟶ W1 := homOfLE inf_le_left
  let g2 : W ⟶ W2 := homOfLE inf_le_right
  refine ⟨W, ⟨hz1, hz2⟩, A.obj.map g1.op a, A.obj.map g2.op b, ?_, ?_⟩
  · have hn := eta.hom.naturality_apply g1.op a
    have hw := congrArg (fun h ↦ h (eta.hom.app (op W1) a))
      (congrArg ConcreteCategory.hom (colimit.w D
        ((homOfLE (show (Opens.map f).obj W ≤ (Opens.map f).obj W1 from
          fun x hx ↦ hx.1)).op :
          op ⟨(Opens.map f).obj W1, hz1⟩ ⟶
            op ⟨(Opens.map f).obj W, ⟨hz1, hz2⟩⟩)))
    exact (congrArg (colimit.ι D (op ⟨(Opens.map f).obj W, ⟨hz1, hz2⟩⟩)) hn).trans
      (hw.trans ha)
  · have hn := eta.hom.naturality_apply g2.op b
    have hw := congrArg (fun h ↦ h (eta.hom.app (op W2) b))
      (congrArg ConcreteCategory.hom (colimit.w D
        ((homOfLE (show (Opens.map f).obj W ≤ (Opens.map f).obj W2 from
          fun x hx ↦ hx.2)).op :
          op ⟨(Opens.map f).obj W2, hz2⟩ ⟶
            op ⟨(Opens.map f).obj W, ⟨hz1, hz2⟩⟩)))
    exact (congrArg (colimit.ι D (op ⟨(Opens.map f).obj W, ⟨hz1, hz2⟩⟩)) hn).trans
      (hw.trans hb)

end TopCat
