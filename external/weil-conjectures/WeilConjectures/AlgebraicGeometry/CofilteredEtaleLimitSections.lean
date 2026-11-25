/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import WeilConjectures.AlgebraicGeometry.DirectedEtaleLimitSections
import Mathlib.CategoryTheory.Presentable.Directed
import Mathlib.CategoryTheory.Limits.Final

/-! # Sections over a cofiltered limit of etale schemes

Source: Stacks Project, Tag 03Q9, degree zero, using Tags 09YQ and 03S2.
(blueprint: lem-weil-pbc-cofiltered-etale-limit-sections).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
variable {J : Type u} [SmallCategory J] {R : Scheme.{u}}
  (B : J ⥤ R.Etale) (c : Cone (B ⋙ Scheme.Etale.forget R ⋙ Over.forget R))
  (p : c.pt ⟶ R) (h : ∀ j, c.π.app j ≫ (B.obj j).hom = p)

/-- The diagonal section map from the terminal etale object of the limit to the
base change of a stage. Its first component is the limit leg; its second is the identity.
Source: Stacks Project, Tag 03Q9, canonical section restriction.
(blueprint: lem-weil-pbc-cofiltered-etale-limit-sections). -/
noncomputable def limitSectionMap (j : J) :
    Scheme.Etale.mk (𝟙 c.pt) ⟶
      (MorphismProperty.Over.pullback @Etale ⊤ p).obj (B.obj j) :=
  MorphismProperty.Over.homMk
    (pullback.lift (c.π.app j) (𝟙 _) (by simpa using h j))
    (pullback.lift_snd _ _ _)

set_option backward.isDefEq.respectTransparency false

/-- Compatibility of the diagonal section maps with transition morphisms.
Source: Stacks Project, Tag 03Q9, compatibility of the section comparison components.
(blueprint: lem-weil-pbc-cofiltered-etale-limit-sections).
Proof: compare the two pullback projections, using the cone's naturality for the
first projection and the identity for the second. -/
theorem limitSectionMap_naturality {j k : J} (a : j ⟶ k) :
    limitSectionMap B c p h j ≫
      (MorphismProperty.Over.pullback @Etale ⊤ p).map (B.map a) =
        limitSectionMap B c p h k := by
  apply MorphismProperty.Over.Hom.ext
  change pullback.lift _ _ _ ≫ pullback.lift _ _ _ = pullback.lift _ _ _
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    have hw := c.w a
    change c.π.app j ≫
      (MorphismProperty.Over.forget @Etale ⊤ R ⋙ Over.forget R).map (B.map a) =
        c.π.app k at hw
    rw [MorphismProperty.Over.forget_comp_forget_map] at hw
    exact hw
  · simp only [Category.assoc, pullback.lift_snd]

variable (H : Sheaf R.smallEtaleTopology (Type (u + 1)))

set_option backward.isDefEq.respectTransparency false

/-- The section cocone whose components pull back by the adjunction unit and then
restrict along `limitSectionMap`. Unit naturality and compatibility of the cone legs
prove naturality, without any continuity hypothesis.
Source: Stacks Project, Tag 03Q9, degree-zero comparison map.
(blueprint: lem-weil-pbc-cofiltered-etale-limit-sections). -/
noncomputable def limitSectionCocone : Cocone (B.op ⋙ H.obj) where
  pt := ((Scheme.etaleSetPullback p).obj H).obj.obj (op (Scheme.Etale.mk (𝟙 c.pt)))
  ι.app j :=
    (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ p) (Type (u + 1))
      (R.smallGrothendieckTopology @Etale)
      (c.pt.smallGrothendieckTopology @Etale)).unit.app H).hom.app (op (B.obj j.unop))) ≫
      ((Scheme.etaleSetPullback p).obj H).obj.map
        (limitSectionMap B c p h j.unop).op
  ι.naturality j k a := by
    dsimp
    rw [Category.comp_id]
    rw [← Category.assoc]
    rw [NatTrans.naturality]
    change _ ≫ ((Scheme.etaleSetPullback p).obj H).obj.map
      (((MorphismProperty.Over.pullback @Etale ⊤ p).map (B.map a.unop)).op) ≫ _ = _
    rw [← Functor.map_comp]
    congr 2
    exact congrArg Quiver.Hom.op (limitSectionMap_naturality B c p h a.unop)

/-- The explicit unit/restriction cocone is a colimit when its etale stages are qcqs,
its transition morphisms are affine, and its scheme cone is limiting. The base scheme
need not be quasi-separated; all qcqs assumptions concern the stages.
Source: Stacks Project, Tag 03Q9, degree zero, using Theorem 09YQ and Tag 03S2.
(blueprint: lem-weil-pbc-cofiltered-etale-limit-sections).

Proof:
1. Apply `exists_directed_reindexing` to `J` opposite, obtaining one nonempty directed
   index preserving both the scheme limit and the section colimit. Choose a stage zero
   and restrict to its cofinal upper tail.
2. On stage zero take the inverse image of H along its etale structure map to R, and
   take the terminal etale object. Apply `etaleSetSectionContinuity`: the stages are
   qcqs, their maps are affine, and the terminal object's structure morphism is qcqs.
3. Inverse-image composition identifies the sheaf at every stage with the inverse
   image of H along its structure map to R, and the limit sheaf with the inverse
   image along p, using the equations h. Each stage structure map is etale.
   `etaleSetInverseImageRestriction` identifies its terminal sections with H(B_j).
   Its unit equation and inverse-image composition identify the transition maps
   with H applied to the opposite of B's maps.
4. The limit components, under the same identifications, are the unit for p followed
   by restriction along the map with components c_j and the identity. This is
   `limitSectionMap`, as checked by its two pullback projections. Thus the cocone is
   exactly `limitSectionCocone`. Continuity's bijective colimit comparison makes it
   a colimit. Cofinality of the upper tail and the directed reindexing gives the
   asserted colimit over J opposite.
Small cases: a one-object identity diagram gives etale restriction; an empty stage
is allowed and its terminal section set is a singleton by the empty-cover sheaf axiom.
The cofiltered hypothesis excludes an empty indexing category. -/
theorem cofilteredLimitSections
    {J : Type u} [SmallCategory J] {R : Scheme.{u}}
    (B : J ⥤ R.Etale) (c : Cone (B ⋙ Scheme.Etale.forget R ⋙ Over.forget R))
    (p : c.pt ⟶ R) (h : ∀ j, c.π.app j ≫ (B.obj j).hom = p)
    (H : Sheaf R.smallEtaleTopology (Type (u + 1))) [IsCofiltered J]
    [∀ j : J, CompactSpace (B.obj j).left]
    [∀ j : J, QuasiSeparatedSpace (B.obj j).left]
    [∀ {j k : J} (a : j ⟶ k), IsAffineHom (B.map a).left]
    (_hc : IsLimit c) : Nonempty (IsColimit (limitSectionCocone B c p h H)) := by
  obtain ⟨I, horder, hdirected, hnonempty, F, hfinal⟩ :=
    IsFiltered.exists_directed Jᵒᵖ
  let := horder
  let := hdirected
  let := hnonempty
  let := hfinal
  let B' := F.leftOp ⋙ B
  let c' := c.whisker F.leftOp
  have : ∀ i : Iᵒᵖ, CompactSpace (B'.obj i).left :=
    fun i ↦ inferInstanceAs (CompactSpace (B.obj (F.leftOp.obj i)).left)
  have : ∀ i : Iᵒᵖ, QuasiSeparatedSpace (B'.obj i).left :=
    fun i ↦ inferInstanceAs (QuasiSeparatedSpace (B.obj (F.leftOp.obj i)).left)
  have : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (B'.map a).left :=
    fun a ↦ inferInstanceAs (IsAffineHom (B.map (F.leftOp.map a)).left)
  have hc' : IsLimit c' :=
    (Functor.Initial.isLimitWhiskerEquiv F.leftOp c).symm _hc
  have h' : ∀ i, c'.π.app i ≫ (B'.obj i).hom = p :=
    fun i ↦ h (F.leftOp.obj i)
  let κ := (limitSectionCocone B c p h H).whisker F.leftOp.op
  obtain ⟨hcκ⟩ := directedEtaleLimitSections B' c' p h' H hc' κ.ι (fun _ ↦ rfl)
  exact ⟨Functor.Final.isColimitWhiskerEquiv F.leftOp.op
    (limitSectionCocone B c p h H) hcκ⟩

end AlgebraicGeometry
