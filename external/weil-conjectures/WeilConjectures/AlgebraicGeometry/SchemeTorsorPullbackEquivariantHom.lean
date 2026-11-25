/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
import WeilConjectures.AlgebraicGeometry.EtaleConstantSheafPullbackUnitContinuousMap


/-!
# Equivariant morphisms for scheme torsor inverse image

Source: Stacks Project Tags 03Q1 (4), 03AG and 0A5G.
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Etale

-- Check the action on the open fibres of the locally constant coefficient.
-- On each fibre, equality of both pullback projections reduces it to hact.
private theorem baseChange_smulHom
    {Y Y₀ : Scheme.{u}} (i : Y₀ ⟶ Y)
    {M : Type (u + 1)} [AddCommGroup M] [Finite M]
    [TopologicalSpace M] [DiscreteTopology M]
    (t : Scheme.EtaleTorsor M Y) (t₀ : Scheme.EtaleTorsor M Y₀)
    (e : pullback t.π i ≅ t₀.P)
    (he : e.hom ≫ t₀.π = pullback.snd t.π i)
    (hact : ∀ m : M,
      pullback.map t.π i t.π i (t.vadd m) (𝟙 Y₀) (𝟙 Y)
        (by rw [Category.comp_id, t.vadd_π])
        (by rw [Category.comp_id, Category.id_comp]) ≫ e.hom = e.hom ≫ t₀.vadd m)
    (W : Y.Etale) (g : C(W.left, M)) (x : W ⟶ t.toEtale) :
    i.Etale.map (t.smulHom g x) ≫
      (MorphismProperty.Over.homMk e.hom he : i.Etale.obj t.toEtale ⟶ t₀.toEtale) =
      t₀.smulHom (g.comp (pullback.fst W.hom i).base.hom)
        (i.Etale.map x ≫
          (MorphismProperty.Over.homMk e.hom he : i.Etale.obj t.toEtale ⟶ t₀.toEtale)) := by
  apply MorphismProperty.Over.Hom.ext
  change (i.Etale.map (t.smulHom g x)).left ≫ e.hom = _
  apply Scheme.hom_ext_fiberOpens (g.comp (pullback.fst W.hom i).base.hom)
  intro m
  let V := (pullback W.hom i).fiberOpens
    (g.comp (pullback.fst W.hom i).base.hom) m
  rw [t₀.smulHom_left]
  rw [Scheme.fiberOpens_ι_glueOfContinuousMap]
  have hb : V.ι ≫ (i.Etale.map (t.smulHom g x)).left =
      V.ι ≫ (i.Etale.map x).left ≫
        pullback.map t.π i t.π i (t.vadd m) (𝟙 Y₀) (𝟙 Y)
          (by rw [Category.comp_id, t.vadd_π])
          (by rw [Category.comp_id, Category.id_comp]) := by
    have hfst₁ := i.etale_map_left_comp_fst (t.smulHom g x)
    have hfst₂ := i.etale_map_left_comp_fst x
    have hsnd₁ := i.etale_map_left_comp_snd (t.smulHom g x)
    have hsnd₂ := i.etale_map_left_comp_snd x
    change (i.Etale.map (t.smulHom g x)).left ≫ pullback.fst t.π i = _ at hfst₁
    change (i.Etale.map x).left ≫ pullback.fst t.π i = _ at hfst₂
    change (i.Etale.map (t.smulHom g x)).left ≫ pullback.snd t.π i = _ at hsnd₁
    change (i.Etale.map x).left ≫ pullback.snd t.π i = _ at hsnd₂
    apply pullback.hom_ext
    · change _ ≫ pullback.fst t.π i = _ ≫ pullback.fst t.π i
      simp only [Category.assoc, hfst₁, pullback.map, pullback.lift_fst,
        Category.comp_id]
      rw [t.smulHom_left, Scheme.comp_glueOfContinuousMap]
      rw [Scheme.fiberOpens_ι_glueOfContinuousMap]
      simp only [← Category.assoc, hfst₂]
      rfl
    · change _ ≫ pullback.snd t.π i = _ ≫ pullback.snd t.π i
      simp [Category.assoc, pullback.map, hsnd₁, hsnd₂]
  change V.ι ≫ (i.Etale.map (t.smulHom g x)).left ≫ e.hom =
    V.ι ≫ ((i.Etale.map x).left ≫ e.hom) ≫ t₀.vadd m
  rw [← Category.assoc, hb]
  simp only [Category.assoc, hact]

/-- An equivariant map from the inverse-image sheaf to the represented torsor.
Source: Stacks Project Tags 03Q1 (4), 03AG and 0A5G, final paragraph.
(blueprint: lem-weil-pbc-scheme-torsor-pullback-equivariant-hom)

Proof: The adjunction and Yoneda identify inverse image of the sheaf represented by
`t` with the sheaf represented by its base change. Compose its canonical comparison
with Yoneda of `e`, then with the given torsor identification `hrepr`. This supplies a
sheaf morphism without any invertibility assertion. The representable comparison
carries the unit of a section to its base change. For a constant coefficient `m`,
`hact` and the constant-sheaf comparison's unit identity give the displayed equation.
Every coefficient section is locally the unit of a constant presheaf section: use
sheafification's local representation property. On that cover the preceding equation
applies. Pull the cover back along `i`, use naturality of the two units and of the
morphism and actions, and use separatedness of `R.sheaf` to glue the equalities.
The inverse of the coefficient comparison in `ofIso` cancels its forward map, leaving
exactly the coefficient adjunction unit in the formula. -/
theorem scheme_torsor_pullback_equivariant_hom
    {Y Y₀ : Scheme.{u}} (i : Y₀ ⟶ Y)
    (M : Type (u + 1)) [AddCommGroup M] [Finite M]
    (t : Scheme.EtaleTorsor M Y) (t₀ : Scheme.EtaleTorsor M Y₀)
    (e : pullback t.π i ≅ t₀.P)
    (he : e.hom ≫ t₀.π = pullback.snd t.π i)
    (hact : ∀ m : M,
      pullback.map t.π i t.π i (t.vadd m) (𝟙 Y₀) (𝟙 Y)
        (by rw [Category.comp_id, t.vadd_π])
        (by rw [Category.comp_id, Category.id_comp]) ≫ e.hom = e.hom ≫ t₀.vadd m)
    (R : Sheaf.Torsor ((upperStar AddCommGrpCat.{u + 1} i).obj
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of M))))
    (hrepr : t₀.toSheafTorsor ≈ Sheaf.Torsor.ofIso
      ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} i).app
        (AddCommGrpCat.of M)) R) :
    ∃ f : (Scheme.etaleSetPullback i).obj t.toSheafTorsor.sheaf ⟶ R.sheaf,
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
              (op W) x))) := by
  classical
  let F := MorphismProperty.Over.pullback @Etale ⊤ i
  let : F.IsContinuous Y.smallEtaleTopology Y₀.smallEtaleTopology :=
    Etale.isContinuous_overPullback i
  let E : F.obj t.toEtale ⟶ t₀.toEtale := MorphismProperty.Over.homMk e.hom he
  -- Base change of points, followed by e, is a natural transformation.
  let b : t.toSheafTorsor.sheaf ⟶
      (F.sheafPushforwardContinuous (Type (u + 1))
        Y.smallEtaleTopology Y₀.smallEtaleTopology).obj t₀.toSheafTorsor.sheaf :=
    ⟨{
      app W := TypeCat.ofHom (fun x ↦ ⟨F.map x.down ≫ E⟩)
      naturality W V a := by
        ext x
        apply ULift.ext
        change F.map (a.unop ≫ x.down) ≫ E =
          F.map a.unop ≫ (F.map x.down ≫ E)
        rw [F.map_comp, Category.assoc] }⟩
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    F (Type (u + 1)) Y.smallEtaleTopology Y₀.smallEtaleTopology
  -- Its adjunct has the prescribed evaluation on every adjunction-unit section.
  let f₀ := (adj.homEquiv _ _).symm b
  obtain ⟨r⟩ := hrepr
  refine ⟨f₀ ≫ r.iso.hom, ?_⟩
  dsimp only
  intro W g x
  have hf₀ : adj.unit.app t.toSheafTorsor.sheaf ≫
      (F.sheafPushforwardContinuous (Type (u + 1))
        Y.smallEtaleTopology Y₀.smallEtaleTopology).map f₀ = b := by
    simpa only [adj.homEquiv_unit] using (adj.homEquiv _ _).apply_symm_apply b
  have hf (x : t.toSheafTorsor.sheaf.obj.obj (op W)) :
      f₀.hom.app (op (F.obj W))
        ((adj.unit.app t.toSheafTorsor.sheaf).hom.app (op W) x) =
          b.hom.app (op W) x := by
    exact congrArg (fun k ↦ k.hom.app (op W) x) hf₀
  change r.iso.hom.hom.app (op (F.obj W))
      (f₀.hom.app (op (F.obj W))
        ((adj.unit.app t.toSheafTorsor.sheaf).hom.app (op W) _)) =
    R.vadd _ _ (r.iso.hom.hom.app (op (F.obj W))
      (f₀.hom.app (op (F.obj W))
        ((adj.unit.app t.toSheafTorsor.sheaf).hom.app (op W) x)))
  rw [hf, hf]
  let : TopologicalSpace M := ⊥
  let : DiscreteTopology M := ⟨rfl⟩
  let c := (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} i).app
    (AddCommGrpCat.of M)
  let a := ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit.app
    ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of M))).hom.app (op W) g
  -- Express coefficient transport as pullback of locally constant functions.
  have ha := constant_pullback_unit_continuousMap i M W g
  change (Scheme.Etale.constantSheafIsoContinuousMapSheaf Y₀ M).hom.hom.app
    (op (F.obj W)) (c.hom.hom.app (op (F.obj W)) a) = _ at ha
  have hb : b.hom.app (op W) (t.toSheafTorsor.vadd (op W) g x) =
      t₀.toSheafTorsor.vadd (op (F.obj W))
        (c.hom.hom.app (op (F.obj W)) a) (b.hom.app (op W) x) := by
    apply ULift.ext
    change F.map (t.smulHom
      ((Scheme.Etale.constantSheafIsoContinuousMapSheaf Y M).hom.hom.app (op W) g)
      x.down) ≫ E = t₀.smulHom _ (F.map x.down ≫ E)
    simp only [Iso.symm_inv]
    rw [ha]
    exact baseChange_smulHom i t t₀ e he hact W _ x.down
  rw [hb, r.map_vadd]
  change R.vadd _ (c.inv.hom.app _ (c.hom.hom.app _ a)) _ = R.vadd _ a _
  congr 1
  exact (((sheafToPresheaf Y₀.smallEtaleTopology AddCommGrpCat.{u + 1}) ⋙
    (evaluation _ _).obj (op (F.obj W))).mapIso c).hom_inv_id_apply a

end AlgebraicGeometry.Etale
