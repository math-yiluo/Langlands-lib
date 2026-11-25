/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Residue fields at points of inverse limits

Source: Stacks Project, Limits, Lemma 0CUG (1)
(blueprint: lem-weil-pbc-limit-residue-field).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private noncomputable def pointedResidueMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : X) (y : Y) (h : y = f x) : Y.residueField y ⟶ X.residueField x :=
  (Y.residueFieldCongr h).hom ≫ f.residueFieldMap x

private theorem pointedResidueMap_heq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : X) (y : Y) (h : y = f x) :
    HEq (pointedResidueMap f x y h) (f.residueFieldMap x) := by
  subst y
  simp [pointedResidueMap]

private theorem pointedResidueMap_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) (y : Y) (z : Z)
    (hy : y = f x) (hz : z = g y) (h : z = (f ≫ g) x) :
    pointedResidueMap g y z hz ≫ pointedResidueMap f x y hy =
      pointedResidueMap (f ≫ g) x z h := by
  subst y z
  simp [pointedResidueMap]

private theorem pointedResidueMap_congr {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (hfg : f = g) (x : X) (y : Y) (hf : y = f x) (hg : y = g x) :
    pointedResidueMap f x y hf = pointedResidueMap g x y hg := by
  subst g
  rfl

private theorem pointedResidueMap_id (X : Scheme.{u}) (x : X)
    (f : X ⟶ X) (hf : f = 𝟙 X) (h : x = f x) :
    pointedResidueMap f x x h = 𝟙 (X.residueField x) := by
  subst f
  simp [pointedResidueMap]

private noncomputable def residueDiagram {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (s : c.pt) : I ⥤ CommRingCat.{u} where
  obj i := (D.obj (op i)).residueField (c.π.app (op i) s)
  map {i j} f := pointedResidueMap (D.map f.op)
    (c.π.app (op j) s) (c.π.app (op i) s)
    (by rw [← Scheme.Hom.comp_apply, c.w f.op]; rfl)
  map_id i := by
    exact pointedResidueMap_id _ _ _ (D.map_id _) _
  map_comp {i j k} f g := by
    dsimp
    rw [pointedResidueMap_comp (h := by
      rw [← D.map_comp, ← Scheme.Hom.comp_apply, c.w])]
    apply pointedResidueMap_congr
    exact D.map_comp g.op f.op

private noncomputable def residueCocone {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (s : c.pt) :
    Cocone (residueDiagram D c s) where
  pt := c.pt.residueField s
  ι :=
    { app := fun i ↦ (c.π.app (op i)).residueFieldMap s
      naturality := by
        intro i j f
        dsimp [residueDiagram]
        change pointedResidueMap (D.map f.op) (c.π.app (op j) s)
          (c.π.app (op i) s) _ ≫
          pointedResidueMap (c.π.app (op j)) s (c.π.app (op j) s) rfl = _
        rw [pointedResidueMap_comp (h := by rw [c.w]; rfl)]
        have h := pointedResidueMap_congr (c.w f.op) s (c.π.app (op i) s)
        simpa [pointedResidueMap] using h _ rfl }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem exists_section_rep {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ Scheme.{u})
    [∀ {i j : J} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) (i : J) (U : (D.obj i).Opens)
    (hU : IsAffineOpen U) (t : Γ(c.pt, c.π.app i ⁻¹ᵁ U)) :
    ∃ (j : J) (f : j ⟶ i) (v : Γ(D.obj j, D.map f ⁻¹ᵁ U))
      (h : c.π.app i ⁻¹ᵁ U = c.π.app j ⁻¹ᵁ D.map f ⁻¹ᵁ U),
      (c.π.app j).appLE (D.map f ⁻¹ᵁ U) (c.π.app i ⁻¹ᵁ U) h.le v = t := by
  have (j : Over i) : IsAffine ((opensDiagram D i U).obj j) := hU.preimage (D.map _)
  obtain ⟨j, v, hv⟩ := exists_appTop_π_eq_of_isAffine_of_isLimit
    (opensDiagram D i U) (opensCone D c i U) (isLimitOpensCone D c hc i U)
    ((c.π.app i ⁻¹ᵁ U).topIso.inv t)
  change Γ((D.map j.hom ⁻¹ᵁ U).toScheme, ⊤) at v
  refine ⟨j.left, j.hom, (D.map j.hom ⁻¹ᵁ U).topIso.hom v, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_preimage, c.w]
  · apply (c.π.app i ⁻¹ᵁ U).topIso.commRingCatIsoToRingEquiv.symm.injective
    change (c.π.app i ⁻¹ᵁ U).topIso.inv _ = (c.π.app i ⁻¹ᵁ U).topIso.inv t
    rw [← hv]
    change _ = ((c.π.app j.left).resLE (D.map j.hom ⁻¹ᵁ U)
      (c.π.app i ⁻¹ᵁ U) _).app ⊤ v
    rw [Scheme.Hom.resLE_app_top]
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem evaluation_appLE {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) (x : X) (hx : x ∈ V) :
    f.appLE U V e ≫ X.evaluation V x hx =
      Y.evaluation U (f x) (e hx) ≫ f.residueFieldMap x := by
  rw [Scheme.Hom.appLE, Category.assoc]
  have hres : X.presheaf.map (homOfLE e).op ≫ X.evaluation V x hx =
      X.evaluation (f ⁻¹ᵁ U) x (e hx) := by
    unfold Scheme.evaluation
    rw [← Category.assoc, TopCat.Presheaf.germ_res]
  rw [hres]
  exact (Scheme.evaluation_naturality f x (e hx)).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem exists_residue_rep {I : Type u} [Preorder I]
    [IsDirected I (· ≤ ·)] [Nonempty I] (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) (s : c.pt) (z : c.pt.residueField s) :
    ∃ (i : I) (a : (D.obj (op i)).residueField (c.π.app (op i) s)),
      (c.π.app (op i)).residueFieldMap s a = z := by
  obtain ⟨w, hw⟩ := c.pt.residue_surjective s z
  obtain ⟨V, hsV, ⟨i, U, hU, rfl⟩, t, ht⟩ :=
    TopCat.Presheaf.exists_mem_germ_eq_of_isBasis
      (isBasis_preimage_isAffineOpen D c hc) c.pt.presheaf s w
  obtain ⟨j, f, v, h, hv⟩ := exists_section_rep D c hc i U hU t
  have hs : c.π.app j s ∈ D.map f ⁻¹ᵁ U := by
    change s ∈ c.π.app j ⁻¹ᵁ D.map f ⁻¹ᵁ U
    rw [← h]
    exact hsV
  refine ⟨j.unop, (D.obj j).evaluation (D.map f ⁻¹ᵁ U) (c.π.app j s) hs v, ?_⟩
  change ((c.π.app j).residueFieldMap s)
    ((D.obj j).evaluation (D.map f ⁻¹ᵁ U) (c.π.app j s) hs v) = z
  rw [← CommRingCat.comp_apply, ← evaluation_appLE (c.π.app j)
    (D.map f ⁻¹ᵁ U) (c.π.app i ⁻¹ᵁ U) h.le s hsV,
    CommRingCat.comp_apply, hv]
  change c.pt.residue s (c.pt.presheaf.germ _ s hsV t) = z
  rw [ht, hw]

private noncomputable def isColimit_of_injective_of_covered
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (R : I ⥤ CommRingCat.{u}) (r : Cocone R)
    (hinj : ∀ i, Function.Injective (r.ι.app i))
    (hcover : ∀ z : r.pt, ∃ i a, r.ι.app i a = z) : IsColimit r := by
  let : ReflectsColimit R (forget CommRingCat) :=
    reflectsColimit_of_reflectsIsomorphisms R (forget CommRingCat)
  apply isColimitOfReflects (forget CommRingCat)
  apply Types.FilteredColimit.isColimitOf' (R ⋙ forget CommRingCat)
  · intro z
    obtain ⟨i, a, ha⟩ := hcover z
    exact ⟨i, a, ha.symm⟩
  · intro i a b hab
    exact ⟨i, 𝟙 i, by simpa using hinj i hab⟩

/-- The residue field at a point of an inverse limit with affine transitions is the
colimit of the residue fields of its images. The spectra form a limiting cone, compatible
with the canonical maps into the original schemes. `HEq` identifies the actual canonical
maps despite the equal, but not definitionally equal, image points in their source types.
No arbitrary transition or projection maps are allowed by these identifications.

Source: Stacks Project, Limits, Lemma 0CUG (1)
(blueprint: lem-weil-pbc-limit-residue-field).

Proof:
1. Transport each canonical residue map along the cone identity. Residue-map
   functoriality proves the functor and cocone laws; the transports give the required HEq.
2. Lift a residue element to a stalk element. The inverse images of affine opens of
   stages form a basis (Mathlib `isBasis_preimage_isAffineOpen`), so represent the stalk
   element by a section on such an inverse image.
3. The restricted inverse system consists of affine schemes and is limiting
   (`isLimitOpensCone`). Its global sections form a filtered colimit. Hence the section
   comes from a later stage (`exists_appTop_π_eq_of_isAffine_of_isLimit`), after the
   canonical identifications between sections on an open and global sections of its
   open subscheme. Evaluation naturality sends the residue of this section to the
   original residue element.
4. All cocone maps are injective because their domains are fields. Joint coverage
   and injectivity give a colimit of underlying types (`Types.FilteredColimit.isColimitOf'`).
   The forgetful functor preserves filtered colimits and reflects isomorphisms, so
   it reflects this colimit of rings.
5. Apply the limit-preserving spectrum functor to the opposite colimit cocone.
   Its transition maps are affine because their targets are affine. The canonical
   residue-point compatibility equations are Mathlib's
   `Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField`. -/
theorem exists_isColimit_residueField_of_isLimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) (s : c.pt) :
    ∃ (R : I ⥤ CommRingCat.{u}) (r : Cocone R),
      (∀ i : I, R.obj i = (D.obj (op i)).residueField (c.π.app (op i) s)) ∧
      (∀ (i j : I) (f : i ⟶ j),
        HEq (R.map f) ((D.map f.op).residueFieldMap (c.π.app (op j) s))) ∧
      r.pt = c.pt.residueField s ∧
      (∀ i : I, HEq (r.ι.app i) ((c.π.app (op i)).residueFieldMap s)) ∧
      Nonempty (IsColimit r) ∧
      (∃ t : Cone (R.op ⋙ Scheme.Spec),
        t.pt = Spec (c.pt.residueField s) ∧
        (∀ i : I, HEq (t.π.app (op i))
          (Spec.map ((c.π.app (op i)).residueFieldMap s))) ∧
        Nonempty (IsLimit t) ∧
        ∀ {i j : Iᵒᵖ} (f : i ⟶ j),
          IsAffineHom ((R.op ⋙ Scheme.Spec).map f)) ∧
      (∀ i : I, Spec.map ((c.π.app (op i)).residueFieldMap s) ≫
        (D.obj (op i)).fromSpecResidueField (c.π.app (op i) s) =
          c.pt.fromSpecResidueField s ≫ c.π.app (op i)) ∧
      (∀ (i j : I) (f : i ⟶ j),
        Spec.map ((D.map f.op).residueFieldMap (c.π.app (op j) s)) ≫
          (D.obj (op i)).fromSpecResidueField (D.map f.op (c.π.app (op j) s)) =
        (D.obj (op j)).fromSpecResidueField (c.π.app (op j) s) ≫ D.map f.op) := by
  classical
  let R := residueDiagram D c s
  let r := residueCocone D c s
  have hr : IsColimit r := isColimit_of_injective_of_covered R r
    (fun i ↦ ((c.π.app (op i)).residueFieldMap s).hom.injective)
    (exists_residue_rep D c hc s)
  let t := Scheme.Spec.mapCone r.op
  refine ⟨R, r, (fun _ ↦ rfl), ?_, rfl, (fun _ ↦ HEq.rfl), ⟨hr⟩,
    ⟨t, rfl, (fun _ ↦ HEq.rfl), ⟨isLimitOfPreserves Scheme.Spec hr.op⟩, ?_⟩,
    ?_, ?_⟩
  · intro i j f
    exact pointedResidueMap_heq _ _ _ _
  · intro i j f
    change IsAffineHom (Spec.map (R.map f.unop))
    infer_instance
  · intro i
    exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField _ _
  · intro i j f
    exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField _ _

end AlgebraicGeometry
