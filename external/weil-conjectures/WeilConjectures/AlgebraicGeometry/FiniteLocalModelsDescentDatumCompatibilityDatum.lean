/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
/-! # Natural transport on a local representative -/

@[expose] public section
universe u
open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme
/-- Natural transport compatible with the local representation, before imposing cocycles.

Source: Stacks Project, Tags 03RV and 02W5.
(blueprint: def-weil-pbc-finite-local-model-compatible-transport)
The fields record transport of arbitrary scheme points, its naturality, and its
identification of equal sections on the small etale site. No data is chosen here. -/
structure FiniteLocalModelCompatibleTransport
    (T : Scheme.{u}) (E : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (U : T.Etale) (Q : U.left.FiniteEtale)
    (e : (E.over U).obj ≅ (Etale.overToEtale U).op ⋙
      uliftYoneda.{u + 1}.obj Q.obj) where
  transport {W : Scheme.{u}} (a b : W ⟶ U.left) (h : a ≫ U.hom = b ≫ U.hom) :
    (Over.mk a ⟶ Over.mk Q.obj.hom) → (Over.mk b ⟶ Over.mk Q.obj.hom)
  naturality {W W' : Scheme.{u}} (g : W' ⟶ W) (a b : W ⟶ U.left)
    (h : a ≫ U.hom = b ≫ U.hom) (x : Over.mk a ⟶ Over.mk Q.obj.hom) :
    transport (g ≫ a) (g ≫ b) (by rw [Category.assoc, Category.assoc, h])
      ((Over.homMk g : Over.mk (g ≫ a) ⟶ Over.mk a) ≫ x) =
      (Over.homMk g : Over.mk (g ≫ b) ⟶ Over.mk b) ≫ transport a b h x
  compatibility :
      ∀ (W : T.Etale) (a b : W ⟶ U) (s : E.obj.obj (op W)),
        (transport a.left b.left
          ((MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm)
          (Over.homMk ((e.hom.app (op (Over.mk a))) s).down.left
            (MorphismProperty.Over.w ((e.hom.app (op (Over.mk a))) s).down))).left =
          ((e.hom.app (op (Over.mk b))) s).down.left

private theorem finiteLocalModels_section_naturality
    (T : Scheme.{u}) (E : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (U : T.Etale) (Q : U.left.FiniteEtale)
    (e : (E.over U).obj ≅ (Etale.overToEtale U).op ⋙
      uliftYoneda.{u + 1}.obj Q.obj)
    (V W : T.Etale) (a : V ⟶ U) (b : W ⟶ U) (g : W ⟶ V)
    (hg : g ≫ a = b) (s : E.obj.obj (op V)) :
    g.left ≫ ((e.hom.app (op (Over.mk a))) s).down.left =
      ((e.hom.app (op (Over.mk b))) (E.obj.map g.op s)).down.left := by
  let k : Over.mk b ⟶ Over.mk a := Over.homMk g hg
  have hn := ConcreteCategory.congr_hom (e.hom.naturality k.op) s
  exact congrArg (fun z ↦ z.down.left) hn.symm

/-- The comparison point on the universal pair consisting of a Q-point and a lift to U.

Source: Stacks Project, Tags 03RV and 02W5, evaluated at the universal Q-point.
(blueprint: def-weil-pbc-finite-local-model-comparison-point)
On R = Q times_T U, turn the projection to Q into a section of E using the
first map to U, then represent that same section using the second map to U. -/
noncomputable def finiteLocalModels_comparison
    (T : Scheme.{u}) (E : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (U : T.Etale) (Q : U.left.FiniteEtale)
    (e : (E.over U).obj ≅ (Etale.overToEtale U).op ⋙
      uliftYoneda.{u + 1}.obj Q.obj) :
    Over.mk (CategoryTheory.Limits.pullback.snd (Q.obj.hom ≫ U.hom) U.hom) ⟶
      Over.mk Q.obj.hom := by
  let R := CategoryTheory.Limits.pullback (Q.obj.hom ≫ U.hom) U.hom
  let p : R ⟶ Q.obj.left := CategoryTheory.Limits.pullback.fst _ _
  let b : R ⟶ U.left := CategoryTheory.Limits.pullback.snd _ _
  let V : T.Etale := Etale.mk (b ≫ U.hom)
  let a' : V ⟶ U := MorphismProperty.Over.homMk (p ≫ Q.obj.hom)
    (by
      change (p ≫ Q.obj.hom) ≫ U.hom = b ≫ U.hom
      simpa [p, b, Category.assoc] using
        (CategoryTheory.Limits.pullback.condition (f := Q.obj.hom ≫ U.hom)
          (g := U.hom)))
  let b' : V ⟶ U := MorphismProperty.Over.homMk b rfl
  let z : ((Etale.overToEtale U).op ⋙ uliftYoneda.{u + 1}.obj Q.obj).obj
      (op (Over.mk a')) := ULift.up (MorphismProperty.Over.homMk p rfl)
  let s := e.inv.app (op (Over.mk a')) z
  exact Over.homMk ((e.hom.app (op (Over.mk b'))) s).down.left
    (MorphismProperty.Over.w ((e.hom.app (op (Over.mk b'))) s).down)

/-- Transport by pulling back the fixed comparison morphism, with no witness choice.

Source: Stacks Project, Tags 03RV and 02W5.
(blueprint: def-weil-pbc-finite-local-model-canonical-transport)
For x above a and a second lift b, the pair (x,b) maps to Q times_T U.
Compose this map with the comparison point. The projection equation makes
this a Q-point above b. -/
noncomputable def finiteLocalModels_transport
    (T : Scheme.{u}) (E : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (U : T.Etale) (Q : U.left.FiniteEtale)
    (e : (E.over U).obj ≅ (Etale.overToEtale U).op ⋙
      uliftYoneda.{u + 1}.obj Q.obj)
    {W : Scheme.{u}} (a b : W ⟶ U.left) (h : a ≫ U.hom = b ≫ U.hom)
    (x : Over.mk a ⟶ Over.mk Q.obj.hom) : Over.mk b ⟶ Over.mk Q.obj.hom := by
  let l : W ⟶ CategoryTheory.Limits.pullback (Q.obj.hom ≫ U.hom) U.hom :=
    CategoryTheory.Limits.pullback.lift x.left b
    (by
      have hx : x.left ≫ Q.obj.hom = a := Over.w x
      rw [← Category.assoc, hx, h])
  refine Over.homMk (l ≫ (finiteLocalModels_comparison T E U Q e).left) ?_
  rw [Category.assoc, Over.w]
  change l ≫ CategoryTheory.Limits.pullback.snd _ _ = b
  exact CategoryTheory.Limits.pullback.lift_snd _ _ _

/--
Source: Stacks Project, Tags 03RV and 02W5.
(blueprint: finite-local-models-transport-exists)
The fiber-product Yoneda comparison of the two pullbacks of the finite etale
scheme defines transport for arbitrary scheme maps with equal composites.
Pulling this comparison back along the pair of maps gives the displayed map.
-/
theorem finiteLocalModels_transport_exists
    (T : Scheme.{u}) (E : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (U : T.Etale) (Q : U.left.FiniteEtale)
    (e : (E.over U).obj ≅ (Etale.overToEtale U).op ⋙
      uliftYoneda.{u + 1}.obj Q.obj) :
    Nonempty (∀ {W : Scheme.{u}} (a b : W ⟶ U.left),
      a ≫ U.hom = b ≫ U.hom →
      (Over.mk a ⟶ Over.mk Q.obj.hom) →
      (Over.mk b ⟶ Over.mk Q.obj.hom)) := by
  exact ⟨finiteLocalModels_transport T E U Q e⟩

/--
Source: Stacks Project, Tags 03RV and 02W5.
(blueprint: finite-local-models-transport-naturality)
The transport is induced by pullback of the comparison on the fiber product.
Functoriality of pullback, together with associativity of composition, proves
the displayed naturality equation.
-/
theorem finiteLocalModels_transport_naturality
    (T : Scheme.{u}) (E : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (U : T.Etale) (Q : U.left.FiniteEtale)
    (e : (E.over U).obj ≅ (Etale.overToEtale U).op ⋙
      uliftYoneda.{u + 1}.obj Q.obj) :
    ∀ {W W' : Scheme.{u}} (g : W' ⟶ W) (a b : W ⟶ U.left)
      (h : a ≫ U.hom = b ≫ U.hom) (x : Over.mk a ⟶ Over.mk Q.obj.hom),
      finiteLocalModels_transport T E U Q e (g ≫ a) (g ≫ b)
        (by rw [Category.assoc, Category.assoc, h])
        ((Over.homMk g : Over.mk (g ≫ a) ⟶ Over.mk a) ≫ x) =
      (Over.homMk g : Over.mk (g ≫ b) ⟶ Over.mk b) ≫
        finiteLocalModels_transport T E U Q e a b h x := by
  intro W W' g a b h x
  apply Over.OverMorphism.ext
  simp only [finiteLocalModels_transport, Over.homMk_left, Over.comp_left]
  simp only [← Category.assoc]
  congr 1
  apply CategoryTheory.Limits.pullback.hom_ext <;>
    simp [Category.assoc]

/--
Source: Stacks Project, Tags 03RV and 02W5.
(blueprint: finite-local-models-transport-compatibility)
For an etale source, the comparison identifies the two points obtained from a
common section under the representing isomorphism, yielding compatibility.
-/
theorem finiteLocalModels_transport_compatibility
    (T : Scheme.{u}) (E : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (U : T.Etale) (Q : U.left.FiniteEtale)
    (e : (E.over U).obj ≅ (Etale.overToEtale U).op ⋙
      uliftYoneda.{u + 1}.obj Q.obj) :
    ∀ (W : T.Etale) (a b : W ⟶ U) (s : E.obj.obj (op W)),
      (finiteLocalModels_transport T E U Q e a.left b.left
        ((MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm)
        (Over.homMk ((e.hom.app (op (Over.mk a))) s).down.left
          (MorphismProperty.Over.w ((e.hom.app (op (Over.mk a))) s).down))).left =
      ((e.hom.app (op (Over.mk b))) s).down.left := by
  intro W a b s
  let R := CategoryTheory.Limits.pullback (Q.obj.hom ≫ U.hom) U.hom
  let p : R ⟶ Q.obj.left := CategoryTheory.Limits.pullback.fst _ _
  let q : R ⟶ U.left := CategoryTheory.Limits.pullback.snd _ _
  let V : T.Etale := Etale.mk (q ≫ U.hom)
  let a' : V ⟶ U := MorphismProperty.Over.homMk (p ≫ Q.obj.hom) (by
    change (p ≫ Q.obj.hom) ≫ U.hom = q ≫ U.hom
    simpa [p, q, Category.assoc] using
      (CategoryTheory.Limits.pullback.condition (f := Q.obj.hom ≫ U.hom)
        (g := U.hom)))
  let b' : V ⟶ U := MorphismProperty.Over.homMk q rfl
  let z : ((Etale.overToEtale U).op ⋙ uliftYoneda.{u + 1}.obj Q.obj).obj
      (op (Over.mk a')) := ULift.up (MorphismProperty.Over.homMk p rfl)
  let sV := e.inv.app (op (Over.mk a')) z
  let x := ((e.hom.app (op (Over.mk a))) s).down
  have hx : x.left ≫ Q.obj.hom = a.left := MorphismProperty.Over.w x
  let l : W.left ⟶ R := CategoryTheory.Limits.pullback.lift x.left b.left (by
    rw [← Category.assoc, hx]
    exact (MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm)
  let g : W ⟶ V := MorphismProperty.Over.homMk l (by
    change l ≫ q ≫ U.hom = W.hom
    rw [← Category.assoc]
    simp only [l, q, CategoryTheory.Limits.pullback.lift_snd]
    exact MorphismProperty.Over.w b)
  have hga : g ≫ a' = a := by
    apply MorphismProperty.Over.Hom.ext
    change l ≫ (p ≫ Q.obj.hom) = a.left
    rw [← Category.assoc]
    simpa [l, p] using hx
  have hgb : g ≫ b' = b := by
    apply MorphismProperty.Over.Hom.ext
    exact CategoryTheory.Limits.pullback.lift_snd _ _ _
  have hsV : e.hom.app (op (Over.mk a')) sV = z :=
    ConcreteCategory.congr_hom (e.inv_hom_id_app (op (Over.mk a'))) z
  have hs : E.obj.map g.op sV = s := by
    apply (ConcreteCategory.bijective_of_isIso (e.hom.app (op (Over.mk a)))).1
    apply ULift.ext
    apply MorphismProperty.Over.Hom.ext
    have hn := finiteLocalModels_section_naturality T E U Q e V W a' a g hga sV
    rw [hsV] at hn
    simpa [g, z, l, p, x] using hn.symm
  have hn := finiteLocalModels_section_naturality T E U Q e V W b' b g hgb sV
  rw [hs] at hn
  change l ≫ ((e.hom.app (op (Over.mk b'))) sV).down.left =
    ((e.hom.app (op (Over.mk b))) s).down.left at hn
  exact hn

/-- (blueprint: lem-weil-pbc-finite-local-model-compatible-transport-datum) -/
theorem finiteLocalModels_descentDatum_compatibility_datum
    (T : Scheme.{u}) (E : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (U : T.Etale) (Q : U.left.FiniteEtale)
    (e : (E.over U).obj ≅ (Etale.overToEtale U).op ⋙
      uliftYoneda.{u + 1}.obj Q.obj) :
    Nonempty (FiniteLocalModelCompatibleTransport T E U Q e) := by
  refine ⟨{
    transport := finiteLocalModels_transport T E U Q e
    naturality := finiteLocalModels_transport_naturality T E U Q e
    compatibility := finiteLocalModels_transport_compatibility T E U Q e
  }⟩
end AlgebraicGeometry.Scheme
