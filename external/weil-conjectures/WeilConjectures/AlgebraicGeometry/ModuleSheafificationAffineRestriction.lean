/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-! # Sheafification of module presheaves identified on affine opens

Source: Stacks Project, Tags 009U and 0089, the module basis equivalence and the
universal property of module sheafification
(blueprint: lem-sc-module-sheafification-affine-restriction).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Functor Opposite

namespace AlgebraicGeometry

/-- The affine-open inclusion is cover dense because affine opens form a basis. -/
private theorem affine_cover_dense (Y : Scheme.{u}) :
    (ObjectProperty.ι (fun V : Y.Opens ↦ IsAffineOpen V)).IsCoverDense
      (Opens.grothendieckTopology Y) := by
  apply (TopCat.Opens.coverDense_iff_isBasis _).2
  have hr : Set.range (ObjectProperty.ι (fun V : Y.Opens ↦ IsAffineOpen V)).obj =
      Y.affineOpens := by
    ext U
    constructor
    · rintro ⟨V, rfl⟩
      exact V.property
    · intro h
      exact ⟨⟨U, h⟩, rfl⟩
  rw [hr]
  exact Y.isBasis_affineOpens

/-- Maps into module sheaves extend uniquely from the affine basis. Linearity is local. -/
private theorem affine_module_restriction_bijective (Y : Scheme.{u})
    (M : PresheafOfModules.{u} (moduleRings Y.toRingedSpace).obj)
    (N : SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :
    Function.Bijective (fun f : M ⟶ N.val ↦
      (PresheafOfModules.pushforward₀
        (ObjectProperty.ι (fun V : Y.Opens ↦ IsAffineOpen V))
        (moduleRings Y.toRingedSpace).obj).map f) := by
  let G := ObjectProperty.ι (fun V : Y.Opens ↦ IsAffineOpen V)
  let _ := affine_cover_dense Y
  let E := Functor.IsCoverDense.restrictHomEquivHom
    (G := G) (ℱ := M.presheaf) (ℱ' := (SheafOfModules.toSheaf _).obj N)
  constructor
  · intro f g h
    apply (PresheafOfModules.toPresheaf _).map_injective
    apply E.symm.injective
    ext V x
    change f.app _ x = g.app _ x
    exact congrArg (fun k ↦ k.app V x) h
  · intro f
    let a : M.presheaf ⟶ N.val.presheaf :=
      E ((PresheafOfModules.toPresheaf _).map f)
    have ha : whiskerLeft G.op a = (PresheafOfModules.toPresheaf _).map f :=
      E.left_inv _
    have hal : ∀ (V : (ObjectProperty.FullSubcategory
        (fun V : Y.Opens ↦ IsAffineOpen V))ᵒᵖ)
        (r : (moduleRings Y.toRingedSpace).obj.obj (G.op.obj V))
        (m : M.obj (G.op.obj V)),
        a.app (G.op.obj V) (r • m) = r • (a.app (G.op.obj V) m : N.val.obj (G.op.obj V)) := by
      intro V r m
      have hv := congr_app ha V
      change a.app (G.op.obj V) = _ at hv
      rw [hv]
      exact (f.app V).hom.map_smul r m
    let b : M ⟶ N.val := PresheafOfModules.homMk a (by
      intro X r m
      apply N.isSheaf.isSeparated _ _ (G.is_cover_of_isCoverDense _ X.unop)
      rintro V p ⟨d⟩
      have hloc : N.val.map d.map.op (a.app X (r • m)) =
          N.val.map d.map.op (r • (a.app X m : N.val.obj X)) := by
        have hn := CategoryTheory.congr_fun (a.naturality d.map.op).symm
        change ∀ x, N.val.map d.map.op (a.app X x) =
          a.app (G.op.obj (.op d.obj)) (M.map d.map.op x) at hn
        rw [hn, M.map_smul, hal, N.val.map_smul, hn]
      change N.val.map p.op (a.app X (r • m)) =
        N.val.map p.op (r • (a.app X m : N.val.obj X))
      rw [← d.fac, op_comp, N.val.map_comp]
      exact congrArg (N.val.map d.lift.op) hloc)
    refine ⟨b, ?_⟩
    apply (PresheafOfModules.toPresheaf _).map_injective
    exact ha

set_option backward.isDefEq.respectTransparency false in
/-- A natural identification with a module sheaf on all affine opens extends after
sheafification, naturally in an arbitrary parameter category.
Source: Stacks Project, Tags 009U and 0089
(blueprint: lem-sc-module-sheafification-affine-restriction).

Proof: Affine opens form a basis. For each parameter, extend the given affine-open
maps into the target sheaf to all opens: cover each open by affine opens, apply the
maps to the restrictions of a section, and glue in the target. On overlaps, use
an affine refinement and restriction compatibility; uniqueness proves independence
of the cover. Addition and scalar multiplication hold locally, hence globally.
The resulting module-presheaf map factors uniquely through sheafification. To prove
invertibility, test maps into any module sheaf N: restriction to the affine basis
is bijective for maps from either P or Q into N. Precomposition with the given
basis isomorphism is bijective, so precomposition with the extended map is also
bijective. The sheafification adjunction transfers this bijection to the factored
sheaf morphism. The categorical co-Yoneda criterion makes that morphism an
isomorphism. For a parameter morphism, the two composites agree on every affine
open before factoring; uniqueness of extension and the adjunction prove naturality.
No intersection of affine opens needs to be affine: it is covered by affine opens.
Empty opens use the empty sheaf cover. -/
theorem module_sheafification_iso_of_affine_restriction
    (Y : Scheme.{u}) {C : Type v} [Category.{w} C]
    (P : C ⥤ PresheafOfModules.{u} (moduleRings Y.toRingedSpace).obj)
    (Q : C ⥤ SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    (e : P ⋙ PresheafOfModules.pushforward₀
        (ObjectProperty.ι (fun V : Y.Opens ↦ IsAffineOpen V))
        (moduleRings Y.toRingedSpace).obj ≅
      Q ⋙ SheafOfModules.forget (moduleRings Y.toRingedSpace) ⋙
        PresheafOfModules.pushforward₀
          (ObjectProperty.ι (fun V : Y.Opens ↦ IsAffineOpen V))
          (moduleRings Y.toRingedSpace).obj) :
    Nonempty (P ⋙
      PresheafOfModules.sheafification.{u} (𝟙 (moduleRings Y.toRingedSpace).obj) ≅ Q) := by
  classical
  let R := PresheafOfModules.pushforward₀
    (ObjectProperty.ι (fun V : Y.Opens ↦ IsAffineOpen V))
    (moduleRings Y.toRingedSpace).obj
  let E (M : PresheafOfModules.{u} (moduleRings Y.toRingedSpace).obj)
      (N : SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
    Equiv.ofBijective (fun f : M ⟶ N.val ↦ R.map f)
      (affine_module_restriction_bijective Y M N)
  let a (X : C) : P.obj X ⟶ (Q.obj X).val :=
    (E (P.obj X) (Q.obj X)).symm (e.hom.app X)
  have ha (X : C) : R.map (a X) = e.hom.app X :=
    (E (P.obj X) (Q.obj X)).apply_symm_apply _
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (moduleRings Y.toRingedSpace).obj)
  let f : P ⋙ PresheafOfModules.sheafification
      (𝟙 (moduleRings Y.toRingedSpace).obj) ⟶ Q :=
    { app := fun X ↦ (adj.homEquiv _ _).symm (a X)
      naturality := by
        intro X X' k
        apply (adj.homEquiv _ _).injective
        change adj.homEquiv _ _
          ((PresheafOfModules.sheafification _).map (P.map k) ≫ _) = _
        rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
        simp only [Equiv.apply_symm_apply]
        apply (E (P.obj X) (Q.obj X')).injective
        change R.map (P.map k ≫ a X') = R.map (a X ≫ (Q.map k).val)
        rw [R.map_comp, R.map_comp, ha, ha]
        exact e.hom.naturality k }
  have hf (X : C) : IsIso (f.app X) := by
    apply isIso_of_coyoneda_map_bijective
    intro N
    have hb : Function.Bijective
        (fun h : Q.obj X ⟶ N ↦ a X ≫ h.val) := by
      constructor
      · intro h h' hh
        apply SheafOfModules.hom_ext
        apply (E (Q.obj X).val N).injective
        have hh' := congrArg R.map hh
        rw [R.map_comp, R.map_comp, ha] at hh'
        exact (cancel_epi (e.hom.app X)).1 hh'
      · intro k
        let b := (E (Q.obj X).val N).symm (e.inv.app X ≫ R.map k)
        refine ⟨⟨b⟩, ?_⟩
        apply (E (P.obj X) N).injective
        change R.map (a X ≫ b) = R.map k
        rw [R.map_comp, ha]
        have hb : R.map b = e.inv.app X ≫ R.map k :=
          (E (Q.obj X).val N).apply_symm_apply _
        rw [hb, ← Category.assoc]
        rw [e.hom_inv_id_app]
        change (𝟙 (R.obj (P.obj X))) ≫ R.map k = R.map k
        exact Category.id_comp _
    have he : (fun h : Q.obj X ⟶ N ↦ f.app X ≫ h) =
        fun h ↦ (adj.homEquiv _ _).symm (a X ≫ h.val) := by
      funext h
      apply (adj.homEquiv _ _).injective
      rw [adj.homEquiv_naturality_right]
      change adj.homEquiv _ _ ((adj.homEquiv _ _).symm (a X)) ≫ h.val =
        adj.homEquiv _ _ ((adj.homEquiv _ _).symm (a X ≫ h.val))
      simp only [Equiv.apply_symm_apply]
    rw [he]
    exact (adj.homEquiv _ _).symm.bijective.comp hb
  let _ : IsIso f := (NatTrans.isIso_iff_isIso_app f).mpr hf
  exact ⟨asIso f⟩

end AlgebraicGeometry
