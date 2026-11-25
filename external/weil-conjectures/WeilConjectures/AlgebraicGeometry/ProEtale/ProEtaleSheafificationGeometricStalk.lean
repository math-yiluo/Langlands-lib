/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.Point.OfIsCofiltered
import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-! # Sheafification preserves pro-etale geometric stalks

## References

* Stacks Project, Tags 0F6B, 0F6C, the paragraph before 0993, and 00Y8(3)
* Stacks Project, Tags 0F6B, 0F6C, paragraph before 0993, and 00Y8(3)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private theorem lift_geometricPoint_cover
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {V : X.ProEt} (S : Sieve V) (hS : S ∈ ProEt.topology X V)
    (v : Spec (.of Ω) ⟶ V.left) :
    ∃ (W : X.ProEt) (g : W ⟶ V) (_ : S g) (w : Spec (.of Ω) ⟶ W.left),
      w ≫ g.left = v := by
  obtain ⟨R, hR, hRS⟩ := ProEt.mem_topology_iff.1 hS
  obtain ⟨ι, Z, f, rfl⟩ := R.exists_eq_ofArrows
  have hR' : Presieve.ofArrows (fun i ↦ (Z i).left) (fun i ↦ (f i).left) ∈
      proetalePrecoverage V.left := by
    simpa only [ProEt.mem_precoverage_iff, Presieve.map_ofArrows,
      Functor.comp_obj, Functor.comp_map, ProEt.forget, MorphismProperty.Over.forget,
      MorphismProperty.Comma.forget, Over.forget, Comma.fst] using hR
  have hb := Precoverage.mem_coverings_of_isPullback (fun i ↦ (f i).left) hR' v
    (fun i ↦ pullback.snd (f i).left v) (fun i ↦ pullback.fst (f i).left v)
    (fun i ↦ (IsPullback.of_hasPullback (f i).left v).flip)
  have hb' := propQCPrecoverage_le_precoverage _ hb
  obtain ⟨i, z, hz⟩ :=
    ((ofArrows_mem_precoverage_iff _).1 hb').1 (IsLocalRing.closedPoint Ω)
  have hf : WeaklyEtale (f i).left :=
    ((ofArrows_mem_precoverage_iff _).1 (propQCPrecoverage_le_precoverage _ hR')).2 i
  let := hf
  obtain ⟨σ, hσ⟩ := exists_comp_eq_id_of_weaklyEtale
    (pullback.snd (f i).left v) z
  refine ⟨Z i, f i, hRS _ _ ⟨i⟩, σ ≫ pullback.fst (f i).left v, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hσ, Category.id_comp]

/-- The colimit of the abelian sheafification unit on pointed weakly etale neighbourhoods
is an isomorphism, naturally in the presheaf.
-/
theorem proEtaleGeometricStalk_sheafification
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (P : X.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    IsIso (colim.map (Functor.whiskerLeft (proEtaleGeometricNeighbourhoodForget x).op
      (toSheafify (ProEt.topology X) P))) ∧
    ∀ (Q : X.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (a : P ⟶ Q),
      colim.map (Functor.whiskerLeft (proEtaleGeometricNeighbourhoodForget x).op a) ≫
        colim.map (Functor.whiskerLeft (proEtaleGeometricNeighbourhoodForget x).op
          (toSheafify (ProEt.topology X) Q)) =
      colim.map (Functor.whiskerLeft (proEtaleGeometricNeighbourhoodForget x).op
        (toSheafify (ProEt.topology X) P)) ≫
        colim.map (Functor.whiskerLeft (proEtaleGeometricNeighbourhoodForget x).op
          (sheafifyMap (ProEt.topology X) a)) := by
  let p := proEtaleGeometricNeighbourhoodForget x
  have hp : ∀ ⦃Y : X.ProEt⦄ (R : Sieve Y) (_ : R ∈ ProEt.topology X Y)
      ⦃U : ProEtaleGeometricNeighbourhood x⦄ (f : p.obj U ⟶ Y),
      ∃ (Z : X.ProEt) (g : Z ⟶ Y) (_ : R g)
        (V : ProEtaleGeometricNeighbourhood x) (q : V ⟶ U) (a : p.obj V ⟶ Z),
        a ≫ g = p.map q ≫ f := by
    intro Y R hR U f
    obtain ⟨Z, g, hg, z, hz⟩ := lift_geometricPoint_cover
      (R.pullback f) ((ProEt.topology X).pullback_stable f hR) U.hom.left
    let V : ProEtaleGeometricNeighbourhood x :=
      StructuredArrow.mk (Over.homMk z (by
        change z ≫ Z.hom = x
        rw [← MorphismProperty.Over.w g, ← Category.assoc, hz]
        exact Over.w U.hom))
    let q : V ⟶ U := StructuredArrow.homMk g (by
      apply Over.OverMorphism.ext
      exact hz)
    refine ⟨Z, g ≫ f, hg, V, q, 𝟙 _, ?_⟩
    change 𝟙 Z ≫ (g ≫ f) = g ≫ f
    exact Category.id_comp _
  let Φ : (ProEt.topology X).Point.{u + 1} :=
    GrothendieckTopology.Point.ofIsCofiltered.{u + 1} p hp
  let e (F : X.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
      colimit (p.op ⋙ F) ≅ Φ.presheafFiber.obj F :=
    (colimit.isColimit (p.op ⋙ F)).coconePointUniqueUpToIso
      (GrothendieckTopology.Point.isColimitPresheafFiberOfIsCofilteredCocone.{u + 1}
        p hp F)
  have he (F : X.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1})
      (j : (ProEtaleGeometricNeighbourhood x)ᵒᵖ) :
      colimit.ι (p.op ⋙ F) j ≫ (e F).hom =
        GrothendieckTopology.Point.toPresheafFiberOfIsCofiltered.{u + 1}
          p hp j.unop F :=
    IsColimit.comp_coconePointUniqueUpToIso_hom _ _ j
  have hei (F : X.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1})
      (j : (ProEtaleGeometricNeighbourhood x)ᵒᵖ) :
      GrothendieckTopology.Point.toPresheafFiberOfIsCofiltered.{u + 1}
          p hp j.unop F ≫ (e F).inv =
        colimit.ι (p.op ⋙ F) j :=
    by rw [← he F j, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hmap (F G : X.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (a : F ⟶ G) :
      colim.map (p.op.whiskerLeft a) =
        (e F).hom ≫ Φ.presheafFiber.map a ≫ (e G).inv := by
    apply colimit.hom_ext
    intro j
    rw [colim_map, ι_colimMap, ← Category.assoc, he]
    rw [← Category.assoc,
      GrothendieckTopology.Point.toPresheafFiberOfIsCofiltered_naturality]
    rw [Category.assoc, hei]
    rfl
  refine ⟨?_, ?_⟩
  · change IsIso (colim.map (p.op.whiskerLeft (toSheafify (ProEt.topology X) P)))
    rw [hmap]
    infer_instance
  · intro Q a
    rw [← colim.map_comp, ← colim.map_comp]
    congr 1
    rw [← Functor.whiskerLeft_comp, ← Functor.whiskerLeft_comp, toSheafify_naturality]

end AlgebraicGeometry.Scheme
