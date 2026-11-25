/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedCoefficientComplexDiagram

/-! # The ordinary coefficient-inclusion map as an adjunction mate -/

@[expose] public section
universe u v
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory.Mod
open MonoidalCategory
variable {A : Type u} [Category.{v} A] [MonoidalCategory A] [BraidedCategory A]
  [HasCoequalizers A] [∀ Y : A, PreservesColimitsOfSize.{0, 0} (tensorLeft Y)]
  [∀ Y : A, PreservesColimitsOfSize.{0, 0} (tensorRight Y)]
  {R S T : A} [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S] [MonObj T]

omit [IsCommMonObj S] in
private lemma scalarAdj_unit (f : R ⟶ S) [IsMonHom f] (M : Mod A R) :
    (extendRestrictAdjunction f).unit.app M = extendUnit f M := by
  change extendUnit f M ≫ (comap f).map (𝟙 _) = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

private lemma scalar_trans_unit (f : R ⟶ S) [IsMonHom f] (a : S ⟶ T) [IsMonHom a]
    (g : R ⟶ T) [IsMonHom g] (h : f ≫ a = g) (M : Mod A R) :
    (extendUnit f M).hom ≫ (extendUnit a ((extendScalars f).obj M)).hom ≫
      ((((extendScalarsComp f a).symm ≪≫ extendScalarsIsoOfEq h).hom.app M).hom) =
    (extendUnit g M).hom := by
  have hp := congrArg Hom.hom
    (Adjunction.unit_leftAdjointUniq_hom_app (extendRestrictAdjunction (f ≫ a))
      (((extendRestrictAdjunction f).comp (extendRestrictAdjunction a)).ofNatIsoRight
        (comapComp f a).symm) M)
  have hq := congrArg Hom.hom
    (Adjunction.unit_leftAdjointUniq_hom_app (extendRestrictAdjunction (f ≫ a))
      ((extendRestrictAdjunction g).ofNatIsoRight (comapCongr h).symm) M)
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    CategoryTheory.Functor.whiskerLeft_app, Iso.symm_hom, Adjunction.comp_unit_app,
    scalarAdj_unit, comp_hom', comap_map_hom, comapComp_inv_app_hom,
    ] at hp
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    CategoryTheory.Functor.whiskerLeft_app, Iso.symm_hom, scalarAdj_unit,
    comp_hom', comap_map_hom, comapCongr, isoMk, Iso.refl_hom] at hq
  change (extendUnit (f ≫ a) M).hom ≫ ((extendScalarsComp f a).hom.app M).hom =
    ((extendUnit f M).hom ≫ (extendUnit a ((extendScalars f).obj M)).hom) ≫ 𝟙 _ at hp
  change (extendUnit (f ≫ a) M).hom ≫ ((extendScalarsIsoOfEq h).hom.app M).hom =
    (extendUnit g M).hom ≫ 𝟙 _ at hq
  rw [Category.comp_id] at hp hq
  rw [← Category.assoc, ← hp]
  have hc := congrArg Hom.hom ((extendScalarsComp f a).hom_inv_id_app M)
  simp only [comp_hom', id_hom'] at hc
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, comp_hom', Category.assoc]
  rw [reassoc_of% hc]
  exact hq

private lemma scalar_mixed_mate
    {B : A} [MonObj B] [IsCommMonObj B]
    (f : R ⟶ S) [IsMonHom f] (a : S ⟶ T) [IsMonHom a]
    (g : R ⟶ T) [IsMonHom g] (e : B ⟶ S) [IsMonHom e]
    (e' : B ⟶ T) [IsMonHom e'] (hf : f ≫ a = g) (he : e ≫ a = e')
    (te : extendScalars e ⋙ extendScalars a ≅ extendScalars e')
    (tf : extendScalars f ⋙ extendScalars a ≅ extendScalars g)
    (M : Mod A R)
    (hue : (extendUnit e ((comap e).obj ((extendScalars f).obj M))).hom ≫
      (extendUnit a ((extendScalars e).obj ((comap e).obj ((extendScalars f).obj M)))).hom ≫
      (te.hom.app ((comap e).obj ((extendScalars f).obj M))).hom =
        (extendUnit e' ((comap e).obj ((extendScalars f).obj M))).hom)
    (huf : (extendUnit f M).hom ≫ (extendUnit a ((extendScalars f).obj M)).hom ≫
      (tf.hom.app M).hom = (extendUnit g M).hom) :
    (extendRestrictAdjunction e').homEquiv _ _
      (te.inv.app ((comap e).obj ((extendScalars f).obj M)) ≫
        (extendScalars a).map
          ((extendRestrictAdjunction e).counit.app ((extendScalars f).obj M)) ≫
        tf.hom.app M) = mixedScalarMap f g e e' a hf he M := by
  let N := (extendScalars f).obj M
  let P := (comap e).obj N
  let ε := (extendRestrictAdjunction e).counit.app N
  have hte := congrArg Hom.hom (te.hom_inv_id_app P)
  have htei := congrArg Hom.hom (te.inv_hom_id_app P)
  simp only [comp_hom', id_hom'] at hte htei
  have hu : (extendUnit e' P).hom ≫ (te.inv.app P).hom =
      (extendUnit e P).hom ≫ (extendUnit a ((extendScalars e).obj P)).hom := by
    apply (cancel_mono (te.hom.app P).hom).mp
    simp only [Category.assoc, htei]
    erw [Category.comp_id]
    exact hue.symm
  have hn := congrArg Hom.hom ((extendRestrictAdjunction a).unit.naturality ε)
  simp only [CategoryTheory.Functor.id_map, CategoryTheory.Functor.comp_map,
    scalarAdj_unit, comp_hom', comap_map_hom] at hn
  have ht := congrArg Hom.hom ((extendRestrictAdjunction e).right_triangle_components N)
  simp only [scalarAdj_unit, comp_hom', comap_map_hom, id_hom'] at ht
  let x : N ⟶ (comap a).obj ((extendScalars g).obj M) :=
    extendUnit a N ≫ (comap a).map (tf.hom.app M)
  have hx : x.hom = (mixedScalarMap f g e e' a hf he M).hom := by
    dsimp only [mixedScalarMap, Hom.mk']
    apply congrArg Hom.hom
    apply (extendHomEquiv f M _).injective
    apply hom_ext
    change (extendUnit f M).hom ≫ x.hom =
      (extendUnit f M).hom ≫ (extendHom f _).hom
    rw [extendUnit_hom, extendUnitHom_extendHom]
    change (extendUnit f M).hom ≫
      ((extendUnit a N).hom ≫ (tf.hom.app M).hom) = (extendUnit g M).hom
    exact huf
  apply hom_ext
  simp only [Adjunction.homEquiv_unit, scalarAdj_unit, comp_hom', comap_map_hom]
  change (extendUnit e' P).hom ≫ ((te.inv.app P).hom ≫
      ((extendScalars a).map ε).hom ≫ (tf.hom.app M).hom) = _
  rw [← Category.assoc, hu]
  simp only [Category.assoc]
  rw [← reassoc_of% hn, ← Category.assoc, ht, Category.id_comp]
  exact hx

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale
open Scheme PadicAlgCl

/-- Ordinary tensor transitivity transposes to the explicit coefficient inclusion.

Source: `Mod.extendScalarsComp`, `Mod.extendScalarsIsoOfEq`, and the Hom paragraph
of archived `ModuleObject/Colimit/TwoColimit.lean`.
(auxiliary; not a blueprint node)

Proof: uniqueness of left adjoints defines both tensor transitivity comparisons.
Their unit equations say that the successive units for E→G→Ω, followed by the
comparison, give the unit for E→Ω; the same holds for F. Expand the outer mate
using its unit, use the first equation and naturality of the G→Ω unit, and cancel
the E→G unit against its counit by the triangle identity. The resulting map is
that G→Ω unit followed by the F tensor comparison. Its composite with the F→G
unit is exactly the F→Ω unit by the second equation. The extension adjunction's
universal property identifies it with the morphism used in mixedScalarMap.
Apply this calculation in each degree of C; complex morphisms are determined
by their components. No exactness, boundedness, or filtered diagram is needed. -/
theorem coefficientComplexToAlgCl_underived_compatibility
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    {E F G : FiniteIntermediateField ℓ} (he : E ≤ G) (hf : F ≤ G)
    (C : CochainComplex
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)) ℤ) :
    coefficientComplexTransposedMap X ℓ he hf C = coefficientComplexToAlgCl X ℓ he hf C := by
  apply HomologicalComplex.hom_ext
  intro n
  exact Mod.scalar_mixed_mate
    (padicSubfieldRingObjMap X ℓ hf) (padicSubfieldRingObjToPadicAlgCl X ℓ G)
    (padicSubfieldRingObjToPadicAlgCl X ℓ F) (padicSubfieldRingObjMap X ℓ he)
    (padicSubfieldRingObjToPadicAlgCl X ℓ E)
    (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ hf)
    (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ he)
    ((Mod.extendScalarsComp (padicSubfieldRingObjMap X ℓ he)
      (padicSubfieldRingObjToPadicAlgCl X ℓ G)).symm ≪≫
      Mod.extendScalarsIsoOfEq (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ he))
    ((Mod.extendScalarsComp (padicSubfieldRingObjMap X ℓ hf)
      (padicSubfieldRingObjToPadicAlgCl X ℓ G)).symm ≪≫
      Mod.extendScalarsIsoOfEq (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ hf))
    (C.X n)
    (Mod.scalar_trans_unit _ _ _ _ _) (Mod.scalar_trans_unit _ _ _ _ _)

end AlgebraicGeometry.ProEtale
