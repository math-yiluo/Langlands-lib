/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleRootsOfUnity
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import WeilConjectures.Mathlib.Algebra.Category.Grp.Adjunctions
/-!
# Comparison for units on the pro-etale site

Source: Stacks Project, Tags 0GLZ and 01ZC.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
private def units_isColimit {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c) :
    IsColimit ((CommRingCat.unitsAddCommGrp ⋙ forget AddCommGrpCat).mapCocone c) := by
  let hR := isColimitOfPreserves (forget CommRingCat) hc
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    change Additive c.ptˣ at x
    obtain ⟨i, a, ha⟩ := Types.jointly_surjective_of_isColimit hR x.toMul.val
    obtain ⟨j, b, hb⟩ := Types.jointly_surjective_of_isColimit hR (↑(x.toMul⁻¹) : c.pt)
    change c.ι.app i a = _ at ha
    change c.ι.app j b = _ at hb
    let k := IsFiltered.max i j
    let a' := (F.map (IsFiltered.leftToMax i j)) a
    let b' := (F.map (IsFiltered.rightToMax i j)) b
    have ha' : c.ι.app k a' = x.toMul.val := by
      exact (congrArg (fun h : F.obj i ⟶ c.pt ↦ h a)
        (c.w (IsFiltered.leftToMax i j))).trans ha
    have hb' : c.ι.app k b' = (↑(x.toMul⁻¹) : c.pt) := by
      exact (congrArg (fun h : F.obj j ⟶ c.pt ↦ h b)
        (c.w (IsFiltered.rightToMax i j))).trans hb
    have he : c.ι.app k (a' * b') = c.ι.app k 1 := by
      rw [map_mul, ha', hb', map_one]
      exact x.toMul.val_inv
    obtain ⟨l, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff' hR (a' * b') 1).1 he
    have hf' : F.map f a' * F.map f b' = 1 := by
      change F.map f (a' * b') = F.map f 1 at hf
      simpa only [map_mul, map_one] using hf
    let y : (F.obj l)ˣ := ⟨F.map f a', F.map f b', hf', by rwa [mul_comm]⟩
    refine ⟨l, Additive.ofMul y, ?_⟩
    apply Additive.toMul.injective
    apply Units.ext
    change x.toMul.val = c.ι.app l (F.map f a')
    exact ha'.symm.trans
      (congrArg (fun h : F.obj k ⟶ c.pt ↦ h a') (c.w f)).symm
  · intro i x y h
    change Additive (F.obj i)ˣ at x y
    have hxy : c.ι.app i x.toMul.val = c.ι.app i y.toMul.val :=
      congrArg (fun z ↦ z.toMul.val) h
    obtain ⟨j, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff' hR _ _).1 hxy
    refine ⟨j, f, ?_⟩
    apply Additive.toMul.injective
    apply Units.ext
    exact hf

private instance units_preservesFilteredColimits :
    PreservesFilteredColimitsOfSize.{u, u} CommRingCat.unitsAddCommGrp.{u} where
  preserves_filtered_colimits J _ _ := by
    constructor
    intro F
    let : ReflectsColimitsOfShape J (forget AddCommGrpCat.{u}) :=
      reflectsColimitsOfShape_of_reflectsIsomorphisms
    have h := units_isColimit F (colimit.cocone F) (colimit.isColimit F)
    have h' : IsColimit (CommRingCat.unitsAddCommGrp.mapCocone (colimit.cocone F)) :=
      isColimitOfReflects (forget AddCommGrpCat) h
    exact preservesColimit_of_preserves_colimit_cocone (colimit.isColimit F) h'

open AlgebraicGeometry Opposite
namespace AlgebraicGeometry.ProEtale
private def affineUnitsIsColimit {J : Type u} [SmallCategory J]
    [IsCofiltered J] (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j, IsAffine (D.obj j)] :
    IsColimit ((Scheme.Γ ⋙ CommRingCat.unitsAddCommGrpULift.{u + 1, u}).mapCocone c.op) := by
  have hΓ := (nonempty_isColimit_Γ_mapCocone D c hc).some
  exact isColimitOfPreserves CommRingCat.unitsAddCommGrpULift hΓ

private theorem isIso_app_of_colimits {C B J : Type*} [Category* C] [Category* B]
    [Category* J] {P Q : Cᵒᵖ ⥤ B} (a : P ⟶ Q) {K : J ⥤ C} (c : Cone K)
    (hP : IsColimit (P.mapCocone c.op)) (hQ : IsColimit (Q.mapCocone c.op))
    [∀ i, IsIso (a.app (op (K.obj i)))] : IsIso (a.app (op c.pt)) := by
  let e : K.op ⋙ P ≅ K.op ⋙ Q := NatIso.ofComponents
    (fun i ↦ asIso (a.app (op (K.obj i.unop))))
    (fun f ↦ a.naturality (K.map f.unop).op)
  let h := (IsColimit.precomposeHomEquiv e (Q.mapCocone c.op)).2 hQ
  have heq : a.app (op c.pt) = (hP.coconePointUniqueUpToIso h).hom := by
    apply hP.hom_ext
    intro i
    change P.map (c.π.app i.unop).op ≫ a.app (op c.pt) = _
    simp only [IsColimit.comp_coconePointUniqueUpToIso_hom]
    exact a.naturality (c.π.app i.unop).op
  rw [heq]
  infer_instance

/-- The comparison counit for full units is invertible.
Source: Stacks Project, Tags 0GLZ and 01ZC
(auxiliary; not a blueprint node).
Proof: on an affine pro-etale presentation, comparison sections are the filtered
colimit of etale sections. Units commute with filtered colimits of rings: descend
a unit and its inverse, then descend their product equation. Global sections
turn cofiltered limits of affine schemes into filtered colimits of rings. The
counit is already invertible on etale objects by full faithfulness. Naturality
and uniqueness of colimits prove invertibility on each affine pro-etale object;
the affine dense subsite detects isomorphisms of sheaves. -/
theorem proEtaleUnitsCounit_isIso (Z : Scheme.{u}) :
    IsIso ((comparisonAdjunction AddCommGrpCat.{u + 1} Z).counit.app
      (Scheme.ProEt.gmSheaf Z)) := by
  let A := AddCommGrpCat.{u + 1}
  let G := Scheme.ProEt.gmSheaf Z
  have := isIso_comparisonAdjunction_unit A Z
  let a := ((comparisonAdjunction A Z).counit.app G).hom
  apply isIso_of_isIso_app_affineProEt A
  intro U
  obtain ⟨J, _, _, ⟨p⟩⟩ := U.exists_relativeLimitPresentation
  let K := presentationDiagram p
  let c := presentationCone p
  have hc := isLimitPresentationCone p
  obtain ⟨hP⟩ := isColimit_comparisonUpperStar_mapCocone_of_isAffine A
    ((comparisonLowerStar A Z).obj G) K c hc
  let D := (K ⋙ Scheme.toProEt Z) ⋙ Scheme.ProEt.forget Z ⋙ Over.forget Z
  have hAff (j : J) : IsAffine (D.obj j) := by
    exact inferInstanceAs (IsAffine (K.obj j).left)
  have hQ : IsColimit (G.obj.mapCocone c.op) := by
    exact affineUnitsIsColimit D ((Scheme.ProEt.forget Z ⋙ Over.forget Z).mapCone c) hc
  have hr : IsIso ((comparisonLowerStar A Z).map
      ((comparisonAdjunction A Z).counit.app G)) := inferInstance
  have ha (j : J) : IsIso (a.app (op ((K ⋙ Scheme.toProEt Z).obj j))) := by
    exact NatIso.isIso_app_of_isIso
      (((comparisonLowerStar A Z).map ((comparisonAdjunction A Z).counit.app G)).hom)
        (op (K.obj j))
  exact isIso_app_of_colimits a c hP hQ
end AlgebraicGeometry.ProEtale
