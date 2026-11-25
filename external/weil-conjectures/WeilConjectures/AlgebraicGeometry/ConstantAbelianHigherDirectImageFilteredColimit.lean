/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import WeilConjectures.AlgebraicGeometry.Curve.EtaleSheafHLargeFilteredColimit
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageFunctorComparison
import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageEvaluationComparison

/-!
# Filtered continuity for constant abelian higher direct images

Source: Stacks Project, Tags 03Q5, 0739 and 03Q8, and the filtered-union step
of the constant-coefficient reduction in Tag 0F08.
(blueprint: lem-sbc-constant-abelian-higher-image-filtered-colimit)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

private noncomputable def rawFunctor {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℕ) :
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  DerivedCategory.Plus.singleFunctor _ 0 ⋙ shiftFunctor _ (q : ℤ) ⋙
    preadditiveYoneda ⋙
      (Functor.whiskeringLeft _ _ _).obj
        (uliftYoneda.{u + 1} ⋙
          (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
          presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
          upperStar AddCommGrpCat.{u + 1} h ⋙
          DerivedCategory.Plus.singleFunctor _ 0).op

/-- Constant abelian higher direct images commute with filtered colimits whose
index category lies in the coefficient universe.

Source: Stacks Project, Tags 03Q5 and 0739 (filtered cohomology), and Tag 03Q8
(higher direct images as sheafified cohomology presheaves).
(blueprint: lem-sbc-constant-abelian-higher-image-filtered-colimit)

Proof: The constant-sheaf functor is a left adjoint, hence preserves the coefficient
colimit. On an affine etale object U of X, the pullback Y times_X U is qcqs:
quasi-compactness and quasi-separatedness of h are stable under base change.
Pullback of a constant sheaf is the constant sheaf on this pullback scheme.
Filtered cohomology continuity on that qcqs scheme identifies the canonical image
cocone with a colimit cocone. The index remains in Type(u+1); the finite-cover
argument of 0739 applies at this size, as in etaleCohomology_isColimit_large_filtered.
These comparisons commute with restriction in U and with maps of coefficient
groups. Sheafification preserves colimits. Restrict to the affine etale site,
apply these pointwise colimit comparisons, and use the sheafified cohomology
presheaf formula of 03Q8. The affine-site equivalence transports the resulting
colimit back to the small etale site. This proves preservation of the canonical
cocone, not merely an objectwise isomorphism. Degree zero and empty schemes are
included; there is no torsion or finite-generation hypothesis on coefficients. -/
theorem preservesColimitsOfShape_constantAbelianHigherDirectImage
    {X Y : Scheme.{u}} (h : Y ⟶ X) [QuasiCompact h] [QuasiSeparated h]
    (q : ℕ) (I : Type (u + 1)) [SmallCategory I] [IsFiltered I] :
    PreservesColimitsOfShape I
      (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        DerivedCategory.Plus.singleFunctor
          (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
        rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} h ⋙
        DerivedCategory.Plus.homologyFunctor
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ))  := by
  let G := DerivedCategory.Plus.singleFunctor
    (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
      rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} h ⋙
      DerivedCategory.Plus.homologyFunctor _ (q : ℤ)
  let P := rawFunctor h q
  let B := Scheme.AffineEtale.Spec X
  let A := (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj B.op
  let L := presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}
  have : Small.{u + 1} X.AffineEtale := small_self _
  have : LocallySmall.{u + 1} X.AffineEtale := ⟨fun _ _ ↦ small_max.{u + 1} _⟩
  have : EssentiallySmall.{u + 1} X.AffineEtale :=
    essentiallySmall_of_small_of_locallySmall X.AffineEtale
  have : HasSheafify (Scheme.AffineEtale.topology X) AddCommGrpCat.{u + 1} :=
    hasSheafifyEssentiallySmallSite.{u, u + 1, u + 1, u + 2, u + 1} _ _
  let L' := presheafToSheaf (Scheme.AffineEtale.topology X) AddCommGrpCat.{u + 1}
  let T := B.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (Scheme.AffineEtale.topology X) X.smallEtaleTopology
  have : PreservesColimitsOfShape I (P ⋙ A) := by
    apply preservesColimitsOfShape_of_evaluation
    rintro ⟨W⟩
    let U := B.obj W
    let V := pullback U.hom h
    have : IsAffine U.left := by
      dsimp only [U, B]
      rw [Scheme.AffineEtale.Spec_obj_left]
      infer_instance
    have : CompactSpace ((𝟭 Scheme).obj U.left) :=
      inferInstanceAs (CompactSpace U.left)
    have : QuasiSeparatedSpace ((𝟭 Scheme).obj U.left) :=
      inferInstanceAs (QuasiSeparatedSpace U.left)
    have : QuasiCompact (pullback.fst U.hom h) := inferInstance
    have : QuasiSeparated (pullback.fst U.hom h) := inferInstance
    have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace
      (pullback.fst U.hom h)
    have : QuasiSeparatedSpace V := quasiSeparatedSpace_of_quasiSeparated
      (pullback.fst U.hom h)
    let C := DerivedCategory.singleFunctor
      (Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
        cohomology AddCommGrpCat.{u + 1} V (q : ℤ)
    have : PreservesColimitsOfShape I C :=
      ⟨fun {D} ↦ preservesColimit_of_preserves_colimit_cocone (colimit.isColimit D)
        (Scheme.etaleCohomology_isColimit_large_filtered V (colimit.isColimit D) q).some⟩
    have : PreservesColimitsOfShape I
        (upperStar AddCommGrpCat.{u + 1} (pullback.snd U.hom h) ⋙ C) := inferInstance
    obtain ⟨e⟩ := nonempty_abelianHigherDirectImage_evaluationFunctorIso h q U
    exact preservesColimitsOfShape_of_natIso e.symm
  have : PreservesColimitsOfShape I ((P ⋙ A) ⋙ L') := inferInstance
  have : HasLimitsOfSize.{u, u + 1} AddCommGrpCat.{u + 1} := inferInstance
  have : ∀ U : X.Etaleᵒᵖ,
      HasLimitsOfShape (StructuredArrow U B.op) AddCommGrpCat.{u + 1} := fun U ↦
    HasLimitsOfSize.has_limits_of_shape (C := AddCommGrpCat.{u + 1}) (StructuredArrow U B.op)
  have : ∀ (F : X.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (U : X.Etaleᵒᵖ),
      HasLimit (StructuredArrow.proj U B.op ⋙ F) := fun F U ↦
    HasLimitsOfShape.has_limit (StructuredArrow.proj U B.op ⋙ F)
  have : T.IsEquivalence :=
    (B.sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
      (Scheme.AffineEtale.topology X) X.smallEtaleTopology).toEquivalence.isEquivalence_functor
  let ec := Functor.IsDenseSubsite.sheafEquivSheafificationCompatibility
    (Scheme.AffineEtale.topology X) X.smallEtaleTopology B AddCommGrpCat.{u + 1}
  let ec' : (P ⋙ A) ⋙ L' ≅ (P ⋙ L) ⋙ T :=
    Functor.associator P A L' ≪≫ Functor.isoWhiskerLeft P ec ≪≫
      (Functor.associator P L T).symm
  have : PreservesColimitsOfShape I ((P ⋙ L) ⋙ T) :=
    preservesColimitsOfShape_of_natIso ec'
  have : PreservesColimitsOfShape I (P ⋙ L) :=
    preservesColimitsOfShape_of_reflects_of_preserves (P ⋙ L) T
  obtain ⟨e⟩ := nonempty_abelianHigherDirectImage_sheafificationFunctorIso h q
  let e' : P ⋙ L ≅ G := e
  have : PreservesColimitsOfShape I G := preservesColimitsOfShape_of_natIso e'
  exact inferInstanceAs
    (PreservesColimitsOfShape I
      (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙ G))

end AlgebraicGeometry.Etale
