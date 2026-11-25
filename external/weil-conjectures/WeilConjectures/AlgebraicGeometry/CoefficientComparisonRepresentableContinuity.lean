/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ClassicalContinuityMap
public import WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleClassicalSheavesImage

/-! # Continuity of etale representables at affine presentations

Source: Stacks Project, proetale.tex, Lemmas describe-pullback-from-etale and
limit-pullback (Tag 099S).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

private noncomputable def pullbackEtaleRepresentableIso (X : Scheme.{u}) (V : X.Etale) :
    (Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt X)
      (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X)).obj
        (X.smallEtaleTopology.uliftYoneda.{u + 1}.obj V) ≅
      (Scheme.ProEt.topology X).uliftYoneda.{u + 1}.obj ((Scheme.toProEt X).obj V) := by
  let A := Scheme.proEtaleSiteComparison X
  let L := Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt X)
    (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X)
  let Y := X.smallEtaleTopology.uliftYoneda.{u + 1}.obj V
  let Z := (Scheme.ProEt.topology X).uliftYoneda.{u + 1}.obj ((Scheme.toProEt X).obj V)
  let e (G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) :
      (L.obj Y ⟶ G) ≃ (Z ⟶ G) :=
    ((A.homEquiv Y G).trans X.smallEtaleTopology.uliftYonedaEquiv.{u + 1}).trans
      (Scheme.ProEt.topology X).uliftYonedaEquiv.{u + 1}.symm
  refine Coyoneda.ext _ _ (fun f ↦ e _ f) (fun f ↦ (e _).symm f)
    (fun f ↦ (e _).symm_apply_apply f) (fun f ↦ (e _).apply_symm_apply f) ?_
  intro G G' f g
  let R := (Scheme.toProEt X).sheafPushforwardContinuous (Type (u + 1))
    X.smallEtaleTopology (Scheme.ProEt.topology X)
  change (A.homEquiv Y G').symm
      (X.smallEtaleTopology.uliftYonedaEquiv.{u + 1}.symm
        ((Scheme.ProEt.topology X).uliftYonedaEquiv.{u + 1} (f ≫ g))) =
    (A.homEquiv Y G).symm
      (X.smallEtaleTopology.uliftYonedaEquiv.{u + 1}.symm
        ((Scheme.ProEt.topology X).uliftYonedaEquiv.{u + 1} f)) ≫ g
  have h : X.smallEtaleTopology.uliftYonedaEquiv.{u + 1}.symm
        ((Scheme.ProEt.topology X).uliftYonedaEquiv.{u + 1} (f ≫ g)) =
      X.smallEtaleTopology.uliftYonedaEquiv.{u + 1}.symm
        ((Scheme.ProEt.topology X).uliftYonedaEquiv.{u + 1} f) ≫ R.map g := by
    calc
      _ = X.smallEtaleTopology.uliftYonedaEquiv.{u + 1}.symm
          (g.hom.app _ ((Scheme.ProEt.topology X).uliftYonedaEquiv.{u + 1} f)) :=
        congrArg X.smallEtaleTopology.uliftYonedaEquiv.{u + 1}.symm
          ((Scheme.ProEt.topology X).uliftYonedaEquiv_comp f g)
      _ = _ := (X.smallEtaleTopology.uliftYonedaEquiv_symm_naturality_right
        V (R.map g) _).symm
  exact (congrArg (A.homEquiv Y G').symm h).trans
    (A.homEquiv_naturality_right_symm _ g)

/-- Maps from an affine presentation to an etale object commute with its limit.

Source: Stacks Project, proetale.tex, lemma-limit-pullback (Tag 099S), using
Limits, Proposition 32.6.1 (locally finite presentation)
(auxiliary; not a blueprint node).

Proof: the sheaf-valued Yoneda lemma and the comparison adjunction identify the
inverse image of an etale representable with the corresponding pro-etale
representable. The essential-image characterization of classical sheaves then
makes its continuity map bijective for the original index category of size u+1.
Consequently the restriction cocone for the universe-lifted representable is a
colimit. Its joint surjectivity and eventual-equality criterion transfer to the
coefficient-sized hom sets by taking the underlying arrows of the two ULifts.
This proves that the coyoneda image of the opposite presentation cone is a
colimit. The original cone is limiting by reflection through the fully faithful
forgetful functor; AsSmall.up preserves that limit. Preservation of this one
colimit cocone gives the claimed PreservesColimit instance. No shrinking of the
index category or identification of the independent coefficient universe is
needed. -/
theorem coefficientComparison_representable_preservesColimit (X : Scheme.{u})
    {I : Type (u + 1)} [SmallCategory I] [IsCofiltered I]
    (P : AffinePresentation X I)
    (V : (Scheme.smallModelComparisonEtaleSite.{u, v} X)ᵒᵖ) :
    PreservesColimit (P.diagram ⋙ AsSmall.up).op
      (coyoneda.obj (op ((Scheme.smallModelComparisonInclusion.{u, v} X).op.obj V))) := by
  let V₀ := (AsSmall.down : Scheme.smallModelComparisonEtaleSite.{u, v} X ⥤ X.Etale).obj V.unop
  let T := (Scheme.toProEt X).obj V₀
  let G := (Scheme.ProEt.topology X).uliftYoneda.{u + 1}.obj T
  have hG : IsClassical G := (Scheme.proEtaleClassicalSheavesImage X G).1.mp
    ⟨X.smallEtaleTopology.uliftYoneda.{u + 1}.obj V₀,
      ⟨(pullbackEtaleRepresentableIso X V₀).symm⟩⟩
  have : IsIso (continuityMap P G.obj) :=
    (CategoryTheory.isIso_iff_bijective _).mpr (hG P)
  have hcG : IsColimit (sectionCocone P G.obj) := by
    have : IsIso ((colimit.isColimit (sectionDiagram P G.obj)).desc
        (sectionCocone P G.obj)) := by
      change IsIso (continuityMap P G.obj)
      infer_instance
    exact (colimit.isColimit (sectionDiagram P G.obj)).ofPointIso
  let c' := (AsSmall.up : X.ProEt ⥤
    Scheme.coefficientProEtaleSiteModel.{u, v} X).mapCone P.cone
  have : (AsSmall.up : X.ProEt ⥤
      Scheme.coefficientProEtaleSiteModel.{u, v} X).IsRightAdjoint :=
    (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt)).symm.isRightAdjoint_inverse
  have hc' : IsLimit c' := isLimitOfPreserves _
    (isLimitOfReflects (Scheme.ProEt.forget X) P.isLimit)
  apply preservesColimit_of_preserves_colimit_cocone hc'.op
  apply Types.FilteredColimit.isColimitOf'
  · intro a
    obtain ⟨i, b, hb⟩ := Types.jointly_surjective_of_isColimit hcG
      (ULift.up a.unop.down)
    refine ⟨i, (AsSmall.up.map b.down).op, ?_⟩
    apply Quiver.Hom.unop_inj
    apply ULift.ext
    exact (congrArg ULift.down hb).symm
  · intro i a b hab
    have hab' : (sectionCocone P G.obj).ι.app i (ULift.up a.unop.down) =
        (sectionCocone P G.obj).ι.app i (ULift.up b.unop.down) := by
      apply ULift.ext
      exact congrArg (fun f ↦ f.unop.down) hab
    obtain ⟨k, f, hf⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff' hcG
        (ULift.up a.unop.down) (ULift.up b.unop.down)).mp hab'
    refine ⟨k, f, ?_⟩
    apply Quiver.Hom.unop_inj
    apply ULift.ext
    change P.diagram.map f.unop ≫ a.unop.down = P.diagram.map f.unop ≫ b.unop.down
    exact congrArg ULift.down hf

end AlgebraicGeometry.ProEtale
