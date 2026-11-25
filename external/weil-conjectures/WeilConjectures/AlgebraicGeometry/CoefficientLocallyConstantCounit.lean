/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
import Mathlib.CategoryTheory.Sites.LocalProperties
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization

/-! # Classicality of coefficient-sized locally constant set sheaves

Source: Bhatt--Scholze, Lemmas 5.1.1--5.1.4.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.ConcreteCategory Opposite

namespace CategoryTheory.CoefficientClassical

private noncomputable def colimitEvaluationComparison
    {D : Type (u + 1)} [Category.{u} D]
    {J : Type w} [SmallCategory J] (K : J ⥤ Dᵒᵖ) (c : Cocone K)
    [HasColimitsOfShape J (Type (max v (u + 1)))] :
    (Functor.whiskeringLeft J Dᵒᵖ (Type (max v (u + 1)))).obj K ⋙ colim ⟶
      (evaluation Dᵒᵖ (Type (max v (u + 1)))).obj c.pt where
  app P := colimit.desc (K ⋙ P) (P.mapCocone c)
  naturality P Q f := by
    apply colimit.hom_ext
    intro j
    change colimit.ι (K ⋙ P) j ≫ colim.map (K.whiskerLeft f) ≫
        colimit.desc (K ⋙ Q) (Q.mapCocone c) =
      colimit.ι (K ⋙ P) j ≫ colimit.desc (K ⋙ P) (P.mapCocone c) ≫ f.app c.pt
    simp only [colim_map]
    rw [ι_colimMap_assoc, colimit.ι_desc, colimit.ι_desc_assoc]
    exact (f.naturality (c.ι.app j)).symm

/-- A set-valued left Kan extension preserves a colimit if the representables in
its defining image preserve that colimit.
Source: the density theorem for presheaves and commutation of colimits, applied to
the finite-presentation argument in Bhatt--Scholze, Lemma 5.1.1.
(auxiliary; not a blueprint node).

Proof: The canonical map from the colimit of values to the value at the colimit
is natural in a presheaf. Both its source and target preserve presheaf colimits:
Kan extension is a left adjoint, restriction and evaluation compute colimits
pointwise, and colimits commute with colimits. On a representable the Kan
extension is the representable of its image, so the given hypothesis makes this
map invertible. Express an arbitrary presheaf as the canonical colimit of its
representables. Preservation of that colimit makes the same map invertible for
the arbitrary presheaf. This is exactly the preservation criterion. -/
private theorem lan_preserves_colimit_of_representables
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (B : C ⥤ D) (G : Cᵒᵖ ⥤ Type (max v (u + 1)))
    {J : Type u} [SmallCategory J] (K : J ⥤ Dᵒᵖ) (c : Cocone K) (hc : IsColimit c)
    (h : ∀ Y, PreservesColimit K (uliftYoneda.{max v (u + 1)}.obj (B.obj Y))) :
    PreservesColimit K (B.op.lan.obj G) := by
  have : PreservesColimitsOfSize.{u, max v (u + 1)}
      (B.op.lan : (Cᵒᵖ ⥤ Type (max v (u + 1))) ⥤ Dᵒᵖ ⥤ Type (max v (u + 1))) :=
    (B.op.lanAdjunction (Type (max v (u + 1)))).leftAdjoint_preservesColimits
  let a : (Functor.whiskeringLeft J Dᵒᵖ (Type (max v (u + 1)))).obj K ⋙ colim ⟶
      (evaluation Dᵒᵖ (Type (max v (u + 1)))).obj c.pt :=
    colimitEvaluationComparison K c
  let a' := Functor.whiskerLeft B.op.lan a
  have hrep (Y : C) : IsIso (a.app (uliftYoneda.{max v (u + 1)}.obj (B.obj Y))) := by
    let := h Y
    change IsIso (colimit.desc (K ⋙ uliftYoneda.{max v (u + 1)}.obj (B.obj Y))
      ((uliftYoneda.{max v (u + 1)}.obj (B.obj Y)).mapCocone c))
    change IsIso (((colimit.isColimit _).coconePointUniqueUpToIso
      (isColimitOfPreserves (uliftYoneda.{max v (u + 1)}.obj (B.obj Y)) hc)).hom)
    infer_instance
  have happ (Y : C) : IsIso (a'.app (uliftYoneda.{max v (u + 1)}.obj Y)) := by
    let e := (Presheaf.compULiftYonedaIsoULiftYonedaCompLan.{max v (u + 1)} B).app Y
    have : IsIso (a.app (uliftYoneda.{max v (u + 1)}.obj (B.obj Y))) := hrep Y
    have eq : a'.app (uliftYoneda.{max v (u + 1)}.obj Y) =
        (((Functor.whiskeringLeft J Dᵒᵖ (Type (max v (u + 1)))).obj K ⋙ colim).map e.inv) ≫
          a.app (uliftYoneda.{max v (u + 1)}.obj (B.obj Y)) ≫
            ((evaluation Dᵒᵖ (Type (max v (u + 1)))).obj c.pt).map e.hom := by
      change a.app _ = _
      rw [← a.naturality, ← Functor.map_comp_assoc]
      rw [e.inv_hom_id, Functor.map_id, Category.id_comp]
      rfl
    rw [eq]
    infer_instance
  have : IsIso (Functor.whiskerLeft (Presheaf.functorToRepresentables.{max v (u + 1)} G) a') := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro i
    exact happ i.unop.1.unop
  have : IsIso (a'.app G) := isIso_app_coconePt_of_preservesColimit
    (Presheaf.functorToRepresentables.{max v (u + 1)} G) a'
      (Presheaf.coconeOfRepresentable.{max v (u + 1)} G)
      (Presheaf.colimitOfRepresentable.{max v (u + 1)} G)
  have : IsIso (colimit.desc (K ⋙ B.op.lan.obj G)
      ((B.op.lan.obj G).mapCocone c)) := by exact this
  have : IsIso ((colimit.isColimit (K ⋙ B.op.lan.obj G)).desc
      ((B.op.lan.obj G).mapCocone c)) := by exact this
  exact preservesColimit_of_preserves_colimit_cocone hc
    (IsColimit.ofPointIso (colimit.isColimit (K ⋙ B.op.lan.obj G)))

end CategoryTheory.CoefficientClassical

namespace AlgebraicGeometry.Scheme.CoefficientClassical

-- The original sites with values in the independent coefficient universe.
private noncomputable abbrev comparison (X : Scheme.{u}) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (toProEt X)
    (Type (max v (u + 1))) X.smallEtaleTopology (ProEt.topology X)

open Scheme in
private theorem setLanRelative (S : Scheme.{u}) (F : S.Etaleᵒᵖ ⥤ (Type (max v (u + 1)))) :
    Functor.PreservesRelativeFilteredColimits.{u} (AffineEtale.toAffineProEt S)
      ((AffineProEt.toProEt S).op ⋙ (Scheme.toProEt S).op.lan.obj F) := by
  constructor
  intro I _ _ K c hc
  -- The limit cone in the pro-étale site.
  have hc₁ : IsLimit ((AffineProEt.toProEt S).mapCone c) := isLimitOfPreserves _ hc
  -- The limit cone in `Over S`, obtained by reflecting the `Scheme`-level limit cone
  -- along `Over.forget S`.
  have hcOver : IsLimit ((ProEt.forget S).mapCone ((AffineProEt.toProEt S).mapCone c)) :=
    isLimitOfReflects (CategoryTheory.Over.forget S)
      (((AffineProEt.isLimitMapConeToSchemeOfIsLimit c hc).ofIsoLimit
        (Functor.mapConeMapCone c).symm).ofIsoLimit (Functor.mapConeMapCone _).symm)
  -- The comparison of the two relevant diagrams in the pro-étale site.
  have e : (K ⋙ AffineEtale.toAffineProEt S) ⋙ AffineProEt.toProEt S ≅
      (K ⋙ AffineEtale.Spec S) ⋙ Scheme.toProEt S :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft K (AffineEtale.toAffineProEtCompToProEtIso S) ≪≫
      (Functor.associator _ _ _).symm
  -- Mapping into an étale `S`-scheme commutes with the cofiltered limit, by
  -- `Scheme.preservesColimit_yoneda`.
  have hpres : ∀ (X : S.Etaleᵒᵖ),
      PreservesColimit ((K ⋙ AffineEtale.Spec S).op ⋙ (Scheme.toProEt S).op)
        (coyoneda.obj (Opposite.op ((Scheme.toProEt S).op.obj X))) := by
    intro X
    have h₁ : ∀ {i j : I} (f : i ⟶ j), IsAffineHom
        ((((K ⋙ AffineEtale.toAffineProEt S) ⋙ AffineProEt.toProEt S) ⋙
          ProEt.forget S).map f).left :=
      fun f ↦ inferInstanceAs
        (IsAffineHom ((AffineEtale.toAffineProEt S).map (K.map f)).left)
    have h₂ : ∀ (i : I), CompactSpace
        ((((K ⋙ AffineEtale.toAffineProEt S) ⋙ AffineProEt.toProEt S) ⋙
          ProEt.forget S).obj i).left :=
      fun i ↦ inferInstanceAs (CompactSpace ((AffineEtale.toAffineProEt S).obj (K.obj i)).left)
    have h₃ : ∀ (i : I), QuasiSeparatedSpace
        ((((K ⋙ AffineEtale.toAffineProEt S) ⋙ AffineProEt.toProEt S) ⋙
          ProEt.forget S).obj i).left :=
      fun i ↦ inferInstanceAs
        (QuasiSeparatedSpace ((AffineEtale.toAffineProEt S).obj (K.obj i)).left)
    have h₄ : LocallyOfFinitePresentation
        ((ProEt.forget S).obj ((Scheme.toProEt S).obj X.unop)).hom :=
      inferInstanceAs (LocallyOfFinitePresentation X.unop.hom)
    have := Scheme.preservesColimit_yoneda
      (((K ⋙ AffineEtale.toAffineProEt S) ⋙ AffineProEt.toProEt S) ⋙ ProEt.forget S)
      ((ProEt.forget S).obj ((Scheme.toProEt S).obj X.unop))
    have hyon : IsColimit
        ((yoneda.obj ((ProEt.forget S).obj ((Scheme.toProEt S).obj X.unop))).mapCocone
          ((ProEt.forget S).mapCone ((AffineProEt.toProEt S).mapCone c)).op) :=
      isColimitOfPreserves _ hcOver.op
    have hy : IsColimit ((yoneda.obj ((Scheme.toProEt S).obj X.unop)).mapCocone
        ((AffineProEt.toProEt S).mapCone c).op) :=
      IsColimit.mapCoconeEquiv (ProEt.forgetOpCompYonedaIso ((Scheme.toProEt S).obj X.unop))
        (by exact hyon)
    have hco : IsColimit ((coyoneda.obj (Opposite.op ((Scheme.toProEt S).op.obj X))).mapCocone
        ((AffineProEt.toProEt S).mapCone c).op) :=
      IsColimit.mapCoconeEquiv (Coyoneda.objOpOp _).symm hy
    let : PreservesColimit ((K ⋙ AffineEtale.toAffineProEt S) ⋙ AffineProEt.toProEt S).op
        (coyoneda.obj (Opposite.op ((Scheme.toProEt S).op.obj X))) :=
      preservesColimit_of_preserves_colimit_cocone hc₁.op hco
    exact preservesColimit_of_iso_diagram _ (NatIso.op e).symm
  let : PreservesColimit ((K ⋙ AffineEtale.Spec S).op ⋙ (Scheme.toProEt S).op)
      ((Scheme.toProEt S).op.leftKanExtension F) := inferInstance
  have e' : (K ⋙ AffineEtale.Spec S).op ⋙ (Scheme.toProEt S).op ≅
      ((K ⋙ AffineEtale.toAffineProEt S) ⋙ AffineProEt.toProEt S).op := NatIso.op e
  let : PreservesColimit ((K ⋙ AffineEtale.toAffineProEt S) ⋙ AffineProEt.toProEt S).op
      ((Scheme.toProEt S).op.leftKanExtension F) :=
    preservesColimit_of_iso_diagram _ e'
  exact ⟨isColimitOfPreserves ((Scheme.toProEt S).op.leftKanExtension F) hc₁.op⟩

open Scheme in
private theorem setLanSheaf (S : Scheme.{u}) (F : S.Etaleᵒᵖ ⥤ (Type (max v (u + 1))))
    (hF : Presheaf.IsSheaf (smallEtaleTopology S) F) :
    Presheaf.IsSheaf (AffineProEt.topology S)
      ((AffineProEt.toProEt S).op ⋙ (Scheme.toProEt S).op.lan.obj F) := by
  let := setLanRelative S F
  have : HasFilteredColimitsOfSize.{u, u} (Type (max v (u + 1))) :=
    hasFilteredColimitsOfSize_of_univLE.{u, u, max v (u + 1), max v (u + 1)}
  have : AB5OfSize.{u, u} (Type (max v (u + 1))) :=
    AB5OfSize_of_univLE.{u, u, max v (u + 1), max v (u + 1)} (Type (max v (u + 1)))
  apply Presheaf.isSheaf_of_generates_of_isRelativelyPresentable
      (AffineEtale.toAffineProEt S) (AffineProEt.minimalPrecoverage S)
      (AffineEtale.topology S)
  · let iso : (AffineEtale.toAffineProEt S).op ⋙
        (AffineProEt.toProEt S).op ⋙ S.toProEt.op.lan.obj F ≅
        (AffineEtale.Spec S).op ⋙ F :=
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Functor.opComp _ _).symm _ ≪≫
        Functor.isoWhiskerRight (NatIso.op (AffineEtale.toAffineProEtCompToProEtIso S).symm) _ ≪≫
        Functor.isoWhiskerRight (Functor.opComp _ _) _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (asIso <| ((Scheme.toProEt S).op.lanUnit.app F)).symm
    rw [Presheaf.isSheaf_of_iso_iff iso]
    exact Functor.op_comp_isSheaf_of_isSheaf _ _ _ _ hF
  · exact AffineProEt.generates_minimalPrecoverage S
  · exact AffineProEt.minimalPrecoverage_le_relativelyPresentable S
  · exact AffineProEt.minimalPrecoverage_le_finite S

open Scheme in
private theorem setIsIsoToSheafify {S : Scheme.{u}}
    (F : Sheaf S.smallEtaleTopology (Type (max v (u + 1))))
    (Y : S.ProEt) (hY : proAffineEtale Y.hom) :
    IsIso ((toSheafify (ProEt.topology S) ((toProEt S).op.lan.obj F.obj)).app (op Y)) := by
  have : HasLimitsOfSize.{u, u + 1} (Type (max v (u + 1))) :=
    hasLimitsOfSizeShrink.{u, u + 1, max v (u + 1), max v (u + 1)} (Type (max v (u + 1)))
  have h2 : IsIso ((AffineProEt.toProEt S).op.whiskerLeft
      (toSheafify (ProEt.topology S) ((toProEt S).op.lan.obj F.obj))) :=
    Functor.IsDenseSubsite.isIso_whiskerLeft_toSheafify
      (AffineProEt.topology S) _ _ (Type (max v (u + 1))) _
      (setLanSheaf S F.obj F.property)
  exact inferInstanceAs (IsIso (((AffineProEt.toProEt S).op.whiskerLeft
    (toSheafify (ProEt.topology S) ((toProEt S).op.lan.obj F.obj))).app
      (op (AffineProEt.mk Y.hom hY))))

open Scheme in
private theorem setComparisonUnit (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology (Type (max v (u + 1)))) :
    ((comparison.{u, v} X).unit.app F).hom =
      (toProEt X).op.lanUnit.app F.obj ≫
        (toProEt X).op.whiskerLeft
          (toSheafify _ ((toProEt X).op.lan.obj F.obj)) := by
  change (sheafToPresheaf _ (Type (max v (u + 1)))).map
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _).unit.app F) = _
  rw [Functor.sheafPullbackConstruction.sheafAdjunctionContinuous,
    Adjunction.map_restrictFullyFaithful_unit_app]
  simp

open Scheme in
private theorem setComparisonUnit_isIso (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology (Type (max v (u + 1)))) (W : X.Etale)
    [IsAffine W.left] :
    IsIso (((comparison.{u, v} X).unit.app F).hom.app (op W)) := by
  rw [setComparisonUnit]
  have : IsIso ((toSheafify (ProEt.topology X) ((toProEt X).op.lan.obj F.obj)).app
      (op ((toProEt X).obj W))) :=
    setIsIsoToSheafify F ((toProEt X).obj W)
      (@proAffineEtale.of_isAffine _ _ (inferInstanceAs (IsAffine W.left)) W.hom
        (inferInstanceAs (Etale W.hom)))
  change IsIso (((toProEt X).op.lanUnit.app F.obj).app (op W) ≫
    (toSheafify (ProEt.topology X) ((toProEt X).op.lan.obj F.obj)).app
      (op ((toProEt X).obj W)))
  infer_instance

-- Localize the comparison adjunction at U, commute scheme base change with the
-- comparison direct image, and evaluate the resulting isomorphism at the terminal
-- object. The comparison unit there is invertible.

/-- Full faithfulness of the set-valued comparison, in its unit-normalized form.
Source: Bhatt--Scholze, Lemmas 5.1.1--5.1.2.
(auxiliary; not a blueprint node).

Proof: Restrict the unit to the dense affine etale subsite. At every affine etale
object the Kan-extension unit is invertible because the inclusion is fully faithful,
and the sheafification map is invertible by the affine section formula. Their
composite is the comparison unit. Restriction to the dense subsite and inclusion
of sheaves into presheaves both reflect isomorphisms. -/
private theorem proEtaleComparisonUnitSets_isIso (X : Scheme.{u}) :
    IsIso (comparison.{u, v} X).unit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  let R := (AffineEtale.Spec X).sheafPushforwardContinuous (Type (max v (u + 1)))
    (AffineEtale.topology X) X.smallEtaleTopology
  suffices IsIso ((R ⋙ sheafToPresheaf _ (Type (max v (u + 1)))).map
      ((comparison.{u, v} X).unit.app F)) from
    isIso_of_reflects_iso _ (R ⋙ sheafToPresheaf _ (Type (max v (u + 1))))
  change IsIso ((AffineEtale.Spec X).op.whiskerLeft
    ((comparison.{u, v} X).unit.app F).hom)
  rw [NatTrans.isIso_iff_isIso_app]
  intro U
  have : IsAffine ((AffineEtale.Spec X).obj U.unop).left := by
    change IsAffine (Spec U.unop.left.unop)
    infer_instance
  exact setComparisonUnit_isIso X F ((AffineEtale.Spec X).obj U.unop)

private theorem isIso_app_of_colimits {C J : Type*} [Category* C] [Category* J]
    {P Q : Cᵒᵖ ⥤ Type w} (a : P ⟶ Q) {K : J ⥤ C} (c : Cone K)
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

private theorem setLanAffineContinuous (X : Scheme.{u})
    (G : X.Etaleᵒᵖ ⥤ Type (max v (u + 1))) :
    PreservesFilteredColimitsOfSize.{u, u}
      ((AffineProEt.toProEt X).op ⋙ (toProEt X).op.lan.obj G) := by
  constructor
  intro J _ _
  constructor
  intro K
  constructor
  intro c hc
  let K' := K.leftOp ⋙ AffineProEt.toProEt X
  let c' := (AffineProEt.toProEt X).mapCone (coneLeftOpOfCocone c)
  have hc' : IsLimit c' := isLimitOfPreserves _ (isLimitConeLeftOpOfCocone K hc)
  have hcOver : IsLimit ((ProEt.forget X).mapCone c') :=
    isLimitOfReflects (CategoryTheory.Over.forget X)
      (((AffineProEt.isLimitMapConeToSchemeOfIsLimit
        (coneLeftOpOfCocone c) (isLimitConeLeftOpOfCocone K hc)).ofIsoLimit
        (Functor.mapConeMapCone (coneLeftOpOfCocone c)).symm).ofIsoLimit
          (Functor.mapConeMapCone c').symm)
  have hpres (Y : X.Etale) :
      PreservesColimit K'.op (uliftYoneda.{max v (u + 1)}.obj ((toProEt X).obj Y)) := by
    have h₁ : ∀ {i j : Jᵒᵖ} (f : i ⟶ j),
        IsAffineHom (((K' ⋙ ProEt.forget X).map f).left) := fun f ↦
      inferInstanceAs (IsAffineHom ((K.leftOp.map f).left))
    have h₂ : ∀ i : Jᵒᵖ, CompactSpace (((K' ⋙ ProEt.forget X).obj i).left) := fun i ↦
      inferInstanceAs (CompactSpace ((K.leftOp.obj i).left))
    have h₃ : ∀ i : Jᵒᵖ, QuasiSeparatedSpace (((K' ⋙ ProEt.forget X).obj i).left) := fun i ↦
      inferInstanceAs (QuasiSeparatedSpace ((K.leftOp.obj i).left))
    have h₄ : LocallyOfFinitePresentation ((ProEt.forget X).obj ((toProEt X).obj Y)).hom :=
      inferInstanceAs (LocallyOfFinitePresentation Y.hom)
    have := Scheme.preservesColimit_yoneda (K' ⋙ ProEt.forget X)
      ((ProEt.forget X).obj ((toProEt X).obj Y))
    have hyon : IsColimit
        ((yoneda.obj ((ProEt.forget X).obj ((toProEt X).obj Y))).mapCocone
          ((ProEt.forget X).mapCone c').op) := isColimitOfPreserves _ hcOver.op
    have hy : IsColimit ((yoneda.obj ((toProEt X).obj Y)).mapCocone c'.op) :=
      IsColimit.mapCoconeEquiv (ProEt.forgetOpCompYonedaIso ((toProEt X).obj Y))
        (by exact hyon)
    have : PreservesColimit K'.op (yoneda.obj ((toProEt X).obj Y)) :=
      preservesColimit_of_preserves_colimit_cocone hc'.op hy
    change PreservesColimit K'.op (yoneda.obj ((toProEt X).obj Y) ⋙ uliftFunctor.{max v (u + 1)})
    infer_instance
  have := CategoryTheory.CoefficientClassical.lan_preserves_colimit_of_representables
    (toProEt X) G K'.op c'.op hc'.op hpres
  have hL := isColimitOfPreserves ((toProEt X).op.lan.obj G) hc'.op
  exact ⟨by exact hL.whiskerEquivalence (opOpEquivalence J).symm⟩

/-- The inverse image of an etale sheaf is continuous on affine ind-etale limits.
Source: Bhatt--Scholze, Lemmas 5.1.1--5.1.2, with the same finite-presentation
argument for arbitrary affine ind-etale stages.
(auxiliary; not a blueprint node).

Proof: Before sheafification the inverse image is a Kan extension. An etale
scheme is locally of finite presentation, so maps to it from a cofiltered limit
of affine schemes factor through a stage, with equality also detected at a
stage. Thus the representables defining the Kan extension preserve the given
filtered colimit. The density theorem and commutation of colimits imply that
the Kan extension does too. The affine section formula identifies this Kan
extension with its sheafification on every affine ind-etale stage and on the
limit; naturality identifies all restriction maps. -/
private theorem proEtaleComparisonSets_continuous (X : Scheme.{u})
    (G : Sheaf X.smallEtaleTopology (Type (max v (u + 1)))) :
    PreservesFilteredColimitsOfSize.{u, u}
      ((AffineProEt.toProEt X).op ⋙
        ((Functor.sheafPullbackConstruction.sheafPullback (toProEt X)
          (Type (max v (u + 1))) X.smallEtaleTopology (ProEt.topology X)).obj G).obj) := by
  have := setLanAffineContinuous X G.obj
  constructor
  intro J _ _
  constructor
  intro K
  constructor
  intro c hc
  let K' := K.leftOp ⋙ AffineProEt.toProEt X
  let c' := (AffineProEt.toProEt X).mapCone (coneLeftOpOfCocone c)
  have hc' : IsLimit c' :=
    isLimitOfPreserves _ (isLimitConeLeftOpOfCocone K hc)
  have hL : IsColimit (((toProEt X).op.lan.obj G.obj).mapCocone c'.op) := by
    have h := isColimitOfPreserves
      ((AffineProEt.toProEt X).op ⋙ (toProEt X).op.lan.obj G.obj)
        (isLimitConeLeftOpOfCocone K hc).op
    exact h
  have hStages (j : Jᵒᵖᵒᵖ) : IsIso
      ((toSheafify (ProEt.topology X) ((toProEt X).op.lan.obj G.obj)).app (op (K'.obj j.unop))) :=
    setIsIsoToSheafify G _ (K.leftOp.obj j.unop).prop
  have hPoint : IsIso
      ((toSheafify (ProEt.topology X) ((toProEt X).op.lan.obj G.obj)).app (op c'.pt)) :=
    setIsIsoToSheafify G _ c.pt.unop.prop
  have h := @ProEtale.isColimitMapCoconeOfNatTrans _ _ _ _ _ _ _ _
    (toSheafify (ProEt.topology X) ((toProEt X).op.lan.obj G.obj)) _ c'.op
      hStages hPoint hL
  exact ⟨by exact h.whiskerEquivalence (opOpEquivalence J).symm⟩

/-- The comparison counit is invertible for a sheaf continuous on affine ind-etale
presentations.
Source: Bhatt--Scholze, Lemmas 5.1.1--5.1.2.
(auxiliary; not a blueprint node).

Proof: Test on the dense affine ind-etale subsite. Present each basis object by
an etale cofiltered diagram. Both the sheaf and its comparison inverse image carry
this limit to a colimit. On finite stages the counit is inverse to the comparison
unit, hence is invertible. The unique map between the two colimits is therefore
invertible, and its naturality identifies it with the counit at the limit object. -/
private theorem proEtaleComparisonCounitSets_isIso_of_continuous (X : Scheme.{u})
    (F : Sheaf (ProEt.topology X) (Type (max v (u + 1))))
    (hF : Functor.PreservesRelativeFilteredColimits.{u} (AffineEtale.toAffineProEt X)
      ((AffineProEt.toProEt X).op ⋙ F.obj)) :
    IsIso ((comparison.{u, v} X).counit.app F) := by
  have hu := proEtaleComparisonUnitSets_isIso.{u, v} X
  let L := Functor.sheafPullbackConstruction.sheafPullback (toProEt X)
    (Type (max v (u + 1))) X.smallEtaleTopology (ProEt.topology X)
  have : L.Full := (comparison.{u, v} X).full_L_of_isSplitEpi_unit_app
  have : L.Faithful := (comparison.{u, v} X).faithful_L_of_mono_unit_app
  let a := ((comparison.{u, v} X).counit.app F).hom
  let R := (AffineProEt.toProEt X).sheafPushforwardContinuous (Type (max v (u + 1)))
    (AffineProEt.topology X) (ProEt.topology X)
  suffices IsIso ((R ⋙ sheafToPresheaf _ (Type (max v (u + 1)))).map
      ((comparison.{u, v} X).counit.app F)) from
    isIso_of_reflects_iso _ (R ⋙ sheafToPresheaf _ (Type (max v (u + 1))))
  change IsIso ((AffineProEt.toProEt X).op.whiskerLeft a)
  rw [NatTrans.isIso_iff_isIso_app]
  intro U
  obtain ⟨J, _, _, ⟨p⟩⟩ := U.unop.exists_relativeLimitPresentation
  let c := (AffineProEt.toProEt X).mapCone p.cone
  let K := p.diag ⋙ AffineEtale.Spec X
  let e : p.diag ⋙ AffineEtale.toAffineProEt X ⋙ AffineProEt.toProEt X ≅
      K ⋙ toProEt X := Functor.isoWhiskerLeft p.diag
        (AffineEtale.toAffineProEtCompToProEtIso X)
  let c' : Cone (K ⋙ toProEt X) := (Cone.postcompose e.hom).obj c
  have hcont := proEtaleComparisonSets_continuous X
    (((toProEt X).sheafPushforwardContinuous (Type (max v (u + 1)))
      X.smallEtaleTopology (ProEt.topology X)).obj F)
  have hP := isColimitOfPreserves
    ((AffineProEt.toProEt X).op ⋙
      (L.obj (((toProEt X).sheafPushforwardContinuous (Type (max v (u + 1)))
        X.smallEtaleTopology (ProEt.topology X)).obj F)).obj) p.isLimit.op
  obtain ⟨hQ⟩ := hF.nonempty_isColimit p.cone p.isLimit
  have hr : IsIso (((toProEt X).sheafPushforwardContinuous (Type (max v (u + 1)))
      X.smallEtaleTopology (ProEt.topology X)).map
        ((comparison.{u, v} X).counit.app F)) := inferInstance
  have ha (j : J) : IsIso (a.app (op ((K ⋙ toProEt X).obj j))) := by
    exact NatIso.isIso_app_of_isIso
      ((((toProEt X).sheafPushforwardContinuous (Type (max v (u + 1)))
        X.smallEtaleTopology (ProEt.topology X)).map
          ((comparison.{u, v} X).counit.app F)).hom) (op (K.obj j))
  exact isIso_app_of_colimits a c' (by exact hP) (by exact hQ)

end AlgebraicGeometry.Scheme.CoefficientClassical

namespace CategoryTheory.CoefficientClassical

private theorem finite_sections_lift
    {C : Type w} [Category.{u} C]
    {Λ : Type u} [SmallCategory Λ] [IsFiltered Λ]
    (D : Λ ⥤ Cᵒᵖ ⥤ Type (max v (u + 1))) (c : Cocone D) (hc : IsColimit c)
    {I : Type*} [Finite I] (Y : I → C) (x : ∀ i, c.pt.obj (op (Y i))) :
    ∃ (k : Λ) (y : ∀ i, (D.obj k).obj (op (Y i))),
      ∀ i, (c.ι.app k).app (op (Y i)) (y i) = x i := by
  classical
  have : Fintype I := Fintype.ofFinite I
  have hs (i : I) := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves ((evaluation _ _).obj (op (Y i))) hc) (x i)
  choose j y hy using hs
  obtain ⟨s⟩ := IsFiltered.cocone_nonempty (Discrete.functor j)
  refine ⟨s.pt, fun i ↦ (D.map (s.ι.app ⟨i⟩)).app _ (y i), fun i ↦ ?_⟩
  have hw := congrArg (fun t ↦ t.app (op (Y i))) (c.w (s.ι.app ⟨i⟩))
  exact (congr_hom hw (y i)).trans (hy i)

private theorem finite_sections_equal
    {C : Type w} [Category.{u} C]
    {Λ : Type u} [SmallCategory Λ] [IsFiltered Λ]
    (D : Λ ⥤ Cᵒᵖ ⥤ Type (max v (u + 1))) (c : Cocone D) (hc : IsColimit c)
    {I : Type*} [Finite I] (Y : I → C) (j : Λ)
    (x y : ∀ i, (D.obj j).obj (op (Y i)))
    (h : ∀ i, (c.ι.app j).app _ (x i) = (c.ι.app j).app _ (y i)) :
    ∃ (k : Λ) (f : j ⟶ k), ∀ i,
      (D.map f).app (op (Y i)) (x i) = (D.map f).app (op (Y i)) (y i) := by
  classical
  have hs (i : I) := (Types.FilteredColimit.isColimit_eq_iff'
    (isColimitOfPreserves ((evaluation _ _).obj (op (Y i))) hc) (x i) (y i)).mp (h i)
  choose k f hf using hs
  obtain ⟨l, g, q, hq⟩ := IsFiltered.wideSpan f
  refine ⟨l, g, fun i ↦ ?_⟩
  rw [← hq i]
  simp only [Functor.map_comp, NatTrans.comp_app, types_comp_apply]
  exact congrArg ((D.map (q i)).app _) (hf i)

/-- A filtered colimit of presheaves satisfying the sheaf condition for one finite
presieve with pairwise pullbacks satisfies that same condition.
Source: Stacks Project, Sites, Tag 0738(4) and Tag 00VM; Categories, Tag 002W
(auxiliary; not a blueprint node).

Proof: Index the arrows of R by its finite subtype of uncurried arrows. Evaluation
preserves presheaf colimits. For separatedness, lift two sections over X to a common
stage. Their restrictions agree in the colimit over each arrow of R, so each such
equality holds after a transition. The finite wide-span lemma for filtered categories
makes all of these transitions factor through a single transition. Separatedness at
that stage identifies the two sections, hence their images in the colimit agree.

For existence, lift the finitely many members of a compatible family to stages of
the diagram, and take a cocone over the finite discrete diagram of those stages.
This gives a family at one stage. For each pair of arrows of R, compatibility of its
image implies equality of the two restrictions over the pairwise pullback after a
transition. There are finitely many pairs, so the finite wide-span lemma again gives
one transition making every compatibility equation hold. At that stage the sheaf
condition provides an amalgamation. Its image amalgamates the original family by
naturality and the cocone equations. Empty R causes no exception: the finite discrete
cocone and the wide-span construction also apply to empty index sets, and the
stagewise empty-presieve sheaf condition supplies the unique section over X.

This is the finite-stage argument of Sites Tag 0738(4), applied directly to the
sectionwise presheaf colimit and the sheaf condition of Tag 00VM. -/
private theorem finitePresieveSheafFilteredColimit
    {C : Type w} [Category.{u} C]
    {Λ : Type u} [SmallCategory Λ] [IsFiltered Λ]
    (D : Λ ⥤ Cᵒᵖ ⥤ Type (max v (u + 1))) (c : Cocone D) (hc : IsColimit c)
    {X : C} (R : Presieve X) [R.HasPairwisePullbacks]
    (hfinite : R.uncurry.Finite)
    (hD : ∀ i, R.IsSheafFor (D.obj i)) : R.IsSheafFor c.pt := by
  classical
  let I := R.uncurry
  have : Finite I := Set.finite_coe_iff.mpr hfinite
  let Y : I → C := fun i ↦ i.val.1
  let f : ∀ i : I, Y i ⟶ X := fun i ↦ i.val.2
  have hf (i : I) : R (f i) := i.property
  rw [← Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  have hsep : R.IsSeparatedFor c.pt := by
    intro z a b haz hbz
    have hab {Z : C} {h : Z ⟶ X} (hh : R h) :
        c.pt.map h.op a = c.pt.map h.op b := (haz h hh).trans (hbz h hh).symm
    obtain ⟨j, a', b', ha, hb⟩ := Types.FilteredColimit.jointly_surjective_of_isColimit₂
      (isColimitOfPreserves ((evaluation _ _).obj (op X)) hc) a b
    change (c.ι.app j).app (op X) a' = a at ha
    change (c.ι.app j).app (op X) b' = b at hb
    have heq (i : I) :
        (c.ι.app j).app (op (Y i)) ((D.obj j).map (f i).op a') =
        (c.ι.app j).app (op (Y i)) ((D.obj j).map (f i).op b') := by
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply, ha, hb]
      exact hab (hf i)
    obtain ⟨k, g, hg⟩ := finite_sections_equal D c hc Y j
      (fun i ↦ (D.obj j).map (f i).op a')
      (fun i ↦ (D.obj j).map (f i).op b') heq
    have he : (D.map g).app (op X) a' = (D.map g).app (op X) b' := by
      apply (hD k).isSeparatedFor.ext
      intro Z h hh
      have eq := hg (⟨⟨Z, h⟩, hh⟩ : I)
      simpa only [Y, f, NatTrans.naturality_apply] using eq
    have hw := congrArg (fun t ↦ t.app (op X)) (c.w g)
    calc
      a = (c.ι.app j).app (op X) a' := ha.symm
      _ = (c.ι.app k).app (op X) ((D.map g).app (op X) a') :=
        (congr_hom hw a').symm
      _ = (c.ι.app k).app (op X) ((D.map g).app (op X) b') := congrArg _ he
      _ = (c.ι.app j).app (op X) b' := congr_hom hw b'
      _ = b := hb
  refine ⟨hsep, ?_⟩
  intro x hx
  obtain ⟨j, y, hy⟩ := finite_sections_lift D c hc Y (fun i ↦ x (f i) (hf i))
  have hp (ij : I × I) : HasPullback (f ij.1) (f ij.2) :=
    Presieve.HasPairwisePullbacks.has_pullbacks (hf ij.1) (hf ij.2)
  let Z : I × I → C := fun ij ↦ @pullback _ _ _ _ _ (f ij.1) (f ij.2) (hp ij)
  let a : ∀ ij : I × I, (D.obj j).obj (op (Z ij)) := fun ij ↦
    have := hp ij
    (D.obj j).map (pullback.fst (f ij.1) (f ij.2)).op (y ij.1)
  let b : ∀ ij : I × I, (D.obj j).obj (op (Z ij)) := fun ij ↦
    have := hp ij
    (D.obj j).map (pullback.snd (f ij.1) (f ij.2)).op (y ij.2)
  have heq (ij : I × I) :
      (c.ι.app j).app (op (Z ij)) (a ij) = (c.ι.app j).app (op (Z ij)) (b ij) := by
    have := hp ij
    dsimp [a, b, Z]
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply]
    exact (congrArg (c.pt.map (pullback.fst (f ij.1) (f ij.2)).op) (hy ij.1)).trans
      (((Presieve.pullbackCompatible_iff x).mp hx (hf ij.1) (hf ij.2)).trans
        (congrArg (c.pt.map (pullback.snd (f ij.1) (f ij.2)).op) (hy ij.2)).symm)
  obtain ⟨k, g, hg⟩ := finite_sections_equal D c hc Z j a b heq
  let z : R.FamilyOfElements (D.obj k) := fun T h hh ↦
    (D.map g).app (op T) (y (⟨⟨T, h⟩, hh⟩ : I))
  have hz : z.Compatible := by
    rw [Presieve.pullbackCompatible_iff]
    intro T₁ T₂ h₁ h₂ hh₁ hh₂
    let i₁ : I := ⟨⟨T₁, h₁⟩, hh₁⟩
    let i₂ : I := ⟨⟨T₂, h₂⟩, hh₂⟩
    have := hp (i₁, i₂)
    have eq := hg (i₁, i₂)
    simpa only [a, b, z, Z, i₁, i₂, Y, f, NatTrans.naturality_apply] using eq
  obtain ⟨s, hs, _⟩ := hD k z hz
  refine ⟨(c.ι.app k).app (op X) s, ?_⟩
  intro T h hh
  let i : I := ⟨⟨T, h⟩, hh⟩
  have hw := congrArg (fun t ↦ t.app (op T)) (c.w g)
  calc
    c.pt.map h.op ((c.ι.app k).app (op X) s) =
        (c.ι.app k).app (op T) ((D.obj k).map h.op s) :=
      (NatTrans.naturality_apply (c.ι.app k) h.op s).symm
    _ = (c.ι.app k).app (op T) ((D.map g).app (op T) (y i)) :=
      congrArg _ (hs h hh)
    _ = (c.ι.app j).app (op T) (y i) := congr_hom hw (y i)
    _ = x h hh := hy i

private theorem finiteGeneratedSheafFilteredColimit
    {C : Type (u + 1)} [Category.{u} C] [HasPullbacks C]
    (K : Precoverage C) (T : GrothendieckTopology C)
    (hK : K.Generates T) (hfinite : K ≤ Precoverage.finite C)
    {Λ : Type u} [SmallCategory Λ] [IsFiltered Λ]
    (D : Λ ⥤ Cᵒᵖ ⥤ Type (max v (u + 1))) (c : Cocone D) (hc : IsColimit c)
    (hD : ∀ i, Presheaf.IsSheaf T (D.obj i)) : Presheaf.IsSheaf T c.pt := by
  rw [isSheaf_iff_isSheaf_of_type]
  apply hK.isSheaf_of_forall
  intro X R hR
  apply finitePresieveSheafFilteredColimit D c hc R (hfinite X hR)
  intro i
  exact (hK.isSheaf_type_iff.mp
    ((isSheaf_iff_isSheaf_of_type T (D.obj i)).mp (hD i))) R hR

private noncomputable def productSections
    {C : Type (u + 1)} [Category.{u} C] [HasBinaryProducts C]
    (F : Cᵒᵖ ⥤ Type (max v (u + 1))) : Cᵒᵖ ⥤ Cᵒᵖ ⥤ Type (max v (u + 1)) :=
  (Limits.prod.functor : C ⥤ C ⥤ C).op ⋙
    Functor.opHom C C ⋙ (Functor.whiskeringRight _ _ _).obj F

private theorem productSections_isSheaf {C : Type (u + 1)} [Category.{u} C] [HasBinaryProducts C]
    (T : GrothendieckTopology C) (F : Sheaf T (Type (max v (u + 1)))) (B : C) :
    Presheaf.IsSheaf T ((productSections F.obj).obj (op B)) := by
  have hi : (Over.star B ⋙ Over.forget B).IsContinuous T T :=
    Functor.isContinuous_comp _ _ _ (T.over B) _
  have he : Over.star B ⋙ Over.forget B ≅ Limits.prod.functor.obj B := Iso.refl _
  have hi' : (Limits.prod.functor.obj B).IsContinuous T T :=
    Functor.isContinuous_of_iso he T T
  exact (Limits.prod.functor.obj B).op_comp_isSheaf T T F

private theorem productContinuity_of_cover
    {C : Type (u + 1)} [Category.{u} C] [HasBinaryProducts C] [HasPullbacks C]
    (K : Precoverage C) (T : GrothendieckTopology C)
    (hK : K.Generates T) (hfinite : K ≤ Precoverage.finite C)
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ C) (c : Cone D) (F : Sheaf T (Type (max v (u + 1))))
    {I : Type*} (U : I → C) (hU : T.CoversTop U)
    (hlocal : ∀ i (V : C) (_ : V ⟶ U i), Nonempty (IsColimit
      (F.obj.mapCocone ((Limits.prod.functor.flip.obj V).mapCone c).op))) :
    ∀ V : C, Nonempty (IsColimit
      (F.obj.mapCocone ((Limits.prod.functor.flip.obj V).mapCone c).op)) := by
  let B := productSections F.obj
  let Q := B.mapCocone c.op
  let P := D.op ⋙ B
  let a := colimit.desc P Q
  have hP : Presheaf.IsSheaf T (colimit P) :=
    finiteGeneratedSheafFilteredColimit K T hK hfinite P _ (colimit.isColimit P)
      (fun j ↦ productSections_isSheaf T F (D.obj j.unop))
  have hQ : Presheaf.IsSheaf T Q.pt := productSections_isSheaf T F c.pt
  let a' : (⟨colimit P, hP⟩ : Sheaf T (Type (max v (u + 1)))) ⟶ ⟨Q.pt, hQ⟩ := ⟨a⟩
  have hlocal' (i : I) (V : C) (f : V ⟶ U i) : IsIso (a.app (op V)) := by
    let E := (evaluation Cᵒᵖ (Type (max v (u + 1)))).obj (op V)
    let hc := isColimitOfPreserves E (colimit.isColimit P)
    obtain ⟨hd⟩ : Nonempty (IsColimit (E.mapCocone Q)) := hlocal i V f
    have heq : a.app (op V) = (hc.coconePointUniqueUpToIso hd).hom := by
      apply hc.hom_ext
      intro j
      change (colimit.ι P j).app (op V) ≫ a.app (op V) = _
      rw [← NatTrans.comp_app, colimit.ι_desc]
      exact (hc.comp_coconePointUniqueUpToIso_hom hd j).symm
    rw [heq]
    infer_instance
  have ha' : IsIso a' := by
    apply Sheaf.isIso_of_coversTop hU
    intro i
    rw [← ObjectProperty.isIso_hom_iff, NatTrans.isIso_iff_isIso_app]
    intro V
    exact hlocal' i V.unop.left V.unop.hom
  have ha : IsIso a := (sheafToPresheaf T (Type (max v (u + 1)))).map_isIso a'
  have : IsIso ((colimit.isColimit P).desc Q) := ha
  have hQcolim : IsColimit Q := IsColimit.ofPointIso (colimit.isColimit P)
  intro V
  exact ⟨isColimitOfPreserves ((evaluation Cᵒᵖ (Type (max v (u + 1)))).obj (op V)) hQcolim⟩

end CategoryTheory.CoefficientClassical

namespace AlgebraicGeometry.Scheme.CoefficientClassical

private noncomputable abbrev comparisonCoefficientPullback (X : Scheme.{u}) :=
  Functor.sheafPullbackConstruction.sheafPullback (toProEt X)
    (Type (max v (u + 1))) X.smallEtaleTopology (ProEt.topology X)

private noncomputable abbrev etaleComparisonPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  Functor.sheafPullbackConstruction.sheafPullback
    (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (max v (u + 1)))
    Y.smallEtaleTopology X.smallEtaleTopology

private noncomputable abbrev proEtaleComparisonPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  Functor.sheafPullbackConstruction.sheafPullback
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) (Type (max v (u + 1)))
    (ProEt.topology Y) (ProEt.topology X)

private noncomputable abbrev proEtaleComparisonAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) (Type (max v (u + 1)))
    (ProEt.topology Y) (ProEt.topology X)

private noncomputable def comparisonCoefficientPullbackIso {X Y : Scheme.{u}}
    (f : X ⟶ Y) :
    etaleComparisonPullback.{u, v} f ⋙
      comparisonCoefficientPullback.{u, v} X ≅
    comparisonCoefficientPullback.{u, v} Y ⋙
      proEtaleComparisonPullback.{u, v} f := by
  let D := Type (max v (u + 1))
  have : (MorphismProperty.Over.pullback @Etale ⊤ f).IsContinuous
      Y.smallEtaleTopology X.smallEtaleTopology := Etale.isContinuous_overPullback f
  let a := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ f) D Y.smallEtaleTopology X.smallEtaleTopology
  let b := proEtaleComparisonAdjunction.{u, v} f
  have := ProEt.isContinuous_overPullback f
  have := isContinuous_toProEt X
  have := isContinuous_toProEt Y
  have := Functor.isContinuous_comp (toProEt Y)
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f)
    Y.smallEtaleTopology (ProEt.topology Y) (ProEt.topology X)
  have := Functor.isContinuous_comp (MorphismProperty.Over.pullback @Etale ⊤ f)
    (toProEt X) Y.smallEtaleTopology X.smallEtaleTopology (ProEt.topology X)
  let e := Functor.sheafPushforwardContinuousComp (toProEt Y)
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) D Y.smallEtaleTopology
      (ProEt.topology Y) (ProEt.topology X) ≪≫
    Functor.sheafPushforwardContinuousIso (ProEtale.toProEtCompOverPullbackIso f) D
      Y.smallEtaleTopology (ProEt.topology X) ≪≫
    (Functor.sheafPushforwardContinuousComp (MorphismProperty.Over.pullback @Etale ⊤ f)
      (toProEt X) D Y.smallEtaleTopology X.smallEtaleTopology (ProEt.topology X)).symm
  exact ((conjugateIsoEquiv (a.comp (comparison.{u, v} X))
    ((comparison.{u, v} Y).comp b)).symm e.symm).symm

private noncomputable def restrictionInverseImageIso (X : Scheme.{u}) (U : X.ProEt) :
    proEtaleComparisonPullback.{u, v} U.hom ≅
      @Functor.sheafPushforwardContinuous U.left.ProEt _ X.ProEt _
        (MorphismProperty.Over.map (P := @WeaklyEtale) ⊤ U.prop)
        (Type (max v (u + 1))) _ (ProEt.topology U.left) (ProEt.topology X)
        (ProEt.isContinuous_overMap U.prop) := by
  letI hMap := ProEt.isContinuous_overMap U.prop
  letI hPull := ProEt.isContinuous_overPullback U.hom
  have hMap' : (MorphismProperty.Over.map (P := @WeaklyEtale) ⊤ U.prop).IsContinuous
      (ProEt.topology U.left) (ProEt.topology X) := ProEt.isContinuous_overMap U.prop
  let adj : (MorphismProperty.Over.map (P := @WeaklyEtale) ⊤ U.prop) ⊣
      MorphismProperty.Over.pullback @WeaklyEtale ⊤ U.hom :=
    MorphismProperty.Over.mapPullbackAdj (@WeaklyEtale) ⊤ U.hom U.prop _root_.trivial
  exact (proEtaleComparisonAdjunction.{u, v} U.hom).leftAdjointUniq
    (@Adjunction.sheafPushforwardContinuous _ _ _ _ _ _ _ _ adj
      (ProEt.topology U.left) (ProEt.topology X) hMap' hPull)

private noncomputable def classicalRestrictionIso (X : Scheme.{u}) (U : X.ProEt) :
    comparisonCoefficientPullback.{u, v} X ⋙
      @Functor.sheafPushforwardContinuous U.left.ProEt _ X.ProEt _
        (MorphismProperty.Over.map (P := @WeaklyEtale) ⊤ U.prop)
        (Type (max v (u + 1))) _ (ProEt.topology U.left) (ProEt.topology X)
        (ProEt.isContinuous_overMap U.prop) ≅
    etaleComparisonPullback.{u, v} U.hom ⋙
      comparisonCoefficientPullback.{u, v} U.left :=
  (Functor.isoWhiskerLeft _ (restrictionInverseImageIso X U)).symm ≪≫
    (comparisonCoefficientPullbackIso.{u, v} U.hom).symm

private abbrev restriction (X : Scheme.{u}) (U : X.ProEt) :=
  @Functor.sheafPushforwardContinuous U.left.ProEt _ X.ProEt _
    (MorphismProperty.Over.map (P := @WeaklyEtale) ⊤ U.prop)
    (Type (max v (u + 1))) _ (ProEt.topology U.left) (ProEt.topology X)
    (ProEt.isContinuous_overMap U.prop)

private noncomputable def refinedDiagram (X : Scheme.{u}) (U : X.AffineProEt)
    {J : Type u} [SmallCategory J] (D : J ⥤ X.AffineProEt)
    (s : D ⟶ (Functor.const J).obj U) : J ⥤ U.left.AffineProEt :=
  MorphismProperty.Over.iteratedLift D s (fun j ↦ AffineProEt.proAffineEtale_hom _)

private noncomputable def refinedCone (X : Scheme.{u}) (U : X.AffineProEt)
    {J : Type u} [SmallCategory J] {D : J ⥤ X.AffineProEt}
    (s : D ⟶ (Functor.const J).obj U) (c : Cone D) (t : c.pt ⟶ U)
    (ht : ∀ j, c.π.app j ≫ s.app j = t) : Cone (refinedDiagram X U D s) where
  pt := AffineProEt.mk t.left (AffineProEt.proAffineEtale_hom t)
  π.app j := MorphismProperty.Over.homMk (c.π.app j).left
    (congrArg (fun f ↦ f.left) (ht j))
  π.naturality i j f := by
    apply MorphismProperty.Over.Hom.ext
    exact congrArg (fun f ↦ f.left) (c.π.naturality f)

private noncomputable def refinedConeIsLimit (X : Scheme.{u}) (U : X.AffineProEt)
    {J : Type u} [SmallCategory J] [IsCofiltered J] {D : J ⥤ X.AffineProEt}
    (s : D ⟶ (Functor.const J).obj U) (c : Cone D) (t : c.pt ⟶ U)
    (ht : ∀ j, c.π.app j ≫ s.app j = t) (hc : IsLimit c) :
    IsLimit (refinedCone X U s c t ht) := by
  apply isLimitOfReflects (AffineProEt.toScheme U.left)
  exact AffineProEt.isLimitMapConeToSchemeOfIsLimit c hc

private noncomputable def refinedDiagramIso (X : Scheme.{u}) (U : X.AffineProEt)
    {J : Type u} [SmallCategory J] (D : J ⥤ X.AffineProEt)
    (s : D ⟶ (Functor.const J).obj U) :
    refinedDiagram X U D s ⋙ AffineProEt.toProEt U.left ⋙
        MorphismProperty.Over.map (P := @WeaklyEtale) ⊤
          ((AffineProEt.toProEt X).obj U).prop ≅ D ⋙ AffineProEt.toProEt X :=
  NatIso.ofComponents (fun j ↦ MorphismProperty.Over.isoMk (Iso.refl _)
    (MorphismProperty.Over.w (s.app j)).symm)
    (fun f ↦ MorphismProperty.Over.Hom.ext (by simp; rfl))

private noncomputable def refinedConeIso (X : Scheme.{u}) (U : X.AffineProEt)
    {J : Type u} [SmallCategory J] {D : J ⥤ X.AffineProEt}
    (s : D ⟶ (Functor.const J).obj U) (c : Cone D) (t : c.pt ⟶ U)
    (ht : ∀ j, c.π.app j ≫ s.app j = t) :
    (Cone.postcompose (refinedDiagramIso X U D s).hom).obj
      (((AffineProEt.toProEt U.left) ⋙
        MorphismProperty.Over.map (P := @WeaklyEtale) ⊤
          ((AffineProEt.toProEt X).obj U).prop).mapCone
            (refinedCone X U s c t ht)) ≅
      (AffineProEt.toProEt X).mapCone c := by
  let ep : ((MorphismProperty.Over.map (P := @WeaklyEtale) ⊤
      ((AffineProEt.toProEt X).obj U).prop).obj
      ((AffineProEt.toProEt U.left).obj (refinedCone X U s c t ht).pt)) ≅
      (AffineProEt.toProEt X).obj c.pt :=
    MorphismProperty.Over.isoMk (Iso.refl _) (MorphismProperty.Over.w t).symm
  refine Cone.ext ep ?_
  intro j
  apply MorphismProperty.Over.Hom.ext
  change (c.π.app j).left ≫ 𝟙 _ = 𝟙 _ ≫ (c.π.app j).left
  simp

private theorem continuity_over_basis_object (X : Scheme.{u}) (U : X.AffineProEt)
    (F : Sheaf (ProEt.topology X) (Type (max v (u + 1))))
    (hF : PreservesFilteredColimitsOfSize.{u, u}
      ((AffineProEt.toProEt U.left).op ⋙
        ((restriction X ((AffineProEt.toProEt X).obj U)).obj F).obj))
    {J : Type u} [SmallCategory J] [IsCofiltered J] {D : J ⥤ X.AffineProEt}
    (s : D ⟶ (Functor.const J).obj U) (c : Cone D) (t : c.pt ⟶ U)
    (ht : ∀ j, c.π.app j ≫ s.app j = t) (hc : IsLimit c) :
    Nonempty (IsColimit
      (F.obj.mapCocone ((AffineProEt.toProEt X).mapCone c).op)) := by
  let c' := refinedCone X U s c t ht
  have hc' := refinedConeIsLimit X U s c t ht hc
  have := hF
  let R := (restriction X ((AffineProEt.toProEt X).obj U)).obj F
  have hR : IsColimit (((AffineProEt.toProEt U.left).op ⋙ R.obj).mapCocone c'.op) :=
    isColimitOfPreserves _ hc'.op
  let iD := refinedDiagramIso X U D s
  let iC := refinedConeIso X U s c t ht
  let cNew := ((AffineProEt.toProEt U.left) ⋙
    MorphismProperty.Over.map (P := @WeaklyEtale) ⊤
      ((AffineProEt.toProEt X).obj U).prop).mapCone c'
  have hR' : IsColimit (F.obj.mapCocone cNew.op) := hR
  refine ⟨(IsColimit.equivOfNatIsoOfIso
    (Functor.isoWhiskerRight (NatIso.op iD.symm) F.obj) (F.obj.mapCocone cNew.op) _ ?_).toFun hR'⟩
  refine Cocone.ext (F.obj.mapIso ((Cone.forget _).mapIso iC).op).symm ?_
  intro j
  change F.obj.map (iD.hom.app j.unop).op ≫
    F.obj.map (cNew.π.app j.unop).op ≫ F.obj.map iC.inv.hom.op =
      F.obj.map (((AffineProEt.toProEt X).mapCone c).π.app j.unop).op
  rw [← F.obj.map_comp, ← F.obj.map_comp, ← op_comp, ← op_comp]
  congr 2

private theorem affineHasTerminal (X : Scheme.{u}) [IsAffine X] :
    HasTerminal X.AffineProEt := by
  apply IsTerminal.hasTerminal (X := AffineProEt.ofEtale (𝟙 X))
  exact IsTerminal.ofUniqueHom
    (fun U ↦ MorphismProperty.Over.homMk U.hom (Category.comp_id _))
    (fun U f ↦ MorphismProperty.Over.Hom.ext (by
      change f.left = U.hom
      have hw : f.left ≫ 𝟙 X = U.hom := MorphismProperty.Over.w f
      exact (Category.comp_id _).symm.trans hw))

private noncomputable def rightProdIso {C : Type*} [Category* C] [HasBinaryProducts C] (V : C) :
    Limits.prod.functor.flip.obj V ≅ Limits.prod.functor.obj V :=
  NatIso.ofComponents (fun W ↦ Limits.prod.braiding W V) (by
    intro W W' f
    apply Limits.prod.hom_ext <;> simp)

private theorem affine_continuity (X : Scheme.{u}) [IsAffine X]
    (F : Sheaf (ProEt.topology X) (Type (max v (u + 1))))
    (I : Type (max v (u + 1))) (U : I → X.AffineProEt)
    (hU : (AffineProEt.topology X).CoversTop U)
    (hF : ∀ i, ∃ G : Sheaf (U i).left.smallEtaleTopology (Type (max v (u + 1))), Nonempty
      ((restriction X ((AffineProEt.toProEt X).obj (U i))).obj F ≅
        (comparisonCoefficientPullback.{u, v} (U i).left).obj G)) :
    PreservesFilteredColimitsOfSize.{u, u} ((AffineProEt.toProEt X).op ⋙ F.obj) := by
  have := affineHasTerminal X
  have : HasFiniteLimits X.AffineProEt := hasFiniteLimits_of_hasTerminal_and_pullbacks
  constructor
  intro J _ _
  have : IsConnected Jᵒᵖ := IsCofiltered.isConnected _
  constructor
  intro K
  constructor
  intro d hd
  let D := K.leftOp
  let c := coneLeftOpOfCocone d
  have hc : IsLimit c := isLimitConeLeftOpOfCocone K hd
  let F' := ((AffineProEt.toProEt X).sheafPushforwardContinuous (Type (max v (u + 1)))
    (AffineProEt.topology X) (ProEt.topology X)).obj F
  have hall := CategoryTheory.CoefficientClassical.productContinuity_of_cover
    (AffineProEt.minimalPrecoverage X) (AffineProEt.topology X)
    (AffineProEt.generates_minimalPrecoverage X) (AffineProEt.minimalPrecoverage_le_finite X)
    D c F' U hU (fun i V f ↦ ?_)
  · obtain ⟨hT⟩ := hall (⊤_ X.AffineProEt)
    let ep : Limits.prod.functor.flip.obj (⊤_ X.AffineProEt) ≅ 𝟭 X.AffineProEt :=
      NatIso.ofComponents (fun W ↦ Limits.prod.rightUnitor W)
        (fun f ↦ Limits.prod.rightUnitor_hom_naturality f)
    have hC : IsColimit (F'.obj.mapCocone c.op) :=
      IsColimit.mapCoconeEquiv (Functor.isoWhiskerRight (NatIso.op ep.symm) F'.obj) hT
    exact ⟨by exact hC.whiskerEquivalence (opOpEquivalence J).symm⟩
  · let cV := (Limits.prod.functor.flip.obj V).mapCone c
    have : PreservesLimitsOfShape Jᵒᵖ (Limits.prod.functor.obj V) :=
      prod_preservesConnectedLimits V
    have : PreservesLimitsOfShape Jᵒᵖ (Limits.prod.functor.flip.obj V) :=
      preservesLimitsOfShape_of_natIso (rightProdIso V).symm
    have hcV : IsLimit cV := isLimitOfPreserves _ hc
    let s : D ⋙ Limits.prod.functor.flip.obj V ⟶ (Functor.const Jᵒᵖ).obj (U i) :=
      { app j := Limits.prod.snd ≫ f
        naturality j k a := by simp }
    let t : cV.pt ⟶ U i := Limits.prod.snd ≫ f
    have ht : ∀ j, cV.π.app j ≫ s.app j = t := by
      intro j
      change Limits.prod.map (c.π.app j) (𝟙 V) ≫ Limits.prod.snd ≫ f = _
      rw [Limits.prod.map_snd_assoc, Category.id_comp]
      rfl
    obtain ⟨G, ⟨e⟩⟩ := hF i
    have hClass : PreservesFilteredColimitsOfSize.{u, u}
        ((AffineProEt.toProEt (U i).left).op ⋙
          ((comparisonCoefficientPullback.{u, v} (U i).left).obj G).obj) :=
      proEtaleComparisonSets_continuous.{u, v} (U i).left G
    have hres : PreservesFilteredColimitsOfSize.{u, u}
        ((AffineProEt.toProEt (U i).left).op ⋙
          ((restriction X ((AffineProEt.toProEt X).obj (U i))).obj F).obj) := by
      constructor
      intro L _ _
      let ep := Functor.isoWhiskerLeft (AffineProEt.toProEt (U i).left).op
        ((sheafToPresheaf _ (Type (max v (u + 1)))).mapIso e.symm)
      exact @preservesColimitsOfShape_of_natIso _ _ _ _ L _ _ _ ep
        (hClass.preserves_filtered_colimits L)
    exact continuity_over_basis_object X (U i) F hres s cV t ht hcV

private theorem global_continuity (X : Scheme.{u})
    (F : Sheaf (ProEt.topology X) (Type (max v (u + 1))))
    (hF : ∀ U : X.AffineProEt,
      PreservesFilteredColimitsOfSize.{u, u}
        ((AffineProEt.toProEt U.left).op ⋙
          ((restriction X ((AffineProEt.toProEt X).obj U)).obj F).obj)) :
    Functor.PreservesRelativeFilteredColimits.{u} (AffineEtale.toAffineProEt X)
      ((AffineProEt.toProEt X).op ⋙ F.obj) := by
  constructor
  intro J _ _ D c hc
  classical
  let j₀ : J := IsCofiltered.nonempty.some
  let D₀ := CategoryTheory.Over.forget j₀ ⋙ D ⋙ AffineEtale.toAffineProEt X
  let c₀ := c.whisker (CategoryTheory.Over.forget j₀)
  let U := (D ⋙ AffineEtale.toAffineProEt X).obj j₀
  let s : D₀ ⟶ (Functor.const (CategoryTheory.Over j₀)).obj U :=
    Functor.whiskerRight (CategoryTheory.Over.forgetCocone j₀).ι
      (D ⋙ AffineEtale.toAffineProEt X) ≫ (Functor.constComp _ _ _).hom
  let t : c₀.pt ⟶ U := c.π.app j₀
  have ht : ∀ j, c₀.π.app j ≫ s.app j = t := by
    intro j
    exact c.w j.hom
  have hc₀ : IsLimit c₀ := (Functor.Initial.isLimitWhiskerEquiv _ _).symm hc
  obtain ⟨h⟩ := continuity_over_basis_object X U F (hF U) s c₀ t ht hc₀
  exact ⟨(Functor.Final.isColimitWhiskerEquiv
    (CategoryTheory.Over.forget j₀).op _).toFun h⟩

private theorem affineClassicalCover (X : Scheme.{u})
    (F : Sheaf (ProEt.topology X) (Type (max v (u + 1))))
    (I : Type (max v (u + 1))) (U : I → X.ProEt) (hU : (ProEt.topology X).CoversTop U)
    (hF : ∀ i, ∃ G : Sheaf (U i).left.smallEtaleTopology (Type (max v (u + 1))), Nonempty
      ((restriction X (U i)).obj F ≅
        (comparisonCoefficientPullback.{u, v} (U i).left).obj G))
    (V : X.AffineProEt) :
    ∃ (A : Type (max v (u + 1))) (W : A → V.left.AffineProEt),
      (AffineProEt.topology V.left).CoversTop W ∧
      ∀ a, ∃ G : Sheaf (W a).left.smallEtaleTopology (Type (max v (u + 1))), Nonempty
        ((restriction V.left ((AffineProEt.toProEt V.left).obj (W a))).obj
          ((restriction X ((AffineProEt.toProEt X).obj V)).obj F) ≅
            (comparisonCoefficientPullback.{u, v} (W a).left).obj G) := by
  let V' := (AffineProEt.toProEt X).obj V
  let M := MorphismProperty.Over.map (P := @WeaklyEtale) ⊤ V'.prop
  let E := AffineProEt.toProEt V.left ⋙ M
  have hm : M.IsCocontinuous (ProEt.topology V.left) (ProEt.topology X) :=
    ProEt.isCocontinuous_overMap V'.prop
  have he : E.IsCocontinuous (AffineProEt.topology V.left) (ProEt.topology X) :=
    isCocontinuous_comp _ _ _ (ProEt.topology V.left)
  let A := Σ Z : V.left.AffineProEt, Σ i : I, E.obj Z ⟶ U i
  refine ⟨A, Sigma.fst, ?_, ?_⟩
  · intro T
    apply (AffineProEt.topology V.left).superset_covering _
      (E.cover_lift _ _ (hU (E.obj T)))
    rintro Z f ⟨i, ⟨g⟩⟩
    exact ⟨⟨Z, i, g⟩, ⟨𝟙 Z⟩⟩
  · rintro ⟨Z, i, g⟩
    have hcomp : WeaklyEtale (g.left ≫ (U i).hom) := by
      rw [MorphismProperty.Over.w g]
      exact (E.obj Z).prop
    have hg : WeaklyEtale g.left := WeaklyEtale.of_comp g.left (U i).hom
    let Zg : (U i).left.ProEt := ProEt.mk g.left
    obtain ⟨G, ⟨e⟩⟩ := hF i
    let Z' := (AffineProEt.toProEt V.left).obj Z
    let Mg := MorphismProperty.Over.map (P := @WeaklyEtale) ⊤ Zg.prop
    let Mi := MorphismProperty.Over.map (P := @WeaklyEtale) ⊤ (U i).prop
    let Mz := MorphismProperty.Over.map (P := @WeaklyEtale) ⊤ Z'.prop
    let eMaps : Mz ⋙ M ≅ Mg ⋙ Mi := NatIso.ofComponents
      (fun W ↦ MorphismProperty.Over.isoMk (Iso.refl _) (by
        change 𝟙 W.left ≫ ((W.hom ≫ g.left) ≫ (U i).hom) =
          (W.hom ≫ Z.hom) ≫ V.hom
        simp only [Category.id_comp, Category.assoc]
        exact congrArg (fun a ↦ W.hom ≫ a) (MorphismProperty.Over.w g)))
      (fun f ↦ MorphismProperty.Over.Hom.ext (by simp; rfl))
    let eR : (restriction V.left Z').obj ((restriction X V').obj F) ≅
        (restriction (U i).left Zg).obj ((restriction X (U i)).obj F) :=
      { hom := ⟨Functor.whiskerRight (NatTrans.op eMaps.inv) F.obj⟩
        inv := ⟨Functor.whiskerRight (NatTrans.op eMaps.hom) F.obj⟩
        hom_inv_id := by ext W; simp [← F.obj.map_comp, ← op_comp]; rfl
        inv_hom_id := by ext W; simp [← F.obj.map_comp, ← op_comp]; rfl }
    refine ⟨(etaleComparisonPullback.{u, v} g.left).obj G, ⟨?_⟩⟩
    exact eR ≪≫ (restriction (U i).left Zg).mapIso e ≪≫
      (classicalRestrictionIso (U i).left Zg).app G

/-- Local etale presentations imply continuity on affine ind-etale presentations.
Source: Bhatt--Scholze, Lemma 5.1.4, using the continuity criterion of Lemma 5.1.2.
(auxiliary; not a blueprint node).

Proof: Refine the given cover over each affine basis object by all affine ind-etale
objects admitting a map to one of its members. Cocontinuity of localization and of
the dense affine inclusion proves that these objects cover. Raw restriction is the
scheme inverse image, by the map/pullback adjunction, so comparison/pullback
compatibility preserves the local etale presentations on this refinement.

Over an affine base, form the diagram of sheaves V |-> F(C_j times V) and its
canonical cocone V |-> F(C times V). These are sheaves because product with a
fixed object is continuous. Their pointwise filtered colimit is again a sheaf:
the affine pro-etale topology is generated by finite presieves with pairwise
pullbacks, and finitely many representatives and equality witnesses move to a
single stage. Over each refined cover member the classical-continuity theorem
makes the cocone limiting in the required colimit sense, including on every
object mapping to that member. Thus the comparison from the pointwise colimit
to the cocone point is an isomorphism locally, hence globally. Evaluate at the
terminal affine object to obtain section continuity over the affine base.

For a general base, pass to the cofinal over-category of any stage of the affine
etale presentation. Regard this diagram as an affine ind-etale diagram over that
affine stage. The affine result applies to the restriction of F there, and finality
of the opposite over-category returns the original section colimit. Empty covers
are included in the finite-presieve argument; filtered categories are nonempty. -/
private theorem proEtale_locallyClassical_continuity (X : Scheme.{u})
    (F : Sheaf (ProEt.topology X) (Type (max v (u + 1))))
    (I : Type (max v (u + 1))) (U : I → X.ProEt) (hU : (ProEt.topology X).CoversTop U)
    (hF : ∀ i, ∃ G : Sheaf (U i).left.smallEtaleTopology (Type (max v (u + 1))), Nonempty
      (((@Functor.sheafPushforwardContinuous (U i).left.ProEt _ X.ProEt _
          (MorphismProperty.Over.map (P := @WeaklyEtale) ⊤ (U i).prop)
          (Type (max v (u + 1))) _ (ProEt.topology (U i).left) (ProEt.topology X)
          (ProEt.isContinuous_overMap (U i).prop)).obj F) ≅
        (Functor.sheafPullbackConstruction.sheafPullback (toProEt (U i).left)
          (Type (max v (u + 1))) (U i).left.smallEtaleTopology
          (ProEt.topology (U i).left)).obj G)) :
    Functor.PreservesRelativeFilteredColimits.{u} (AffineEtale.toAffineProEt X)
      ((AffineProEt.toProEt X).op ⋙ F.obj) := by
  apply global_continuity X F
  intro V
  obtain ⟨A, W, hW, hG⟩ := affineClassicalCover.{u, v} X F I U hU hF V
  exact affine_continuity V.left
    ((restriction X ((AffineProEt.toProEt X).obj V)).obj F) A W hW hG

-- Constants descend by uniqueness of their left adjunction to global sections.
private noncomputable def comparisonConstantIso (X : Scheme.{u}) :
    constantSheaf X.smallEtaleTopology (Type (max v (u + 1))) ⋙
      Functor.sheafPullbackConstruction.sheafPullback (toProEt X)
        (Type (max v (u + 1))) X.smallEtaleTopology (ProEt.topology X) ≅
      constantSheaf (ProEt.topology X) (Type (max v (u + 1))) :=
  (((constantSheafAdj X.smallEtaleTopology (Type (max v (u + 1)))
      (MorphismProperty.Over.mkIdTerminal _ X)).comp (comparison.{u, v} X)).ofNatIsoRight
      (NatIso.ofComponents (fun _ ↦ Iso.refl _))).leftAdjointUniq
    (constantSheafAdj (ProEt.topology X) (Type (max v (u + 1)))
      (MorphismProperty.Over.mkIdTerminal _ X))

private noncomputable def modelEquivalence {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) :
    Sheaf ((AsSmall.down : AsSmall.{max v (u + 1)} C ⥤ C).inducedTopology J)
      (Type (max v (u + 1))) ≌ Sheaf J (Type (max v (u + 1))) := by
  let e := AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := C)
  have : (AsSmall.up : C ⥤ AsSmall.{max v (u + 1)} C).IsContinuous J
      (AsSmall.down.inducedTopology J) :=
    inferInstanceAs (e.functor.IsContinuous J (e.inverse.inducedTopology J))
  exact CategoryTheory.Equivalence.mk
    (AsSmall.up.sheafPushforwardContinuous (Type (max v (u + 1))) J
      (AsSmall.down.inducedTopology J))
    (AsSmall.down.sheafPushforwardContinuous (Type (max v (u + 1)))
      (AsSmall.down.inducedTopology J) J) (Iso.refl _) (Iso.refl _)

private noncomputable def modelSliceFrom (X : Scheme.{u})
    (W : coefficientProEtaleSiteModel.{u, v} X) :
    (AsSmall.down.obj W).left.ProEt ⥤ Over W :=
  ProEt.sliceFrom X (AsSmall.down.obj W) ⋙ Over.post AsSmall.up

private instance modelUp_cocontinuous (X : Scheme.{u}) :
    (AsSmall.up : X.ProEt ⥤ coefficientProEtaleSiteModel.{u, v} X).IsCocontinuous
      (ProEt.topology X) (coefficientProEtaleModelTopology.{u, v} X) := by
  let e := AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt)
  have : e.functor.IsDenseSubsite (ProEt.topology X)
      (e.inverse.inducedTopology (ProEt.topology X)) := inferInstance
  exact inferInstanceAs (e.functor.IsCocontinuous (ProEt.topology X)
    (e.inverse.inducedTopology (ProEt.topology X)))

private instance modelSliceFrom_continuous (X : Scheme.{u})
    (W : coefficientProEtaleSiteModel.{u, v} X) :
    (modelSliceFrom X W).IsContinuous (ProEt.topology (AsSmall.down.obj W).left)
      ((coefficientProEtaleModelTopology.{u, v} X).over W) := by
  let U : X.ProEt := AsSmall.down.obj W
  let J := ProEt.topology X
  let K := coefficientProEtaleModelTopology.{u, v} X
  have := ProEt.sliceDense X U
  have : (ProEt.sliceFrom X U).IsContinuous (ProEt.topology U.left) (J.over U) :=
    inferInstanceAs ((ProEt.sliceEquiv X U).inverse.IsContinuous
      (ProEt.topology U.left) (J.over U))
  have : (AsSmall.up : X.ProEt ⥤ coefficientProEtaleSiteModel.{u, v} X).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt)).functor.IsEquivalence
  have : (Over.post (X := U) (AsSmall.up : X.ProEt ⥤
      coefficientProEtaleSiteModel.{u, v} X)).IsContinuous (J.over U) (K.over W) :=
    Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
      ((CoverPreserving.of_isContinuous AsSmall.up J K).overPost U)
  exact Functor.isContinuous_comp (ProEt.sliceFrom X U) (Over.post AsSmall.up)
    (ProEt.topology U.left) (J.over U) (K.over W)

private instance modelSliceFrom_cocontinuous (X : Scheme.{u})
    (W : coefficientProEtaleSiteModel.{u, v} X) :
    (modelSliceFrom X W).IsCocontinuous (ProEt.topology (AsSmall.down.obj W).left)
      ((coefficientProEtaleModelTopology.{u, v} X).over W) := by
  let U : X.ProEt := AsSmall.down.obj W
  have := ProEt.sliceFrom_cocont X U
  have : (AsSmall.up : X.ProEt ⥤ coefficientProEtaleSiteModel.{u, v} X).IsCocontinuous
      (ProEt.topology X) (coefficientProEtaleModelTopology.{u, v} X) :=
    modelUp_cocontinuous.{u, v} X
  have : (Over.post (X := U) (AsSmall.up : X.ProEt ⥤
      coefficientProEtaleSiteModel.{u, v} X)).IsCocontinuous ((ProEt.topology X).over U)
        ((coefficientProEtaleModelTopology.{u, v} X).over W) :=
    inferInstanceAs ((Over.post (X := U) (AsSmall.up : X.ProEt ⥤
      coefficientProEtaleSiteModel.{u, v} X)).IsCocontinuous ((ProEt.topology X).over U)
        ((coefficientProEtaleModelTopology.{u, v} X).over (AsSmall.up.obj U)))
  exact isCocontinuous_comp (ProEt.sliceFrom X U) (Over.post AsSmall.up)
    (ProEt.topology U.left) ((ProEt.topology X).over U)

private theorem raw_localClassical (X : Scheme.{u})
    (H : Sheaf (coefficientProEtaleModelTopology.{u, v} X) (Type (max v (u + 1))))
    {I : Type (max v (u + 1))} (W : I → coefficientProEtaleSiteModel.{u, v} X)
    (hW : (coefficientProEtaleModelTopology.{u, v} X).CoversTop W)
    (hH : ∀ i, ∃ Q : Type (max v (u + 1)), Nonempty
      (H.over (W i) ≅ (constantSheaf
        ((coefficientProEtaleModelTopology.{u, v} X).over (W i))
        (Type (max v (u + 1)))).obj Q)) :
    IsIso ((comparison.{u, v} X).counit.app
      ((modelEquivalence.{u, v} (ProEt.topology X)).functor.obj H)) := by
  let F := (modelEquivalence.{u, v} (ProEt.topology X)).functor.obj H
  let U : I → X.ProEt := fun i ↦ AsSmall.down.obj (W i)
  have : (AsSmall.up : X.ProEt ⥤ coefficientProEtaleSiteModel.{u, v} X).IsCocontinuous
      (ProEt.topology X) (coefficientProEtaleModelTopology.{u, v} X) :=
    modelUp_cocontinuous.{u, v} X
  have hU : (ProEt.topology X).CoversTop U := by
    intro V
    apply (ProEt.topology X).superset_covering _
      ((AsSmall.up : X.ProEt ⥤ coefficientProEtaleSiteModel.{u, v} X).cover_lift
        (ProEt.topology X) (coefficientProEtaleModelTopology.{u, v} X)
        (hW (AsSmall.up.obj V)))
    rintro Z f ⟨i, ⟨g⟩⟩
    exact ⟨i, ⟨g.down⟩⟩
  have hlocal (i : I) : ∃ G : Sheaf (U i).left.smallEtaleTopology
      (Type (max v (u + 1))), Nonempty
      ((restriction X (U i)).obj F ≅
        (comparisonCoefficientPullback.{u, v} (U i).left).obj G) := by
    obtain ⟨Q, ⟨e⟩⟩ := hH i
    let R := (modelSliceFrom X (W i)).sheafPushforwardContinuous (Type (max v (u + 1)))
      (ProEt.topology (U i).left)
      ((coefficientProEtaleModelTopology.{u, v} X).over (W i))
    let e₀ : (restriction X (U i)).obj F ≅ R.obj (H.over (W i)) :=
      ObjectProperty.isoMk _ (Iso.refl _)
    let ec := ((modelSliceFrom X (W i)).pushforwardContinuousSheafificationCompatibility
      (Type (max v (u + 1))) (ProEt.topology (U i).left)
      ((coefficientProEtaleModelTopology.{u, v} X).over (W i))).app
        ((Functor.const (Over (W i))ᵒᵖ).obj Q)
    refine ⟨(constantSheaf (U i).left.smallEtaleTopology
      (Type (max v (u + 1)))).obj Q, ⟨?_⟩⟩
    exact e₀ ≪≫ R.mapIso e ≪≫ ec.symm ≪≫
      ((comparisonConstantIso (U i).left).app Q).symm
  exact proEtaleComparisonCounitSets_isIso_of_continuous X F
    (proEtale_locallyClassical_continuity.{u, v} X F I U hU hlocal)

private theorem model_counit_of_raw (X : Scheme.{u})
    (H : Sheaf (coefficientProEtaleModelTopology.{u, v} X) (Type (max v (u + 1))))
    (hH : IsIso ((comparison.{u, v} X).counit.app
      ((modelEquivalence.{u, v} (ProEt.topology X)).functor.obj H))) :
    IsIso ((smallModelProEtaleComparison.{u, v} X).counit.app H) := by
  let E := modelEquivalence.{u, v} X.smallEtaleTopology
  let P := modelEquivalence.{u, v} (ProEt.topology X)
  let a := (E.toAdjunction.comp (comparison.{u, v} X)).comp P.symm.toAdjunction
  let eR : P.functor ⋙
      (toProEt X).sheafPushforwardContinuous (Type (max v (u + 1)))
        X.smallEtaleTopology (ProEt.topology X) ⋙ E.inverse ≅
      smallModelComparisonPushforward.{u, v} X :=
    NatIso.ofComponents (fun _ ↦ ObjectProperty.isoMk _ (Iso.refl _))
  have ha : IsIso (a.counit.app H) := by
    have hRaw : IsIso ((comparison.{u, v} X).counit.app (P.symm.inverse.obj H)) := hH
    have hE : IsIso (E.toAdjunction.counit.app
        (((toProEt X).sheafPushforwardContinuous (Type (max v (u + 1)))
          X.smallEtaleTopology (ProEt.topology X)).obj (P.symm.inverse.obj H))) :=
      inferInstanceAs (IsIso (E.counitIso.hom.app _))
    have hMiddle : IsIso ((E.toAdjunction.comp (comparison.{u, v} X)).counit.app
        (P.symm.inverse.obj H)) := by
      rw [Adjunction.comp_counit_app]
      infer_instance
    have hP : IsIso (P.symm.toAdjunction.counit.app H) :=
      inferInstanceAs (IsIso (P.symm.counitIso.hom.app H))
    change IsIso (((E.toAdjunction.comp (comparison.{u, v} X)).comp
      P.symm.toAdjunction).counit.app H)
    rw [Adjunction.comp_counit_app]
    infer_instance
  let b := a.ofNatIsoRight eR
  have hb : IsIso (b.counit.app H) := by
    dsimp [b, Adjunction.ofNatIsoRight]
    infer_instance
  let e := (smallModelProEtaleComparison.{u, v} X).leftAdjointUniq b
  have he := Adjunction.leftAdjointUniq_hom_app_counit
    (smallModelProEtaleComparison.{u, v} X) b H
  rw [← he]
  infer_instance

end AlgebraicGeometry.Scheme.CoefficientClassical

namespace AlgebraicGeometry.ProEtale

/-- The comparison counit is invertible for a locally constant set sheaf, in the
coefficient universe, on the existing small site models.

Source: Bhatt--Scholze, Lemmas 5.1.1--5.1.4, p. 34
(auxiliary; not a blueprint node).

Proof: transport the slice restrictions and covering family through AsSmall and
weakly etale localization. Constant sheaves are classical: compose the constant
sheaf adjunction on the etale site with the comparison adjunction and use uniqueness
of left adjoints to identify its inverse image with the pro-etale constant sheaf.
Thus the given local trivializations make the sheaf locally classical. Classicality
is local by the equalizer argument of Lemma 5.1.4: work on an affine ind-etale basis,
take a finite affine refinement of the trivializing cover of Spec A, and form its
finite disjoint union Spec B. The restrictions on its components are classical;
sections on the disjoint union and its base changes are finite products of these
classical section functors. Write
an ind-etale A-algebra C as a filtered colimit of etale A-algebras C_j. The sheaf
condition expresses sections over C and C_j as equalizers of sections over their
base changes to B and B tensor B. Local classicality identifies the latter two
section sets with the corresponding filtered colimits. Filtered colimits of sets
commute with equalizers, so the same holds over C. The affine section formula of
Lemma 5.1.1 and the counit criterion of Lemma 5.1.2 now show the counit invertible
on the affine basis, and hence everywhere. This proof works in max v (u+1): every
geometric diagram has size at most u+1 and filtered colimits and finite equalizers
exist and commute in the coefficient universe. No constant set need be inhabited;
the empty-base case is covered by the same sheaf condition. Transport the result
back through the site equivalences to the displayed counit. -/
theorem coefficientLocallyConstant_counit_isIso (X : Scheme.{u})
    (H : Sheaf (Scheme.coefficientProEtaleModelTopology.{u, v} X)
      (Type (max v (u + 1))))
    (hH : ∃ (L : Type (max v (u + 1)))
      (W : L → Scheme.coefficientProEtaleSiteModel.{u, v} X),
      (Scheme.coefficientProEtaleModelTopology.{u, v} X).CoversTop W ∧
        ∀ j : L, ∃ Q : Type (max v (u + 1)),
          Nonempty (H.over (W j) ≅
            (constantSheaf ((Scheme.coefficientProEtaleModelTopology.{u, v} X).over (W j))
              (Type (max v (u + 1)))).obj Q)) :
    IsIso ((Scheme.smallModelProEtaleComparison.{u, v} X).counit.app H) := by
  obtain ⟨I, W, hW, hH⟩ := hH
  exact Scheme.CoefficientClassical.model_counit_of_raw X H
    (Scheme.CoefficientClassical.raw_localClassical X H W hW hH)

end AlgebraicGeometry.ProEtale
