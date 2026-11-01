import Langlands.AlgebraicGeometry.Picard.PolarizationBaseChangeStatement
import Langlands.AlgebraicGeometry.Picard.AmpleMumfordTransport
import Langlands.AlgebraicGeometry.Picard.DualBaseChangePoincare
import Langlands.AbelianScheme.BaseChangeCoherence

/-! # Stability of relative polarizations under base change -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable {S S' S'' S''' : Scheme.{u}}

/-- The underlying map of a base-changed homomorphism lies over the original homomorphism. -/
@[reassoc]
lemma hom_baseChange_map_fst (t : S''' ⟶ S'') {Z W : AbelianScheme S''} (φ : Z ⟶ W) :
    hom ((baseChange t).map φ) ≫ pullback.fst W.X.hom t = pullback.fst Z.X.hom t ≫ hom φ := by
  change ((Over.pullback t).map (groupHom φ).hom.hom).left ≫ _ = _
  simp

/-- The first projection of the actual family-space map for the self-product of an abelian
scheme. -/
@[reassoc]
lemma baseChangeFamilySpaceMap_self_fst (t : S''' ⟶ S'') (Z : AbelianScheme S'') :
    baseChangeFamilySpaceMap t Z Z.X ≫ pullback.fst Z.X.hom Z.X.hom =
      pullback.fst ((baseChange t).obj Z).X.hom ((baseChange t).obj Z).X.hom ≫
        pullback.fst Z.X.hom t :=
  baseChangeFamilySpaceMap_fst t Z Z.X

/-- The second projection of the actual family-space map for the self-product of an abelian
scheme. -/
@[reassoc]
lemma baseChangeFamilySpaceMap_self_snd (t : S''' ⟶ S'') (Z : AbelianScheme S'') :
    baseChangeFamilySpaceMap t Z Z.X ≫ pullback.snd Z.X.hom Z.X.hom =
      pullback.snd ((baseChange t).obj Z).X.hom ((baseChange t).obj Z).X.hom ≫
        pullback.fst Z.X.hom t :=
  baseChangeFamilySpaceMap_snd t Z Z.X

variable (b : S' ⟶ S) (c : S'' ⟶ S') (t : S''' ⟶ S'') (A : AbelianScheme S)

/-- The underlying map of the inverse composition comparison, followed by the projection of
the direct base change. -/
@[reassoc]
lemma hom_baseChangeCompIso_inv_fst :
    hom (baseChangeCompIso b c A).inv ≫ pullback.fst A.X.hom (c ≫ b) =
      pullback.fst ((baseChange b).obj A).X.hom c ≫ pullback.fst A.X.hom b :=
  GroupScheme.baseChangeCompIso_inv_fst b c A.toGrp

/-- The actual total-space maps of the direct and successive base changes agree along the
induced map of self-products of the comparison isomorphism. -/
lemma mumfordProductMap_baseChangeComp :
    mumfordProductMap ((baseChange t).map (baseChangeCompIso b c A).inv) ≫
        baseChangeFamilySpaceMap t ((baseChange (c ≫ b)).obj A)
          ((baseChange (c ≫ b)).obj A).X ≫
        baseChangeFamilySpaceMap (c ≫ b) A A.X =
      baseChangeFamilySpaceMap t ((baseChange c).obj ((baseChange b).obj A))
          ((baseChange c).obj ((baseChange b).obj A)).X ≫
        baseChangeFamilySpaceMap c ((baseChange b).obj A) ((baseChange b).obj A).X ≫
        baseChangeFamilySpaceMap b A A.X := by
  apply pullback.hom_ext
  · simp only [Category.assoc, baseChangeFamilySpaceMap_self_fst,
      baseChangeFamilySpaceMap_self_fst_assoc, mumfordProductMap_fst_assoc,
      hom_baseChange_map_fst_assoc, hom_baseChangeCompIso_inv_fst]
  · simp only [Category.assoc, baseChangeFamilySpaceMap_self_snd,
      baseChangeFamilySpaceMap_self_snd_assoc, mumfordProductMap_snd_assoc,
      hom_baseChange_map_fst_assoc, hom_baseChangeCompIso_inv_fst]

/-- The successive base-change comparison is a homomorphism whose underlying map is an
isomorphism. -/
instance isIso_hom_baseChange_map_baseChangeCompIso_inv :
    IsIso (hom ((baseChange t).map (baseChangeCompIso b c A).inv)) :=
  ⟨hom ((baseChange t).map (baseChangeCompIso b c A).hom),
    by rw [← hom_comp, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, hom_id],
    by rw [← hom_comp, ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, hom_id]⟩

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (square : MumfordBundlePicardZeroStatement.{u})
  (universality : PicardZeroUniversalBaseChangeStatement.{u})

/-- An ample Mumford presentation after base change along `t` of the direct base change along
`c ≫ b` gives one after base change along `t` of the successive base change along `b`,
then `c`. -/
theorem hasAmpleMumfordAfterBaseChange_comp (hA : HasDualScheme A)
    (f : A.X ⟶ dualScheme A hA)
    (h : HasAmpleMumfordAfterBaseChange preservation square ((baseChange (c ≫ b)).obj A)
      (hasDualScheme_baseChange universality (c ≫ b) A hA) universality t
      (dualBaseChangeMap A hA universality (c ≫ b) f)) :
    HasAmpleMumfordAfterBaseChange preservation square
      ((baseChange c).obj ((baseChange b).obj A))
      (hasDualScheme_baseChange universality c _ (hasDualScheme_baseChange universality b A hA))
      universality t
      (dualBaseChangeMap _ _ universality c (dualBaseChangeMap A hA universality b f)) := by
  refine hasAmpleMumfordPresentation_of_homomorphism
    ((baseChange t).map (baseChangeCompIso b c A).inv) preservation square _ _ _ _ ?_ h
  exact ⟨dualBaseChangeMapPoincareForgetIso t universality _ _ _ ≪≫
    (LineBundle.pullback _).mapIso
      (dualBaseChangeMapPoincareForgetIso c universality _ _ _ ≪≫
        (LineBundle.pullback _).mapIso
          (dualBaseChangeMapPoincareForgetIso b universality A hA f) ≪≫
        LineBundle.pullbackCompEqIso _ _ rfl _) ≪≫
    LineBundle.pullbackCompEqIso _ _ rfl _ ≪≫
    LineBundle.pullbackEqIso (mumfordProductMap_baseChangeComp b c t A).symm _ ≪≫
    ((LineBundle.pullback _).mapIso
      (dualBaseChangeMapPoincareForgetIso t universality _ _ _ ≪≫
        (LineBundle.pullback _).mapIso
          (dualBaseChangeMapPoincareForgetIso (c ≫ b) universality A hA f) ≪≫
        LineBundle.pullbackCompEqIso _ _ rfl _) ≪≫
      LineBundle.pullbackCompEqIso _ _ rfl _).symm⟩

/-- A relative polarization remains a relative polarization after actual base change and the
canonical comparison with the dual of the changed abelian scheme. -/
theorem polarizationBaseChange : PolarizationBaseChangeStatement.{u} := by
  intro preservation square universality stability composition unitCoherence associativity
    comparison symmetry compatibility S S' b A hA geometryA MA evaluationA hA' geometryA' MA'
    evaluationA' lam h
  let e := dualAbelianBaseChangeIso preservation stability composition unitCoherence associativity
    comparison symmetry universality compatibility b A hA geometryA MA evaluationA
    hA' geometryA' MA' evaluationA'
  let eg : ((baseChange b).obj (dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
        evaluationA stability composition unitCoherence associativity comparison
        symmetry)).toGrp ≅
      (dualAbelianSchemeFromEvaluation ((baseChange b).obj A) hA' geometryA' preservation MA'
        evaluationA' stability composition unitCoherence associativity comparison symmetry).toGrp :=
    { hom := groupHom e.hom
      inv := groupHom e.inv
      hom_inv_id := congrArg (fun f => groupHom f) e.hom_inv_id
      inv_hom_id := congrArg (fun f => groupHom f) e.inv_hom_id }
  let : IsIso eg.hom := eg.isIso_hom
  have he : IsIsogeny e.hom := Langlands.GroupScheme.isIsogeny_of_isIso eg.hom
  refine ⟨(h.1.baseChange b).comp he, ?_⟩
  intro K _ _ s
  rw [dualAbelianBaseChangeMap_hom]
  obtain ⟨K', _, ι, hp⟩ := h.2 K (s ≫ b)
  exact ⟨K', _, ι, hasAmpleMumfordAfterBaseChange_comp b s _ A preservation square universality
    hA _ hp⟩

end Langlands.AbelianScheme
