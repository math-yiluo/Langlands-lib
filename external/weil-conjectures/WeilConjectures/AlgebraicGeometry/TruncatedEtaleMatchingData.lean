/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteSplitEtaleHypercover
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.LimitsOver
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
/-!
# Finite matching limits of truncated étale diagrams

Source: blueprint corollary-cohomology-pro-etale-affine, finite matching-limit paragraph.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
/-- Matching objects for a finite truncated étale diagram, with universality in schemes over
its base. Source: blueprint finite-hypercover-descent, finite matching-limit paragraph.
(auxiliary; not a blueprint node) -/
structure TruncatedEtaleMatchingData (X : Scheme.{u}) (r : ℕ)
    (S : SimplicialObject.Truncated X.Etale r) where
  matching : Fin (r + 1) → X.Etale
  projection : ∀ (n : Fin (r + 1)) (Δ : SimplexCategory.Truncated r),
    Δ.obj.len < n.val → (Δ.obj ⟶ SimplexCategory.mk n.val) →
      (matching n ⟶ S.obj (op Δ))
  projection_naturality : ∀ (n : Fin (r + 1)) (Δ Δ' : SimplexCategory.Truncated r)
    (h : Δ.obj.len < n.val) (h' : Δ'.obj.len < n.val) (α : Δ' ⟶ Δ)
    (θ : Δ.obj ⟶ SimplexCategory.mk n.val),
    projection n Δ h θ ≫ S.map α.op =
      projection n Δ' h' (α.hom ≫ θ)
  matching_universal : ∀ (n : Fin (r + 1)) (T : Over X)
    (p : ∀ (Δ : SimplexCategory.Truncated r), Δ.obj.len < n.val →
      (Δ.obj ⟶ SimplexCategory.mk n.val) →
        (T ⟶ (Scheme.Etale.forget X).obj (S.obj (op Δ)))),
    (∀ (Δ Δ' : SimplexCategory.Truncated r)
      (h : Δ.obj.len < n.val) (h' : Δ'.obj.len < n.val) (α : Δ' ⟶ Δ)
      (θ : Δ.obj ⟶ SimplexCategory.mk n.val),
      p Δ h θ ≫ (Scheme.Etale.forget X).map (S.map α.op) =
        p Δ' h' (α.hom ≫ θ)) →
    ∃! f : T ⟶ (Scheme.Etale.forget X).obj (matching n),
      ∀ (Δ : SimplexCategory.Truncated r) (h : Δ.obj.len < n.val)
        (θ : Δ.obj ⟶ SimplexCategory.mk n.val),
        f ≫ (Scheme.Etale.forget X).map (projection n Δ h θ) = p Δ h θ
  matchingMap : ∀ n : Fin (r + 1),
    S.obj (op ⟨SimplexCategory.mk n.val, Nat.le_of_lt_succ n.isLt⟩) ⟶ matching n
  matchingMap_projection : ∀ (n : Fin (r + 1)) (Δ : SimplexCategory.Truncated r)
    (h : Δ.obj.len < n.val) (θ : Δ.obj ⟶ SimplexCategory.mk n.val),
    matchingMap n ≫ projection n Δ h θ =
      S.map (SimplexCategory.Truncated.Hom.tr θ Δ.property
        (Nat.le_of_lt_succ n.isLt)).op
  matching_qcqs : ∀ n, CompactSpace (matching n).left ∧
    QuasiSeparatedSpace (matching n).left

private def etaleQcqs (X : Scheme.{u}) : ObjectProperty X.Etale :=
  fun V ↦ CompactSpace V.left ∧ QuasiSeparatedSpace V.left
set_option backward.isDefEq.respectTransparency false in
private theorem qcqs_closed_pullbacks (X : Scheme.{u}) :
    (etaleQcqs X).IsClosedUnderLimitsOfShape WalkingCospan where
  limitsOfShape_le := by
    rintro P ⟨h⟩
    let F := h.diag
    let c : Cone F := ⟨P, h.π⟩
    let c' := (Cone.postcompose (diagramIsoCospan F).hom).obj c
    have hc' : IsLimit c' := (IsLimit.postcomposeHomEquiv _ c).symm h.isLimit
    have hp := (IsPullback.of_isLimit hc').map (Scheme.Etale.forget X ⋙ Over.forget X)
    have : CompactSpace (F.obj WalkingCospan.left).left := (h.prop_diag_obj _).1
    have : QuasiSeparatedSpace (F.obj WalkingCospan.left).left :=
      (h.prop_diag_obj _).2
    have : QuasiSeparatedSpace (F.obj WalkingCospan.one).left :=
      (h.prop_diag_obj _).2
    have : QuasiCompact ((Scheme.Etale.forget X ⋙ Over.forget X).map
        (F.map WalkingCospan.Hom.inl)) := by
      change QuasiCompact (F.map WalkingCospan.Hom.inl).left
      infer_instance
    have : QuasiSeparated ((Scheme.Etale.forget X ⋙ Over.forget X).map
        (F.map WalkingCospan.Hom.inl)) := by
      change QuasiSeparated (F.map WalkingCospan.Hom.inl).left
      infer_instance
    have : QuasiCompact ((Scheme.Etale.forget X ⋙ Over.forget X).map
        (c'.π.app WalkingCospan.right)) :=
      MorphismProperty.of_isPullback hp inferInstance
    have : QuasiSeparated ((Scheme.Etale.forget X ⋙ Over.forget X).map
        (c'.π.app WalkingCospan.right)) :=
      MorphismProperty.of_isPullback hp inferInstance
    exact ⟨@QuasiCompact.compactSpace_of_compactSpace _ _
        ((Scheme.Etale.forget X ⋙ Over.forget X).map (c'.π.app WalkingCospan.right))
        ‹_› (h.prop_diag_obj WalkingCospan.right).1,
      @quasiSeparatedSpace_of_quasiSeparated _ _
        ((Scheme.Etale.forget X ⋙ Over.forget X).map (c'.π.app WalkingCospan.right))
        (h.prop_diag_obj WalkingCospan.right).2 ‹_›⟩
set_option backward.isDefEq.respectTransparency false in
private theorem qcqs_finite_limits (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] :
    ∃ _h : HasFiniteLimits (etaleQcqs X).FullSubcategory,
      @PreservesFiniteLimits _ _ _ _ ((etaleQcqs X).ι ⋙ Scheme.Etale.forget X) := by
  let := qcqs_closed_pullbacks X
  let C := (etaleQcqs X).FullSubcategory
  have : HasPullbacks C := inferInstance
  have : PreservesLimitsOfShape WalkingCospan (etaleQcqs X).ι := inferInstance
  let t : C := ⟨Scheme.Etale.mk (𝟙 X), inferInstanceAs (CompactSpace X),
    inferInstanceAs (QuasiSeparatedSpace X)⟩
  have ht' : IsTerminal ((etaleQcqs X).ι.obj t) :=
    MorphismProperty.Over.mkIdTerminal _ _
  have ht : IsTerminal t := ht'.isTerminalOfObj (etaleQcqs X).ι t
  have : HasTerminal C := ht.hasTerminal
  have hf : HasFiniteLimits C := hasFiniteLimits_of_hasTerminal_and_pullbacks
  have : PreservesLimit (Functor.empty C) (etaleQcqs X).ι := by
    apply preservesLimit_of_preserves_limit_cone ht
    exact (isLimitMapConeEmptyConeEquiv _ _).symm ht'
  have : PreservesLimitsOfShape (Discrete PEmpty) (etaleQcqs X).ι :=
    preservesLimitsOfShape_pempty_of_preservesTerminal _
  have : PreservesFiniteLimits (etaleQcqs X).ι :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks _
  exact ⟨hf, inferInstance⟩
private def truncDegree {r : ℕ} (n : Fin (r + 1)) : SimplexCategory.Truncated r :=
  ⟨SimplexCategory.mk n.val, Nat.le_of_lt_succ n.isLt⟩
private def boundaryProperty {r : ℕ} (n : Fin (r + 1)) :
    ObjectProperty (Over (truncDegree n)) := fun a ↦ a.left.obj.len < n.val
private abbrev TruncatedBoundary {r : ℕ} (n : Fin (r + 1)) :=
  (boundaryProperty n).FullSubcategory
private def boundaryObject {r : ℕ} (n : Fin (r + 1))
    (Δ : SimplexCategory.Truncated r) (h : Δ.obj.len < n.val)
    (θ : Δ.obj ⟶ SimplexCategory.mk n.val) : TruncatedBoundary n :=
  ⟨Over.mk (SimplexCategory.Truncated.Hom.tr θ Δ.property
    (Nat.le_of_lt_succ n.isLt)), h⟩
private def boundaryDiagram {C : Type*} [Category* C] {r : ℕ}
    (S : (SimplexCategory.Truncated r)ᵒᵖ ⥤ C) (n : Fin (r + 1)) :
    (TruncatedBoundary n)ᵒᵖ ⥤ C :=
  ((boundaryProperty n).ι ⋙ Over.forget (truncDegree n)).op ⋙ S
private theorem truncatedHomFinite {r : ℕ} (a b : SimplexCategory.Truncated r) :
    Finite (a ⟶ b) := by
  apply Finite.of_injective (fun f : a ⟶ b ↦ f.hom)
  intro f g h
  exact SimplexCategory.Truncated.Hom.ext _ _
    (congrArg SimplexCategory.Hom.toOrderHom h)
private theorem boundaryFinite {r : ℕ} [Finite (SimplexCategory.Truncated r)]
    (n : Fin (r + 1)) :
    Finite (TruncatedBoundary n) := by
  have : ∀ a b : SimplexCategory.Truncated r, Finite (a ⟶ b) := truncatedHomFinite
  have : Finite (Over (truncDegree n)) := Finite.of_surjective
    (fun a : Σ Δ : SimplexCategory.Truncated r, Δ ⟶ truncDegree n ↦ Over.mk a.2)
    (fun a ↦ ⟨⟨a.left, a.hom⟩, rfl⟩)
  exact Finite.of_injective (fun a : TruncatedBoundary n ↦ a.obj)
    (fun _ _ h ↦ ObjectProperty.FullSubcategory.ext h)
private theorem boundaryHomFinite {r : ℕ} (n : Fin (r + 1))
    (a b : TruncatedBoundary n) : Finite (a ⟶ b) := by
  apply Finite.of_injective (fun f : a ⟶ b ↦ f.hom.left.hom)
  intro f g h
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact SimplexCategory.Truncated.Hom.ext _ _
    (congrArg SimplexCategory.Hom.toOrderHom h)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A truncated diagram of qcqs étale schemes has qcqs matching schemes.
Source: the finite matching-limit paragraph of the blueprint finite-hypercover-descent proof.
(auxiliary; not a blueprint node)

Proof: work in the full subcategory of qcqs étale schemes. It has a terminal object and
scheme fibre products, and its inclusion in schemes over X preserves finite limits.
For degree n take the finite category of all arrows from lower-dimensional simplices to n.
The limit of the restricted contravariant simplicial diagram gives the matching scheme.
The limiting projections give the projection maps, and the simplicial maps out of degree n
give the matching map by the limit universal property. The same universal property after
forgetting to schemes over X gives existence and uniqueness for every compatible boundary
family, including the empty family when n is zero. -/
theorem exists_truncated_etale_matching_data (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] {r : ℕ} [Finite (SimplexCategory.Truncated r)]
    (S : SimplicialObject.Truncated X.Etale r)
    (hS : ∀ Δ, CompactSpace (S.obj Δ).left ∧ QuasiSeparatedSpace (S.obj Δ).left) :
    Nonempty (TruncatedEtaleMatchingData X r S) := by
  classical
  obtain ⟨hfin, hpres⟩ := qcqs_finite_limits X
  let := hfin
  let := hpres
  let C := (etaleQcqs X).FullSubcategory
  let S' : (SimplexCategory.Truncated r)ᵒᵖ ⥤ C := (etaleQcqs X).lift S hS
  let E : C ⥤ Over X := (etaleQcqs X).ι ⋙ Scheme.Etale.forget X
  let (n : Fin (r + 1)) : FinCategory (TruncatedBoundary n) :=
    ⟨@Fintype.ofFinite _ (boundaryFinite n),
      fun a b ↦ @Fintype.ofFinite _ (boundaryHomFinite n a b)⟩
  let G (n : Fin (r + 1)) := boundaryDiagram S' n
  let M (n : Fin (r + 1)) := limit (G n)
  let π (n : Fin (r + 1)) (Δ : SimplexCategory.Truncated r) (h : Δ.obj.len < n.val)
      (θ : Δ.obj ⟶ SimplexCategory.mk n.val) : (M n).obj ⟶ S.obj (op Δ) :=
    (etaleQcqs X).ι.map (limit.π (G n) (op (boundaryObject n Δ h θ)))
  let μcone (n : Fin (r + 1)) : Cone (G n) :=
    { pt := S'.obj (op (truncDegree n))
      π :=
        { app := fun a ↦ S'.map a.unop.obj.hom.op
          naturality := by
            intro a b f
            change (𝟙 _) ≫ S'.map b.unop.obj.hom.op =
              S'.map a.unop.obj.hom.op ≫ S'.map f.unop.hom.left.op
            erw [Category.id_comp, ← S'.map_comp, ← op_comp]
            exact congrArg (fun t ↦ S'.map t.op) (Over.w f.unop.hom).symm } }
  let μ (n : Fin (r + 1)) : S.obj (op (truncDegree n)) ⟶ (M n).obj :=
    (etaleQcqs X).ι.map (limit.lift (G n) (μcone n))
  refine ⟨{ matching := fun n ↦ (M n).obj
            projection := π
            projection_naturality := ?_
            matching_universal := ?_
            matchingMap := μ
            matchingMap_projection := ?_
            matching_qcqs := fun n ↦ (M n).property }⟩
  · intro n Δ Δ' h h' α θ
    let a := boundaryObject n Δ h θ
    let b := boundaryObject n Δ' h' (α.hom ≫ θ)
    let t : b ⟶ a := ObjectProperty.homMk (Over.homMk α (by rfl))
    have ht := limit.w (G n) t.op
    have ht' := congrArg ((etaleQcqs X).ι.map) ht
    change π n Δ h θ ≫ S.map α.op = π n Δ' h' (α.hom ≫ θ) at ht'
    exact ht'
  · intro n T p hp
    have hc : IsLimit (E.mapCone (limit.cone (G n))) :=
      isLimitOfPreserves E (limit.isLimit (G n))
    let q : Cone (G n ⋙ E) :=
      { pt := T
        π :=
          { app := fun a ↦ p a.unop.obj.left a.unop.property a.unop.obj.hom.hom
            naturality := by
              intro a b f
              change (𝟙 T) ≫ p b.unop.obj.left b.unop.property b.unop.obj.hom.hom =
                p a.unop.obj.left a.unop.property a.unop.obj.hom.hom ≫
                  (Scheme.Etale.forget X).map (S.map f.unop.hom.left.op)
              erw [Category.id_comp,
                hp _ _ a.unop.property b.unop.property f.unop.hom.left _]
              congr 1
              exact congrArg (fun t ↦ t.hom) (Over.w f.unop.hom).symm } }
    refine ⟨hc.lift q, ?_, ?_⟩
    · intro Δ h θ
      exact hc.fac q (op (boundaryObject n Δ h θ))
    · intro f hf
      apply hc.hom_ext
      intro a
      exact (hf a.unop.obj.left a.unop.property a.unop.obj.hom.hom).trans
        (hc.fac q a).symm
  · intro n Δ h θ
    have ht := limit.lift_π (μcone n) (op (boundaryObject n Δ h θ))
    have ht' := congrArg ((etaleQcqs X).ι.map) ht
    change μ n ≫ π n Δ h θ =
      S.map (SimplexCategory.Truncated.Hom.tr θ Δ.property
        (Nat.le_of_lt_succ n.isLt)).op at ht'
    exact ht'

end AlgebraicGeometry
