import Langlands.AlgebraicGeometry.SchemeLimitRelativeFiniteStatement
import Langlands.AlgebraicGeometry.SchemeLimitAffineProof
import Langlands.AlgebraicGeometry.SchemeLimitFiniteProof
import Langlands.AlgebraicGeometry.SchemeLimitRelativeClosedImmersionProof
import Langlands.AlgebraicGeometry.SchemeLimitFiberLoci
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Final

/-! # Proof of relative finite-morphism descent -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AffineLimit

open EtaleEquivalenceRelation.Action.TargetLimit

section AffineTarget

variable {I : Type u} [SmallCategory I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) {S X Y : Scheme.{u}}
  [IsAffine S] [IsAffine Y] [∀ i, IsAffine (D.obj i)]
  (t : D ⟶ (Functor.const I).obj S)
  (a : X ⟶ S) (b : Y ⟶ S) (f : X ⟶ Y) (w : f ≫ b = a)
  [LocallyOfFiniteType f] [QuasiCompact f] [QuasiSeparated f]
  (c : Cone D) (hc : IsLimit c) (p : c.pt ⟶ S)
  (hp : ∀ i, c.π.app i ≫ t.app i = p)

include hc hp in
lemma exists_isFinite_level_of_affine_target
    [IsFinite (baseChangeMap a b f w p)] :
    ∃ i, IsFinite (baseChangeMap a b f w (t.app i)) := by
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  have : IsAffine (pullback p a) :=
    isAffine_of_isAffineHom (baseChangeMap a b f w p)
  have : QuasiCompact a := by rw [← w]; infer_instance
  have : QuasiSeparated a := by rw [← w]; infer_instance
  obtain ⟨i, hi⟩ := exists_isAffine_level D t a c hc p hp
  let E := Over.forget i ⋙ diagram D t a
  let F := Over.forget i ⋙ diagram D t b
  have (j : Over i) : IsAffine (E.obj j) := by
    have : IsAffine ((diagram D t a).obj i) := hi
    have : IsAffineHom ((diagram D t a).map j.hom) :=
      MorphismProperty.of_isPullback (P := @IsAffineHom)
        (diagram_map_isPullback a D t j.hom).flip inferInstance
    exact isAffine_of_isAffineHom ((diagram D t a).map j.hom)
  have (j : Over i) : IsAffine (F.obj j) := by dsimp [F]; infer_instance
  let α : E ⟶ F := Functor.whiskerLeft (Over.forget i) (SchemeLimitModel.Geometry.morphismDiagram a b f w D t)
  let cE := (cone D t a c p hp).whisker (Over.forget i)
  let cF := (cone D t b c p hp).whisker (Over.forget i)
  have hcE : IsLimit cE :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) _).symm
      (isLimitCone D t a c p hp hc)
  have hcF : IsLimit cF :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) _).symm
      (isLimitCone D t b c p hp hc)
  have hf (j : Over i) : cE.π.app j ≫ α.app j =
      baseChangeMap a b f w p ≫ cF.π.app j :=
    cone_baseChangeMap D t a b f w c p hp j.left
  let i₀ : Over i := Over.mk (𝟙 i)
  have : LocallyOfFiniteType (α.app i₀) :=
    locallyOfFiniteType_baseChangeMap a b f w (t.app i)
  have hcart {j : Over i} (r : j ⟶ i₀) :
      IsPullback (E.map r) (α.app j) (α.app i₀) (F.map r) :=
    (SchemeLimitModel.Geometry.morphismDiagram_cartesian a b f w D t r.left).flip
  obtain ⟨j, _, hj⟩ := affineDiagramFiniteDescent E F α cE cF hcE hcF
    (baseChangeMap a b f w p) hf i₀ hcart inferInstance
  exact ⟨j.left, hj⟩

end AffineTarget

section TargetCover

variable {S X Y T : Scheme.{u}}
  (a : X ⟶ S) (b : Y ⟶ S) (f : X ⟶ Y) (w : f ≫ b = a)
  (p : T ⟶ S)

lemma isFinite_of_finite_charts (𝒰 : Y.OpenCover)
    (H : ∀ k, IsFinite
      (baseChangeMap (pullback.snd f (𝒰.f k) ≫ (𝒰.f k ≫ b))
        (𝒰.f k ≫ b) (pullback.snd f (𝒰.f k)) rfl p)) :
    IsFinite (baseChangeMap a b f w p) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsFinite)
    (baseChangeCover b p 𝒰)
  intro k
  let h := chart_isPullback a b f w p (𝒰.f k)
  have : IsFinite
      (baseChangeMap (pullback.snd f (𝒰.f k) ≫ (𝒰.f k ≫ b))
        (𝒰.f k ≫ b) (pullback.snd f (𝒰.f k)) rfl p) := H k
  change IsFinite (pullback.snd (baseChangeMap a b f w p)
    (baseChangeMap (𝒰.f k ≫ b) b (𝒰.f k) rfl p))
  rw [← h.isoPullback_inv_snd]
  infer_instance

end TargetCover

/-- Finiteness is detected at one common stage of the affine limit. -/
theorem relativeFiniteDescent : RelativeFiniteDescent.{u} := by
  intro I _ _ D S X Y _ _ t a b f w _ _ _ _ c hc p hp
  classical
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace b
  let 𝒰 := Y.affineCover.finiteSubcover
  constructor
  · intro H
    let := H
    have hchart (k : 𝒰.I₀) :
        ∃ i, IsFinite
          (baseChangeMap (pullback.snd f (𝒰.f k) ≫ (𝒰.f k ≫ b))
            (𝒰.f k ≫ b) (pullback.snd f (𝒰.f k)) rfl (t.app i)) := by
      let g := pullback.snd f (𝒰.f k)
      let z := g ≫ (𝒰.f k ≫ b)
      have : IsFinite (baseChangeMap z (𝒰.f k ≫ b) g rfl p) :=
        MorphismProperty.of_isPullback (P := @IsFinite)
          (chart_isPullback a b f w p (𝒰.f k)) inferInstance
      exact exists_isFinite_level_of_affine_target D t
        z (𝒰.f k ≫ b) g rfl c hc p hp
    choose j hj using hchart
    obtain ⟨i, hi⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image j)
    let r (k : 𝒰.I₀) : i ⟶ j k := (hi (by simp)).some
    refine ⟨i, isFinite_of_finite_charts a b f w (t.app i) 𝒰 ?_⟩
    intro k
    exact MorphismProperty.of_isPullback (P := @IsFinite)
      (SchemeLimitModel.Geometry.morphismDiagram_cartesian
        (pullback.snd f (𝒰.f k) ≫ (𝒰.f k ≫ b))
        (𝒰.f k ≫ b) (pullback.snd f (𝒰.f k)) rfl D t (r k)).flip (hj k)
  · rintro ⟨i, H⟩
    exact MorphismProperty.of_isPullback (P := @IsFinite)
      (cone_baseChangeMap_isPullback a b f w D t c p hp i).flip H

end Langlands.AlgebraicGeometry.AffineLimit
