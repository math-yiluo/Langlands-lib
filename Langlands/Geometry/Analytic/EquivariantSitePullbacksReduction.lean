import Langlands.CategoryTheory.PullbackActions
import Langlands.Geometry.Analytic.EquivariantSitePullbacksStatement
import Langlands.Geometry.Analytic.LocalizedPullbackCompactPreimages
import Langlands.Geometry.Analytic.LocalizedQuasiEtalePullbackAction
import Langlands.Geometry.Analytic.LocalizedQuasiEtalePullbackExistence
import Langlands.Geometry.Analytic.QuasiEtaleStabilityStatement
import Langlands.Geometry.Analytic.EtaleGeometricPointPullbacks
import Langlands.Geometry.Analytic.LocalizedEtaleComposition
import Langlands.Geometry.Analytic.FullRecognitionEtaleRightCancellationStatement

/-! # Equivariant fibre products from localized analytic pullbacks -/

noncomputable section

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {G : Type z} [Group G] [TopologicalSpace G]

namespace GSpace

variable {A B S : GSpace.{u, v, v} K G} {P : LocalizedCategory.{u, v, v} (K := K)}
  (f : A ⟶ S) (g : B ⟶ S) {p : P ⟶ forget.obj A} {q : P ⟶ forget.obj B}
  (h : IsPullback p q (forget.map f) (forget.map g))

private def pullbackActionOnForget : G →* Aut P :=
  Langlands.CategoricalPullback.pullbackAction h A.obj.ρAut B.obj.ρAut S.obj.ρAut
    f.hom.comm g.hom.comm

/-- Equip a supplied localized pullback with the diagonal `G`-action when the first
cospan leg is quasi-étale. The underlying localized object is unchanged. -/
def pullbackOfForget (hf : SaturatedAtlasPresentation.quasiEtale (forget.map f)) :
    GSpace.{u, v, v} K G := by
  let ρ := pullbackActionOnForget f g h
  let Y : Action (LocalizedCategory.{u, v, v} (K := K)) G := ⟨P, (Aut.toEnd P).comp ρ⟩
  letI : T2Space (localizedSpaceFunctor.obj (forget.obj A)) := A.2.1
  letI : T2Space (localizedSpaceFunctor.obj (forget.obj B)) := B.2.1
  have hρ : Y.ρAut = ρ := by
    apply MonoidHom.ext
    intro a
    exact Aut.ext rfl
  refine ⟨Y, (hasCompactPairPreimages_of_quasiEtale h hf).1, ?_⟩
  rw [hρ]
  exact isContinuousAction_of_isPullback_of_quasiEtale h hf A.2.2 B.2.2
    (Langlands.CategoricalPullback.pullbackAction_fst h _ _ _ f.hom.comm g.hom.comm)
    (Langlands.CategoricalPullback.pullbackAction_snd h _ _ _ f.hom.comm g.hom.comm)

/-- The first analytic projection intertwines the diagonal and first factor actions. -/
def pullbackOfForgetFst (hf : SaturatedAtlasPresentation.quasiEtale (forget.map f)) :
    pullbackOfForget f g h hf ⟶ A :=
  ObjectProperty.homMk ⟨p,
    Langlands.CategoricalPullback.pullbackAction_fst h A.obj.ρAut B.obj.ρAut S.obj.ρAut
      f.hom.comm g.hom.comm⟩

/-- The second analytic projection intertwines the diagonal and second factor actions. -/
def pullbackOfForgetSnd (hf : SaturatedAtlasPresentation.quasiEtale (forget.map f)) :
    pullbackOfForget f g h hf ⟶ B :=
  ObjectProperty.homMk ⟨q,
    Langlands.CategoricalPullback.pullbackAction_snd h A.obj.ρAut B.obj.ρAut S.obj.ρAut
      f.hom.comm g.hom.comm⟩

end GSpace

section Over

variable {Q : MorphismProperty (LocalizedCategory.{u, v, v} (K := K))}
  {X : GSpace.{u, v, v} K G}
  {U₁ U₂ U₃ : (Q.inverseImage GSpace.forget).Over ⊤ X}

private theorem over_w_forget (f : U₁ ⟶ U₃) :
    GSpace.forget.map f.left ≫ GSpace.forget.map U₃.hom = GSpace.forget.map U₁.hom := by
  rw [← GSpace.forget.map_comp, MorphismProperty.Over.w f]

/-- Lift an analytic pullback of a site cospan to the category over the equivariant base.
The quasi-étale first leg supplies the `G`-space structure, and the property `Q` of the
composite through the second projection puts the vertex in the site. -/
theorem exists_equivariantSitePullback_of_isPullback (f₁ : U₁ ⟶ U₃) (f₂ : U₂ ⟶ U₃)
    {P : LocalizedCategory.{u, v, v} (K := K)}
    {p : P ⟶ GSpace.forget.obj U₁.left} {q : P ⟶ GSpace.forget.obj U₂.left}
    (h : IsPullback p q (GSpace.forget.map f₁.left) (GSpace.forget.map f₂.left))
    (hf : quasiEtale (GSpace.forget.map f₁.left)) (hQ : Q (q ≫ GSpace.forget.map U₂.hom)) :
    ∃ (W : (Q.inverseImage GSpace.forget).Over ⊤ X) (p₁ : W ⟶ U₁) (p₂ : W ⟶ U₂),
      IsPullback (GSpace.forget.map p₁.left) (GSpace.forget.map p₂.left)
        (GSpace.forget.map f₁.left) (GSpace.forget.map f₂.left) := by
  let a := GSpace.pullbackOfForgetFst f₁.left f₂.left h hf
  let b := GSpace.pullbackOfForgetSnd f₁.left f₂.left h hf
  let W : (Q.inverseImage GSpace.forget).Over ⊤ X :=
    MorphismProperty.Over.mk ⊤ (b ≫ U₂.hom) (by
      change Q (GSpace.forget.map (b ≫ U₂.hom))
      rw [GSpace.forget.map_comp]
      exact hQ)
  have ha : a ≫ U₁.hom = W.hom := by
    apply GSpace.forget.map_injective
    rw [GSpace.forget.map_comp]
    change p ≫ GSpace.forget.map U₁.hom = GSpace.forget.map (b ≫ U₂.hom)
    rw [GSpace.forget.map_comp]
    change p ≫ GSpace.forget.map U₁.hom = q ≫ GSpace.forget.map U₂.hom
    rw [← over_w_forget f₁, ← over_w_forget f₂, ← Category.assoc, ← Category.assoc, h.w]
  let p₁ : W ⟶ U₁ := MorphismProperty.Over.homMk a ha trivial
  let p₂ : W ⟶ U₂ := MorphismProperty.Over.homMk b rfl trivial
  exact ⟨W, p₁, p₂, h⟩

end Over

/-- Quasi-étale composition, base change and cancellation over a common base
suffice to construct the equivariant quasi-étale site pullbacks. -/
theorem equivariantQuasiEtalePullbacks_of_stability
    (hComp : ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K],
      QuasiEtaleCompStatement.{u, v} K)
    (hBase : ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K],
      QuasiEtaleBaseChangeStatement.{u, v} K)
    (hOver : ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K],
      QuasiEtaleOverMorphismStatement.{u, v} K) :
    EquivariantQuasiEtalePullbacksStatement.{u, v, z} := by
  intro K _ _ _ G _ _ X U₁ U₂ U₃ f₁ f₂
  have hf : quasiEtale (GSpace.forget.map f₁.left) :=
    (hOver K).of_postcomp _ _ U₃.prop ((over_w_forget f₁).symm ▸ U₁.prop)
  obtain ⟨P, p, q, hpq⟩ := exists_localizedPullback_of_quasiEtale
    (GSpace.forget.map f₁.left) (GSpace.forget.map f₂.left) hf
  have hq : quasiEtale q := (hBase K).of_isPullback hpq hf
  exact exists_equivariantSitePullback_of_isPullback f₁ f₂ hpq hf
    ((hComp K).comp_mem _ _ hq U₂.prop)

/-- Localized étale pullback existence with its étale projection, and strong étale
right cancellation, suffice to construct the equivariant étale site pullbacks. -/
theorem equivariantEtalePullbacks_of_localizedPullback
    (hPullback : ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K],
      LocalizedEtalePullbackStatement.{u, v} K)
    (hCancel : ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K],
      AffinoidAtlasPresentation.StrongHom.EtaleRightCancellationStatement.{u, v, v} K) :
    EquivariantEtalePullbacksStatement.{u, v, z} := by
  intro K _ _ _ G _ _ X U₁ U₂ U₃ f₁ f₂
  have hStrong : (strongEtale (K := K) :
      MorphismProperty (SaturatedAtlasPresentation.{u, v, v} K)).HasOfPostcompProperty
        (strongEtale (K := K)) := by
    constructor
    intro A B C f g hg hfg
    unfold strongEtale at hg hfg ⊢
    rw [Functor.map_comp] at hfg
    exact hCancel K _ _ _ _ _ hg hfg
  have hf : etale (GSpace.forget.map f₁.left) :=
    (etale_hasOfPostcompProperty_of_strong hStrong).of_postcomp _ _ U₃.prop
      ((over_w_forget f₁).symm ▸ U₁.prop)
  obtain ⟨P, p, q, hpq, hq⟩ := hPullback K
    (GSpace.forget.map f₁.left) (GSpace.forget.map f₂.left) hf
  exact exists_equivariantSitePullback_of_isPullback f₁ f₂ hpq (etale_le_quasiEtale _ hf)
    (etale_comp hq U₂.prop)

end Langlands.Analytic.SaturatedAtlasPresentation
