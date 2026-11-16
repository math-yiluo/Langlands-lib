import Langlands.Geometry.Analytic.EtaleGeometricPointGeometry
import Langlands.Geometry.Analytic.EtalePointwiseLifting.GeometricInputs
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-! # Étale pullbacks and finite diagrams of geometric points -/

noncomputable section

universe u v uL

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory Limits

/-- Pullbacks along an étale leg exist in the actual localized category,
and the projection obtained by base change is étale. -/
def LocalizedEtalePullbackStatement
    (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  ∀ {A B X : LocalizedCategory.{u, v, v} (K := K)} (f : A ⟶ X) (g : B ⟶ X),
    etale f →
    ∃ (P : LocalizedCategory.{u, v, v} (K := K)) (p : P ⟶ A) (q : P ⟶ B),
      IsPullback p q f g ∧ etale q

/-- The full field-point functor preserves pullback squares having an
étale leg. This is an unproved geometric compatibility statement. -/
def LocalizedEtaleFieldPointPullbackStatement
    (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (L : Type uL) [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [IsAlgClosed L]
    [NormedAlgebra K L] : Prop :=
  ∀ {P A B X : LocalizedCategory.{u, v, v} (K := K)}
    (p : P ⟶ A) (q : P ⟶ B) (f : A ⟶ X) (g : B ⟶ X),
    etale f → IsPullback p q f g →
    IsPullback ((localizedFieldPointFunctor L).map p)
      ((localizedFieldPointFunctor L).map q)
      ((localizedFieldPointFunctor L).map f)
      ((localizedFieldPointFunctor L).map g)

namespace EtaleSite

/-- The standard localized geometric inputs for the finite-diagram
part of the geometric-point theorem. No proofs of the inputs are supplied. -/
def GeometricPointFiniteDiagramInputsStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K],
    LocalizedEtaleStabilityStatement.{u, v} K ∧
      LocalizedEtalePullbackStatement.{u, v} K ∧
      ∀ (L : Type uL) [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
        [IsAlgClosed L] [NormedAlgebra K L],
        LocalizedEtaleFieldPointPullbackStatement.{u, v, uL} K L

/-- An étale pullback and its field-point compatibility supply a common
refinement containing the two prescribed field-valued points. -/
theorem geometricPointRefinement_of_etalePullbacks
    (h : GeometricPointFiniteDiagramInputsStatement.{u, v, uL}) :
    GeometricPointRefinementStatement.{u, v, uL} := by
  intro K _ _ _ L _ _ _ _ _ X U V p q hpq
  obtain ⟨hstable, hbase, hfield⟩ := h K
  have := hstable.1
  obtain ⟨P, a, b, hP, hb⟩ := hbase U.hom V.hom U.prop
  let W : EtaleSite X := MorphismProperty.Over.mk ⊤ (b ≫ V.hom)
    ((etale (K := K)).comp_mem b V.hom hb V.prop)
  let a' : W ⟶ U := MorphismProperty.Over.homMk a hP.w
  let b' : W ⟶ V := MorphismProperty.Over.homMk b
  obtain ⟨r, hr₁, hr₂⟩ := Types.exists_of_isPullback
    (hfield L a b U.hom V.hom U.prop hP) p q hpq
  exact ⟨W, a', b', r, hr₁, hr₂⟩

/-- Pulling back the étale diagonal equalizes parallel site arrows at
any field-valued point on which they agree. -/
theorem geometricPointEqualization_of_etalePullbacks
    (h : GeometricPointFiniteDiagramInputsStatement.{u, v, uL}) :
    GeometricPointEqualizationStatement.{u, v, uL} := by
  intro K _ _ _ L _ _ _ _ _ X U V f g p hfg
  obtain ⟨hstable, hbase, hfield⟩ := h K
  have := hstable.1
  have := hstable.2
  let F := localizedFieldPointFunctor (K := K) L
  obtain ⟨P, a, b, hP, hb⟩ := hbase V.hom V.hom V.prop
  obtain ⟨d, hd₁, hd₂⟩ := hP.exists_lift (𝟙 V.left) (𝟙 V.left) rfl
  have hd : etale d := by
    apply (etale (K := K)).of_postcomp d b hb
    rw [hd₂]
    exact etale_of_isIso _
  obtain ⟨c, hc₁, hc₂⟩ := hP.exists_lift f.left g.left
    ((MorphismProperty.Over.w f).trans (MorphismProperty.Over.w g).symm)
  have he : F.map d (F.map f.left p) = F.map c p := by
    apply Types.ext_of_isPullback (hfield L a b V.hom V.hom V.prop hP)
    · rw [← F.map_comp_apply, hd₁, F.map_id_apply,
        ← F.map_comp_apply, hc₁]
    · rw [← F.map_comp_apply, hd₂, F.map_id_apply,
        ← F.map_comp_apply, hc₂]
      exact hfg
  obtain ⟨E, s, t, hE, ht⟩ := hbase d c hd
  obtain ⟨q, -, hq⟩ := Types.exists_of_isPullback
    (hfield L s t d c hd hE) (F.map f.left p) p he
  let W : EtaleSite X := MorphismProperty.Over.mk ⊤ (t ≫ U.hom)
    ((etale (K := K)).comp_mem t U.hom ht U.prop)
  let k : W ⟶ U := MorphismProperty.Over.homMk t
  refine ⟨W, k, q, ?_, hq⟩
  apply MorphismProperty.Over.Hom.ext
  change t ≫ f.left = t ≫ g.left
  have ht₁ : t ≫ f.left = s := by
    rw [← hc₁, ← Category.assoc, ← hE.w, Category.assoc, hd₁, Category.comp_id]
  have ht₂ : t ≫ g.left = s := by
    rw [← hc₂, ← Category.assoc, ← hE.w, Category.assoc, hd₂, Category.comp_id]
  exact ht₁.trans ht₂.symm

/-- Étale pullbacks and image lifting imply the exact geometric-point
target, with all geometric premises retained explicitly. -/
theorem geometricPointStatement_of_etalePullbacks_and_imageLift
    (h : GeometricPointFiniteDiagramInputsStatement.{u, v, uL})
    (hlift : GeometricPointImageLiftStatement.{u, v, uL}) :
    GeometricPointStatement.{u, v, uL} :=
  geometricPointStatement_of_geometry
    ⟨geometricPointRefinement_of_etalePullbacks h,
      geometricPointEqualization_of_etalePullbacks h, hlift⟩

end EtaleSite

end Langlands.Analytic.SaturatedAtlasPresentation
