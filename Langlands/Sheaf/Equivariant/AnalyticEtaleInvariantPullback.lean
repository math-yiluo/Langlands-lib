import Langlands.Cohomology.AnalyticGaloisSiteCover
import Langlands.Sheaf.ImagePullbackContinuity
import Langlands.Sheaf.Equivariant.AnalyticEtaleRefinements
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-! # Equivariant pullback of sheaves along an invariant étale morphism -/

noncomputable section

universe u v z a b

namespace Langlands.Analytic.SaturatedAtlasPresentation.EtaleSite

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Langlands.Sheaf (HasImagePullbacks)

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X Y : LocalizedCategory.{u, v, v} (K := K)}

variable {f : X ⟶ Y} (hf : etale f)

/-- Compose the structure map of an analytic étale object with an étale map of bases. -/
abbrev postcomposeEtale : EtaleSite X ⥤ EtaleSite Y := MorphismProperty.Over.map ⊤ hf

private theorem postcomposeEtale_hasImagePullbacks : HasImagePullbacks (postcomposeEtale hf) := by
  intro W U V a b
  obtain ⟨P, p, q, hpq, hq⟩ := localizedEtalePullbackBaseChange a.left b.left (etale_left a)
  let T : EtaleSite X := MorphismProperty.Over.mk ⊤ (q ≫ V.hom) (etale_comp hq V.prop)
  have hp : p ≫ U.hom = q ≫ V.hom := by
    rw [← MorphismProperty.Over.w a, ← MorphismProperty.Over.w b,
      ← Category.assoc, ← Category.assoc, hpq.w]
  let π₁ : T ⟶ U := MorphismProperty.Over.homMk p hp
  let π₂ : T ⟶ V := MorphismProperty.Over.homMk q rfl
  refine ⟨T, π₁, π₂, MorphismProperty.Over.Hom.ext hpq.w, ?_⟩
  apply IsPullback.of_map_of_faithful
    (F := MorphismProperty.Over.forget etale ⊤ Y ⋙ Over.forget Y)
  exact hpq

/-- Postcomposition is continuous for the analytic étale topologies. -/
instance postcomposeEtale_isContinuous :
    (postcomposeEtale hf).IsContinuous (etaleTopology X) (etaleTopology Y) := by
  apply (postcomposeEtale_hasImagePullbacks hf).isContinuous
  rintro U R hR
  obtain ⟨I, V, a, rfl⟩ := R.exists_eq_ofArrows
  rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows, ofArrows_mem_etalePrecoverage_iff]
  exact (ofArrows_mem_etalePrecoverage_iff (V := V) (f := a)).mp hR

end Langlands.Analytic.SaturatedAtlasPresentation.EtaleSite

namespace Langlands.Sheaf.Equivariant.Analytic

open _root_.CategoryTheory Opposite Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X Y : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
  {f : X ⟶ Y} (hf : etale f) (hInvariant : ∀ g : G, (ρ g).asIso.hom ≫ f = f)

/-- Over an invariant base map all twisted arrows become ordinary arrows over the
coarse analytic base. On objects compose their structure maps with `f`. -/
def invariantEtaleSitePostcompose : TwistedOver etale ρ ⥤ EtaleSite Y where
  obj U := MorphismProperty.Over.mk ⊤ (U.hom ≫ f) (etale_comp U.obj.prop hf)
  map {U V} g := MorphismProperty.Over.homMk g.left (by
    change g.left ≫ V.hom ≫ f = U.hom ≫ f
    rw [← Category.assoc, g.w, Category.assoc, hInvariant])
  map_id _ := MorphismProperty.Over.Hom.ext rfl
  map_comp _ _ := MorphismProperty.Over.Hom.ext rfl

variable (A : Type a) [Category.{b} A]

/-- Pull back a sheaf on the invariant base to a sheaf with an action. On every
ordinary or twisted test object this is the same composition of structure maps. -/
def invariantEtaleSheafPullback : Sheaf (etaleTopology Y) A ⥤ Sheaf (twistedEtaleTopology ρ) A :=
  ObjectProperty.lift _
    (sheafToPresheaf (etaleTopology Y) A ⋙
      (Functor.whiskeringLeft (TwistedOver etale ρ)ᵒᵖ (EtaleSite Y)ᵒᵖ A).obj
        (invariantEtaleSitePostcompose ρ hf hInvariant).op)
    (fun F => (isSheaf_iff_isSheaf_comp (etaleTopology X) _).2
      ((EtaleSite.postcomposeEtale hf).op_comp_isSheaf (etaleTopology X) (etaleTopology Y) F))

/-- Forgetting the action identifies this pullback with ordinary étale restriction. -/
def invariantEtaleSheafPullbackRestrictionIso :
    invariantEtaleSheafPullback ρ hf hInvariant A ⋙
        TwistedOver.restriction ρ (etaleTopology X) A ≅
      (EtaleSite.postcomposeEtale hf).sheafPushforwardContinuous A (etaleTopology X) (etaleTopology Y) :=
  NatIso.ofComponents (fun _ => ObjectProperty.isoMk _ (Iso.refl _))
    (fun _ => Sheaf.hom_ext ((Category.comp_id _).trans (Category.id_comp _).symm))

/-- For a discrete group, the pullback along an invariant étale morphism lands
in locally discrete sheaves whenever the admissible tests cover. -/
def invariantEtaleGSheafPullback {FA : A → A → Type*} {CA : A → Type*}
    [∀ U V, FunLike (FA U V) (CA U) (CA V)] [ConcreteCategory A FA]
    [TopologicalSpace G] [DiscreteTopology G]
    (hCovers : (distinguishedLiftSystem ρ).Covers (twistedEtaleTopology ρ)) :
    Sheaf (etaleTopology Y) A ⥤ EtaleGSheaf ρ A :=
  ((distinguishedLiftSystem ρ).smoothSheafProperty A (twistedEtaleTopology ρ)).lift
    (invariantEtaleSheafPullback ρ hf hInvariant A)
    (fun F => (distinguishedLiftSystem ρ).isLocallyDiscrete_of_discreteTopology hCovers
      ((invariantEtaleSheafPullback ρ hf hInvariant A).obj F).obj)

end Langlands.Sheaf.Equivariant.Analytic
