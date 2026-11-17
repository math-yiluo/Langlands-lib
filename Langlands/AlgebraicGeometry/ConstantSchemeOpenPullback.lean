import Langlands.AlgebraicGeometry.ConnectedEtaleCoverRefinement
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_IsZariskiLocalAtTarget_sigmaMap

/-! # Restriction of constant schemes to connected open refinements -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- The coproduct of the pullbacks of an open immersion forms the pullback
of the constant-scheme structure morphism. -/
theorem isPullback_constantScheme_openImmersion
    {U V : Scheme.{u}} (i : V ⟶ U) [IsOpenImmersion i] (I : Type u) :
    IsPullback (Sigma.desc (fun _ : I => 𝟙 V))
      (Limits.Sigma.map (fun _ : I => i)) i (Sigma.desc (fun _ : I => 𝟙 U)) := by
  let : IsOpenImmersion (Limits.Sigma.map (fun _ : I => i)) :=
    P2MW.S_AlgebraicGeometry_IsZariskiLocalAtTarget_sigmaMap.solution
      @IsOpenImmersion _ (fun _ => inferInstance)
  apply IsOpenImmersion.isPullback
  · apply Sigma.hom_ext
    intro j
    simp
  · ext x
    obtain ⟨⟨j, x⟩, rfl⟩ := (sigmaMk (fun _ : I => U)).surjective x
    change (Sigma.desc (fun _ : I => 𝟙 U))
        ((sigmaMk (fun _ : I => U)) ⟨j, x⟩) ∈ Set.range i ↔
      (sigmaMk (fun _ : I => U)) ⟨j, x⟩ ∈ Set.range (Limits.Sigma.map (fun _ : I => i))
    simp only [sigmaMk_mk]
    have hdesc : (Sigma.desc (fun _ : I => 𝟙 U)) (Sigma.ι (fun _ : I => U) j x) = x := by
      rw [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]
      rfl
    rw [hdesc]
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨Sigma.ι (fun _ : I => V) j y, ?_⟩
      rw [← Scheme.Hom.comp_apply, Sigma.ι_map, Scheme.Hom.comp_apply]
    · rintro ⟨y, hy⟩
      obtain ⟨⟨k, y⟩, rfl⟩ := (sigmaMk (fun _ : I => V)).surjective y
      refine ⟨y, ?_⟩
      have h := congrArg (Sigma.desc (fun _ : I => 𝟙 U)) hy
      change i y = (𝟙 U) x
      simpa only [sigmaMk_mk, ← Scheme.Hom.comp_apply, Category.assoc,
        Sigma.ι_map_assoc, Sigma.ι_comp_desc, Category.comp_id] using h

/-- Pulling a constant scheme back to an open subscheme gives the constant
scheme with the same index type. -/
def constantSchemeOpenPullbackIso
    {U V : Scheme.{u}} (i : V ⟶ U) [IsOpenImmersion i] (I : Type u) :
    (Over.pullback i).obj (Over.mk (Sigma.desc (fun _ : I => 𝟙 U))) ≅
      Over.mk (Sigma.desc (fun _ : I => 𝟙 V)) :=
  (Over.isoMk (isPullback_constantScheme_openImmersion i I).flip.isoPullback
    (by simp)).symm

/-- A supplied constant trivialization restricts along any open immersion. -/
def restrictConstantTrivialization
    {S U V : Scheme.{u}} (q : U ⟶ S) (i : V ⟶ U) [IsOpenImmersion i]
    (C : Over S) (I : Type u)
    (e : (Over.pullback q).obj C ≅ Over.mk (Sigma.desc (fun _ : I => 𝟙 U))) :
    (Over.pullback (i ≫ q)).obj C ≅ Over.mk (Sigma.desc (fun _ : I => 𝟙 V)) :=
  (Over.pullbackComp i q).app C ≪≫
    (Over.pullback i).mapIso e ≪≫ constantSchemeOpenPullbackIso i I

/-- A constant trivialization of an étale cover over a Noetherian local
spectrum restricts to its chosen connected open refinement. -/
def connectedEtaleRefinementTrivialization
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (U : Scheme.{u}) (q : U ⟶ Spec (CommRingCat.of R)) [Etale q] [Surjective q]
    (C : Over (Spec (CommRingCat.of R))) (I : Type u)
    (e : (Over.pullback q).obj C ≅ Over.mk (Sigma.desc (fun _ : I => 𝟙 U))) :
    (Over.pullback ((connectedEtaleRefinementOpen R U q).ι ≫ q)).obj C ≅
      Over.mk (Sigma.desc (fun _ : I => 𝟙 ((connectedEtaleRefinementOpen R U q) : Scheme))) :=
  restrictConstantTrivialization q (connectedEtaleRefinementOpen R U q).ι C I e

end Langlands.AlgebraicGeometry
