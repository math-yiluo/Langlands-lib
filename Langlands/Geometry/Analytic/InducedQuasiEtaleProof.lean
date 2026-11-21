import Langlands.Geometry.Analytic.LocalizedSigmaComponents
import Langlands.Geometry.Analytic.LocalizedSigmaQuasiEtaleProof
import Langlands.Geometry.Analytic.InducedQuasiEtaleStatement

/-! # Induction preserves étale and quasi-étale morphisms -/

noncomputable section

universe u v z

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {G : Type z} [Group G] (H : Subgroup G)

/-- The underlying morphism of the induced morphism is the morphism out of the disjoint union of
the copies of `X` whose restriction to the copy indexed by `c` is `f` followed by the inclusion
of the copy of `X'` indexed by `c`. -/
theorem inductionFunctor_map_hom_eq_desc
    {X X' : Action (LocalizedCategory.{u, max z v, max z v} (K := K)) H} (f : X ⟶ X') :
    ((inductionFunctor H).map f).hom =
      Cofan.IsColimit.desc (isColimitLocalizedSigmaCofan fun _ : G ⧸ H => X.V)
        fun c => f.hom ≫ copy H X' c := by
  refine copies_hom_ext H X fun c => ?_
  rw [copy_inductionFunctor_map]
  exact (Cofan.IsColimit.fac (isColimitLocalizedSigmaCofan fun _ : G ⧸ H => X.V)
    (fun c => f.hom ≫ copy H X' c) c).symm

/-- Induction preserves quasi-étale morphisms. -/
theorem quasiEtale_inductionFunctor_map
    {X X' : Action (LocalizedCategory.{u, max z v, max z v} (K := K)) H} (f : X ⟶ X')
    (hf : quasiEtale f.hom) : quasiEtale ((inductionFunctor H).map f).hom := by
  rw [inductionFunctor_map_hom_eq_desc]
  exact (sigmaDesc_quasiEtale_etale.{u, v, z} K (G ⧸ H) (fun _ => X.V)
    (inducedAction H X').V _).1 fun c =>
      quasiEtale_comp_of_etale hf (etale_localizedSigmaCofan_inj (fun _ : G ⧸ H => X'.V) c)

/-- Induction preserves étale morphisms. -/
theorem etale_inductionFunctor_map
    {X X' : Action (LocalizedCategory.{u, max z v, max z v} (K := K)) H} (f : X ⟶ X')
    (hf : etale f.hom) : etale ((inductionFunctor H).map f).hom := by
  rw [inductionFunctor_map_hom_eq_desc]
  exact (sigmaDesc_quasiEtale_etale.{u, v, z} K (G ⧸ H) (fun _ => X.V)
    (inducedAction H X').V _).2 fun c =>
      etale_comp hf (etale_localizedSigmaCofan_inj (fun _ : G ⧸ H => X'.V) c)

/-- Proof of `MorphismPropertyStatement`: induction of analytic spaces with group actions
preserves quasi-étale and étale morphisms. -/
theorem inductionFunctor_map_quasiEtale_etale : MorphismPropertyStatement.{u, v, z} :=
  fun _ _ _ _ _ _ H _ _ f =>
    ⟨quasiEtale_inductionFunctor_map H f, etale_inductionFunctor_map H f⟩

end Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace
