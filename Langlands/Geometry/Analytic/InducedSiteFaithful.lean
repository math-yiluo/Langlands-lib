import Langlands.Geometry.Analytic.InducedEquivariantSite

/-! # Induction on equivariant quasi-étale sites is faithful -/

noncomputable section

universe u v z

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Fold

variable {G : Type z} [Group G] (H : Subgroup G)
  (X : Action (LocalizedCategory.{u, max z v, max z v} (K := K)) H)

/-- The fold morphism `X_{G/H} → X`, the identity on every copy. -/
def foldHom : (copies H X).pt ⟶ X.V :=
  Cofan.IsColimit.desc (isColimitCopies H X) fun _ => 𝟙 X.V

@[reassoc (attr := simp)]
theorem copy_foldHom (c : G ⧸ H) : copy H X c ≫ foldHom H X = 𝟙 X.V :=
  Cofan.IsColimit.fac _ _ c

/-- Every copy inclusion is a split monomorphism, split by the fold morphism. -/
instance isSplitMono_copy (c : G ⧸ H) : IsSplitMono (copy H X c) :=
  IsSplitMono.mk' ⟨foldHom H X, copy_foldHom H X c⟩

/-- Induction of `H`-objects is injective on morphisms: a morphism is recovered from the
restriction of its induction to the copy indexed by the coset `H`. -/
theorem inductionFunctor_map_injective
    {X X' : Action (LocalizedCategory.{u, max z v, max z v} (K := K)) H} {f f' : X ⟶ X'}
    (h : (inductionFunctor H).map f = (inductionFunctor H).map f') : f = f' := by
  have e := copy_inductionFunctor_map H f (baseCoset H)
  rw [h, copy_inductionFunctor_map] at e
  exact Action.Hom.ext ((cancel_mono (copy H X' (baseCoset H))).mp e).symm

instance faithful_inductionFunctor : (inductionFunctor.{u, v} (K := K) H).Faithful where
  map_injective := inductionFunctor_map_injective H

end Fold

variable {G : Type z} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {H : Subgroup G}
  (hH : IsOpen (H : Set G)) (hC : ContinuityStatement.{u, v, z})
  (hQ : MorphismPropertyStatement.{u, v, z}) (X : GSpace.{u, max z v, max z v} K H)

instance faithful_gSpaceInduction : (gSpaceInduction (K := K) hH hC).Faithful where
  map_injective h := ObjectProperty.hom_ext _
    (inductionFunctor_map_injective H (congrArg (fun φ => φ.hom) h))

/-- Induction `Qét(X(H)) ⥤ Qét(X_{G/H}(G))` is faithful. -/
instance faithful_quasiEtaleSiteInduction : (quasiEtaleSiteInduction hH hC hQ X).Faithful where
  map_injective h := MorphismProperty.Over.Hom.ext
    ((gSpaceInduction hH hC).map_injective (congrArg (fun φ => φ.left) h))

end Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace
