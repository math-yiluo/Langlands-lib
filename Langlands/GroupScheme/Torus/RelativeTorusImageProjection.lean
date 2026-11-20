import Langlands.GroupScheme.SchematicImageOver
import Langlands.GroupScheme.Torus.RelativeTorusImageLocal
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.AlgebraicGeometry.Morphisms.FppfLocalAtTarget
import Langlands.AlgebraicGeometry.Morphisms.FpqcFiniteDescent

/-! # Faithful flatness onto the schematic image of a relative torus -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.RelativeTorusImage

open SchematicImageOver

variable {S : Scheme.{u}} {T G : GroupScheme S} (f : T ⟶ G)
  [IsAffineHom T.X.hom]

private theorem dominant_projection_of_factorization {U : Scheme.{u}}
    (b : U ⟶ S) (D : SplitTorusImageLocal.Factorization ((baseChange b).map f)) :
    IsSchemeTheoreticallyDominant D.projection.hom.hom.left := by
  have : IsAffineHom ((baseChange b).obj T).X.hom :=
    MorphismProperty.pullback_snd _ _ (inferInstance : IsAffineHom T.X.hom)
  have : IsAffineHom D.image.toGrp.X.hom := D.isSplit.isAffineHom
  have : QuasiCompact (D.projection.hom.hom.left ≫ D.image.toGrp.X.hom) := by
    rw [Over.w D.projection.hom.hom]
    infer_instance
  have : QuasiCompact D.projection.hom.hom.left := QuasiCompact.of_comp _ D.image.toGrp.X.hom
  have : Flat D.projection.hom.hom.left := D.flat
  have : Surjective D.projection.hom.hom.left := D.surjective
  exact dominant_of_flat_surjective _

variable [QuasiCompact f.hom.hom.left]

/-- On a flat chart the canonical image and any split-torus factorization
agree over the target and under the source. -/
theorem exists_iso_of_factorization {U : Scheme.{u}}
    (b : U ⟶ S) [Flat b]
    (D : SplitTorusImageLocal.Factorization ((baseChange b).map f)) :
    ∃ e : (Over.pullback b).obj (image f.hom.hom) ≅ D.image.toGrp.X,
      e.hom ≫ D.inclusion.hom.hom = (Over.pullback b).map (inclusion f.hom.hom) ∧
      (Over.pullback b).map (projection f.hom.hom) ≫ e.hom = D.projection.hom.hom := by
  let B := Over.pullback b
  have : IsClosedImmersion (B.map (inclusion f.hom.hom)).left :=
    MorphismProperty.overPullbackMap b _ (inferInstance : IsClosedImmersion (inclusion f.hom.hom).left)
  have : IsClosedImmersion D.inclusion.hom.hom.left := D.isClosed
  have : Flat (pullback.fst (image f.hom.hom).hom b) :=
    MorphismProperty.pullback_fst _ _ (inferInstance : Flat b)
  have : IsSchemeTheoreticallyDominant (B.map (projection f.hom.hom)).left :=
    IsSchemeTheoreticallyDominant.of_isPullback (HomIsogeny.baseChange_isPullback b (projection f.hom.hom))
  have : IsSchemeTheoreticallyDominant D.projection.hom.hom.left :=
    dominant_projection_of_factorization f b D
  apply exists_iso_of_dominant_factorizations
  rw [← Functor.map_comp, projection_inclusion]
  exact congrArg (fun q => q.hom.hom) D.fac.symm

/-- The comparison isomorphism from the base changed schematic image to the
split torus on a flat chart. -/
def isoOfFactorization {U : Scheme.{u}} (b : U ⟶ S) [Flat b]
    (D : SplitTorusImageLocal.Factorization ((baseChange b).map f)) :
    (Over.pullback b).obj (image f.hom.hom) ≅ D.image.toGrp.X :=
  (exists_iso_of_factorization f b D).choose

theorem isoOfFactorization_spec {U : Scheme.{u}} (b : U ⟶ S) [Flat b]
    (D : SplitTorusImageLocal.Factorization ((baseChange b).map f)) :
    (isoOfFactorization f b D).hom ≫ D.inclusion.hom.hom =
      (Over.pullback b).map (inclusion f.hom.hom) ∧
    (Over.pullback b).map (projection f.hom.hom) ≫ (isoOfFactorization f b D).hom =
      D.projection.hom.hom :=
  (exists_iso_of_factorization f b D).choose_spec

/-- Flatness and surjectivity descend from an étale cover with split-torus
factorizations to the projection onto the canonical schematic image. -/
theorem flat_surjective_of_etale_factorizations
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (D : ∀ i : 𝒰.I₀, SplitTorusImageLocal.Factorization ((baseChange (𝒰.f i)).map f)) :
    Flat (projection f.hom.hom).left ∧ Surjective (projection f.hom.hom).left := by
  have (i : 𝒰.I₀) : Etale (𝒰.f i) := 𝒰.map_prop i
  let I := image f.hom.hom
  let p := projection f.hom.hom
  let 𝒱 : Scheme.Cover Scheme.fppfPrecoverage I.left :=
    Scheme.Cover.changeProp (𝒰.pullback₁ I.hom) (Q := @Flat ⊓ @LocallyOfFinitePresentation)
      (fun i => by
        have : Etale ((𝒰.pullback₁ I.hom).f i) := Scheme.Cover.map_prop (𝒰.pullback₁ I.hom) i
        exact ⟨inferInstance, inferInstance⟩)
  have : MorphismProperty.IsLocalAtTarget (@Flat : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
    Langlands.AlgebraicGeometry.FppfLocal.isLocalAtTarget_fppfPrecoverage _
  have : MorphismProperty.IsLocalAtTarget (@Surjective : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
    Langlands.AlgebraicGeometry.FppfLocal.isLocalAtTarget_fppfPrecoverage _
  change ((@Flat ⊓ @Surjective : MorphismProperty Scheme.{u}) p.left)
  refine MorphismProperty.IsLocalAtTarget.of_zeroHypercover 𝒱 fun i => ?_
  let b := 𝒰.f i
  let e := isoOfFactorization f b (D i)
  let p' := (Over.pullback b).map p
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).mapIso e).hom)
  have hfac : p'.left ≫ e.hom.left = (D i).projection.hom.hom.left :=
    congrArg Over.Hom.left (isoOfFactorization_spec f b (D i)).2
  have hlocal : (@Flat ⊓ @Surjective : MorphismProperty Scheme.{u}) p'.left := by
    rw [← MorphismProperty.cancel_right_of_respectsIso (P := @Flat ⊓ @Surjective) _ e.hom.left,
      hfac]
    exact ⟨(D i).flat, (D i).surjective⟩
  have hp := HomIsogeny.baseChange_isPullback b p
  change (@Flat ⊓ @Surjective : MorphismProperty Scheme.{u})
    (pullback.snd p.left (pullback.fst I.hom b))
  rw [← hp.isoPullback_hom_snd,
    MorphismProperty.cancel_left_of_respectsIso (P := @Flat ⊓ @Surjective)] at hlocal
  exact hlocal

end Langlands.GroupScheme.RelativeTorusImage
