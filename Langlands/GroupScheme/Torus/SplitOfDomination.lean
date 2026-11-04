import Langlands.GroupScheme.Torus.PointedMorphismDescent
import Langlands.GroupScheme.Torus.SplittingAssembly
import Langlands.GroupScheme.Torus.Geometry
import Langlands.AlgebraicGeometry.SmoothReducedProof
import Langlands.GroupScheme.Rational.SplitTorusImageDominant
import Langlands.GroupScheme.Rational.TorusDominationBaseChange

/-! # Tori dominated by split tori -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k]

namespace SplitTorusImage

variable {D : CommGroupScheme (Spec (CommRingCat.of k))}
    {H : GroupScheme (Spec (CommRingCat.of k))} {φ : D.toGrp ⟶ H}

/-- A schematically dominant homomorphism fills its closed split-torus image. -/
theorem DominantFactorization.isIso_inclusion (F : DominantFactorization φ)
    (hd : IsSchemeTheoreticallyDominant φ.hom.hom.left) : IsIso F.inclusion := by
  let : IsClosedImmersion F.inclusion.hom.hom.left := F.isSplitSubtorus.2
  have hker : F.inclusion.hom.hom.left.ker = ⊥ := by
    apply le_bot_iff.mp
    calc
      F.inclusion.hom.hom.left.ker ≤
          (F.factor.hom.hom.left ≫ F.inclusion.hom.hom.left).ker :=
        Scheme.Hom.le_ker_comp _ _
      _ = φ.hom.hom.left.ker := by
        change (F.factor ≫ F.inclusion).hom.hom.left.ker = _
        rw [F.factor_comp]
      _ = ⊥ := hd.ker_eq_bot
  have : IsIso F.inclusion.hom.hom.left :=
    IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker
  have : IsIso ((Over.forget _).map F.inclusion.hom.hom) := by
    change IsIso F.inclusion.hom.hom.left
    infer_instance
  have : IsIso F.inclusion.hom.hom :=
    isIso_of_reflects_iso _ (Over.forget _)
  let e : F.image.toGrp ≅ H := Grp.mkIso' (asIso F.inclusion.hom.hom)
  change IsIso e.hom
  infer_instance

/-- A dominant split-torus image factorization whose closed inclusion has
been identified as an actual group-scheme isomorphism. -/
structure DominantPresentation (φ : D.toGrp ⟶ H) extends DominantFactorization φ where
  inclusionIso : image.toGrp ≅ H
  inclusionIso_hom : inclusionIso.hom = inclusion

end SplitTorusImage

/-- Retain the actual split image, factor map and target isomorphism of a
schematically dominant homomorphism from a split torus. -/
def IsSplitTorus.dominantPresentation
    {D : CommGroupScheme (Spec (CommRingCat.of k))}
    (hD : IsSplitTorus D.toGrp)
    {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]
    (φ : D.toGrp ⟶ H) (hd : IsSchemeTheoreticallyDominant φ.hom.hom.left) :
    SplitTorusImage.DominantPresentation φ :=
  let F := hD.dominantFactorization φ
  letI := F.isIso_inclusion hd
  { F with inclusionIso := asIso F.inclusion, inclusionIso_hom := rfl }

/-- Every affine group scheme that is a schematically dominant homomorphic
image of a split torus is itself a split torus. -/
theorem IsSplitTorus.of_schematicallyDominant_hom
    {D H : GroupScheme (Spec (CommRingCat.of k))}
    (hD : IsSplitTorus D) [IsAffineHom H.X.hom]
    (φ : D ⟶ H) (hd : IsSchemeTheoreticallyDominant φ.hom.hom.left) :
    IsSplitTorus H := by
  obtain ⟨I, hI, ⟨eD⟩⟩ := hD
  have : IsIso eD.inv.hom.hom.left :=
    (Over.forget _).map_isIso eD.inv.hom.hom
  let := hd
  have hd' : IsSchemeTheoreticallyDominant (eD.inv ≫ φ).hom.hom.left := by
    change IsSchemeTheoreticallyDominant (eD.inv.hom.hom.left ≫ φ.hom.hom.left)
    infer_instance
  let F := (isSplitTorus_splitTorus (S := Spec (CommRingCat.of k)) I).dominantPresentation
    (D := splitTorus.commGroupScheme _ I) (eD.inv ≫ φ) hd'
  exact IsSplitTorus.of_iso F.inclusionIso.symm F.isSplitSubtorus.1

variable {D H : GroupScheme (Spec (CommRingCat.of k))}

/-- A pointed schematically dominant scheme morphism from a split torus
to a torus forces the target torus to be split. -/
theorem IsTorus.isSplitTorus_of_pointed_schematicallyDominant_morphism
    (hH : IsTorus H) (hD : IsSplitTorus D)
    (p : D.X ⟶ H.X) (hp : η[D.X] ≫ p = η[H.X])
    (hd : IsSchemeTheoreticallyDominant p.left) : IsSplitTorus H := by
  let : IsAffine H.X.left := SplittingAssembly.isAffine_of_isTorus H hH
  let : IsAffineHom H.X.hom := inferInstance
  exact hD.of_schematicallyDominant_hom (hD.isTorus.homOfPointedMorphism hH p hp) hd

/-- Dominance suffices for a torus target because a torus over a field is
smooth and hence reduced. -/
theorem IsTorus.isSplitTorus_of_pointed_dominant_morphism
    (hH : IsTorus H) (hD : IsSplitTorus D)
    (p : D.X ⟶ H.X) (hp : η[D.X] ≫ p = η[H.X])
    (hd : IsDominant p.left) : IsSplitTorus H := by
  let : Smooth H.X.hom := hH.smooth
  let : IsReduced H.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k H.X.left H.X.hom
  let := hd
  exact hH.isSplitTorus_of_pointed_schematicallyDominant_morphism hD p hp
    (IsSchemeTheoreticallyDominant.of_isDominant p.left)

/-- The torus case of pointed split-torus domination is exactly splitness. -/
theorem HasPointedSplitTorusDomination.isSplitTorus
    (h : HasPointedSplitTorusDomination H) (hH : IsTorus H) : IsSplitTorus H := by
  obtain ⟨D, p, hD, hd, hp⟩ := h
  have hp' : η[D.X] ≫ p = η[H.X] := by
    change (1 : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ D.X) ≫ p =
      (1 : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X) at hp
    simpa only [Hom.one_def, SemiCartesianMonoidalCategory.toUnit_unit,
      Category.id_comp] using hp
  exact hH.isSplitTorus_of_pointed_dominant_morphism hD p hp' hd

end Langlands.GroupScheme
