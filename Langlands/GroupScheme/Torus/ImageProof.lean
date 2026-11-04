import Langlands.GroupScheme.Torus.ImageStatement
import Langlands.GroupScheme.SchematicImage
import Langlands.GroupScheme.SchematicImageComparison
import Langlands.GroupScheme.Torus.SplittingDescentHelpers
import Langlands.GroupScheme.Torus.MaximalAmbient

/-! # The schematic image of a torus is a torus -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The actual schematic image of a torus in an affine group is a torus. -/
theorem IsTorus.isTorus_schematicImage
    {k : Type u} [Field k]
    {E H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]
    (hE : IsTorus E) (e : E ⟶ H) [QuasiCompact e.hom.hom.left] :
    IsTorus (SchematicImage.image e) := by
  obtain ⟨K, hK, aK, hs⟩ := hE
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have : Flat b := (fieldExtension_fpqc k K).2.1
  let F := GroupScheme.baseChange b
  have : IsAffineHom (F.obj H).X.hom := by
    change IsAffineHom (CategoryTheory.Limits.pullback.snd H.X.hom b)
    infer_instance
  let D : CommGroupScheme (Spec (CommRingCat.of K)) :=
    { F.obj E with comm := hs.isCommMonObj }
  let d := IsSplitTorus.dominantFactorization (D := D) hs (F.map e)
  have : IsSchemeTheoreticallyDominant (F.map (SchematicImage.projection e)).hom.hom.left :=
    isSchemeTheoreticallyDominant_baseChange b (SchematicImage.projection e)
  have : IsSchemeTheoreticallyDominant d.factor.hom.hom.left := d.dominant
  have hi : IsClosedSubgroup (F.map (SchematicImage.inclusion e)) :=
    IsClosedSubgroup.baseChange b (inferInstanceAs
      (IsClosedImmersion (SchematicImage.inclusion e).hom.hom.left))
  have hfac :
      F.map (SchematicImage.projection e) ≫ F.map (SchematicImage.inclusion e) =
        d.factor ≫ d.inclusion := by
    rw [← F.map_comp, SchematicImage.projection_inclusion, d.factor_comp]
  let c := SchematicImage.isoOfDominantFactorizations
    (F.map (SchematicImage.projection e)) d.factor
    (F.map (SchematicImage.inclusion e)) d.inclusion hi d.isSplitSubtorus.2 hfac
  exact ⟨K, hK, aK, IsSplitTorus.of_iso c d.isSplitSubtorus.1⟩

/-- Every homomorphism from a torus factors through its actual closed torus image. -/
theorem torusImageClosedTorusStatement : TorusImageClosedTorusStatement.{u} := by
  intro k _ H _ _ E hE e
  have : QuasiCompact E.X.hom := hE.quasiCompact
  have : QuasiCompact (e.hom.hom.left ≫ H.X.hom) := by
    simpa only [Over.w e.hom.hom] using ‹QuasiCompact E.X.hom›
  have : QuasiCompact e.hom.hom.left := QuasiCompact.of_comp e.hom.hom.left H.X.hom
  have hI : IsTorus (SchematicImage.image e) := hE.isTorus_schematicImage e
  let Z : CommGroupScheme (Spec (CommRingCat.of k)) :=
    { SchematicImage.image e with comm := hI.isCommMonObj }
  exact ⟨Z, SchematicImage.inclusion e, SchematicImage.projection e,
    hI, inferInstanceAs (IsClosedImmersion (SchematicImage.inclusion e).hom.hom.left),
    SchematicImage.projection_inclusion e⟩

end Langlands.GroupScheme
