import Langlands.GroupScheme.SchematicImageOverGroup
import Langlands.GroupScheme.Torus.RelativeTorusImageProjection
import Langlands.GroupScheme.Torus.RelativeReductive
import Langlands.AbelianScheme.TorsionFiniteEtale

/-! # The image torus of a relative torus homomorphism -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.RelativeTorusImage

open SchematicImageOver

variable {S : Scheme.{u}} {T G : GroupScheme S} (f : T ⟶ G)

/-- Over a flat chart the scheme comparison with the split image is an isomorphism
of group schemes. -/
def groupIsoOfFactorization {U : Scheme.{u}} (b : U ⟶ S)
    [Flat b] [IsAffineHom T.X.hom] [QuasiCompact f.hom.hom.left]
    [Flat (projection f.hom.hom).left] [Surjective (projection f.hom.hom).left]
    (D : SplitTorusImageLocal.Factorization ((baseChange b).map f)) :
    (baseChange b).obj (group f) ≅ D.image.toGrp := by
  let A := (baseChange b).obj (group f)
  let B := D.image.toGrp
  let e : A.X ≅ B.X := isoOfFactorization f b D
  let i := ((baseChange b).map (groupInclusion f)).hom.hom
  let j := D.inclusion.hom.hom
  have hi : IsMonHom i := inferInstanceAs (IsMonHom ((baseChange b).map (groupInclusion f)).hom.hom)
  have hj : IsMonHom j := inferInstanceAs (IsMonHom D.inclusion.hom.hom)
  have : IsClosedImmersion j.left := D.isClosed
  have : Mono j := Over.mono_of_mono_left _
  have he : e.hom ≫ j = i := (isoOfFactorization_spec f b D).1
  refine Grp.mkIso (G := A) (H := B) e ?_ ?_
  · apply (cancel_mono j).mp
    simp only [Category.assoc, he, IsMonHom.one_hom]
  · apply (cancel_mono j).mp
    simp only [Category.assoc, he, IsMonHom.mul_hom i, IsMonHom.mul_hom j,
      tensorHom_comp_tensorHom_assoc]

/-- A map from a relative torus to an affine group locally of finite type factors
through its schematic image, a relative torus, by an fppf projection. -/
theorem exists_factorization {S : Scheme.{u}} {T : CommGroupScheme S} {G : GroupScheme S}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (hT : RelativeTorus.IsTorus T.toGrp) (f : T.toGrp ⟶ G) :
    ∃ (D : CommGroupScheme S) (π : T.toGrp ⟶ D.toGrp) (j : D.toGrp ⟶ G),
      RelativeTorus.IsTorus D.toGrp ∧ IsClosedSubgroup j ∧
        Flat π.hom.hom.left ∧ Surjective π.hom.hom.left ∧
        LocallyOfFinitePresentation π.hom.hom.left ∧ π ≫ j = f := by
  have : IsAffineHom T.toGrp.X.hom := hT.isAffineHom
  have : QuasiCompact (f.hom.hom.left ≫ G.X.hom) := by
    rw [Over.w f.hom.hom]
    infer_instance
  have : QuasiCompact f.hom.hom.left := QuasiCompact.of_comp _ G.X.hom
  obtain ⟨𝒰, h𝒰⟩ := SplitTorusImageLocal.exists_etale_factorizations hT f
  let C (i : 𝒰.I₀) := Classical.choice (h𝒰 i)
  have hp := flat_surjective_of_etale_factorizations f 𝒰 C
  have : Flat (projection f.hom.hom).left := hp.1
  have : Surjective (projection f.hom.hom).left := hp.2
  let D := commGroup f
  let π : T.toGrp ⟶ D.toGrp := groupProjection f
  let j : D.toGrp ⟶ G := groupInclusion f
  have hD : RelativeTorus.IsTorus D.toGrp := by
    refine ⟨𝒰, fun i => ?_⟩
    have : Etale (𝒰.f i) := 𝒰.map_prop i
    exact IsSplitTorus.of_iso (groupIsoOfFactorization f (𝒰.f i) (C i)) (C i).isSplit
  have hi : IsClosedSubgroup j :=
    inferInstanceAs (IsClosedImmersion (inclusion f.hom.hom).left)
  have : Smooth T.toGrp.X.hom := hT.smooth
  have : Smooth D.toGrp.X.hom := hD.smooth
  have : LocallyOfFinitePresentation (π.hom.hom.left ≫ D.toGrp.X.hom) := by
    rw [Over.w π.hom.hom]
    infer_instance
  have hπ : LocallyOfFinitePresentation π.hom.hom.left :=
    Langlands.AlgebraicGeometry.locallyOfFinitePresentation_of_comp _ D.toGrp.X.hom
  exact ⟨D, π, j, hD, hi, hp.1, hp.2, hπ, groupProjection_inclusion f⟩

end Langlands.GroupScheme.RelativeTorusImage
