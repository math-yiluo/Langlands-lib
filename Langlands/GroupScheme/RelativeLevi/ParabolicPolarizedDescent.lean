import Langlands.GroupScheme.RelativeLevi.ParabolicAffineEtaleCover
import Langlands.GroupScheme.RelativeLevi.ParabolicEtaleSheaf
import Langlands.AlgebraicGeometry.Picard.PolarizedSmoothProperDescentStatement

/-! # Reduction of parabolic representability to affine polarized descent -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open Langlands.AlgebraicGeometry.Picard

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.ParabolicSubgroupModuli

variable {S : Scheme.{u}} {G : GroupScheme S} {hG : IsReductive G}

namespace AffineEtaleCoverModel

/-- Coherent actual bundles on the original parabolic families whose universal
bundle on the supplied covering model is ample. -/
structure Polarization (c : AffineEtaleCoverModel hG) where
  lineBundle : PresheafLineBundle (parabolicPresheaf G hG)
  ample : ((lineBundle.baseChange c.baseMap).universal
    (SmoothProperModel.restrictedRepresentation c.baseMap c.model)).IsAmple

/-- The supplied effective polarized-descent theorem descends this same model
and the ample universal line bundle to an affine original base. -/
theorem exists_descendedModel [IsAffine S]
    (hdesc : PolarizedSmoothProperEtaleDescentStatement.{u, u + 1})
    (c : AffineEtaleCoverModel hG) (L : c.Polarization) :
    ∃ d : SmoothProperModel G hG, (L.lineBundle.universal d.represents).IsAmple := by
  obtain ⟨N, e, hs, hp, ha⟩ := hdesc S c.scheme inferInstance c.affine
    c.baseMap c.etale c.surjective (parabolicPresheaf G hG)
    (parabolic_isSheaf_etale G hG) L.lineBundle c.model.scheme
    (SmoothProperModel.restrictedRepresentation c.baseMap c.model)
    c.model.smooth c.model.proper L.ample
  exact ⟨⟨N, e, hs, hp⟩, ha⟩

/-- Choose the descended smooth proper model, retaining ampleness of the
universal bundle from the same coherent line-bundle data. -/
def descend [IsAffine S]
    (hdesc : PolarizedSmoothProperEtaleDescentStatement.{u, u + 1})
    (c : AffineEtaleCoverModel hG) (L : c.Polarization) :
    {d : SmoothProperModel G hG // (L.lineBundle.universal d.represents).IsAmple} :=
  ⟨(c.exists_descendedModel hdesc L).choose,
    (c.exists_descendedModel hdesc L).choose_spec⟩

end AffineEtaleCoverModel

/-- Effective polarized descent together with supplied polarized local models
on affine bases implies the unchanged arbitrary-base parabolic scheme target. -/
theorem relativeParabolicSchemeStatement_of_affinePolarizedModels
    (hdesc : PolarizedSmoothProperEtaleDescentStatement.{u, u + 1})
    (hlocal : ∀ (B : Scheme.{u}) (H : GroupScheme B) (hH : IsReductive H),
      IsAffine B → ∃ c : AffineEtaleCoverModel hH, Nonempty c.Polarization) :
    RelativeParabolicSchemeStatement.{u} := by
  apply relativeParabolicSchemeStatement_iff.mpr
  intro S G hG
  have hd (i : S.affineCover.I₀) : Nonempty
      (SmoothProperModel ((GroupScheme.baseChange (S.affineCover.f i)).obj G)
        (hG.baseChange (S.affineCover.f i))) := by
    obtain ⟨c, ⟨L⟩⟩ := hlocal (S.affineCover.X i)
      ((GroupScheme.baseChange (S.affineCover.f i)).obj G)
      (hG.baseChange (S.affineCover.f i)) inferInstance
    exact ⟨(c.descend hdesc L).val⟩
  let d := SmoothProperModel.zariskiGlue (hG := hG) S.affineCover (fun i => Classical.choice (hd i))
  exact ⟨d.scheme, ⟨d.represents⟩, d.smooth, d.proper⟩

end Langlands.GroupScheme.ParabolicSubgroupModuli
