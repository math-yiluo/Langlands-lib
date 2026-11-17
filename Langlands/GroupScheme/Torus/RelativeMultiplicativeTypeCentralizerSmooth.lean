import Langlands.GroupScheme.Torus.RelativeCentralizerSmooth
import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.GroupScheme.Torus.DiagonalizableBaseChange
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.Torus.MaximalBaseChangeForwardReduction
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Langlands.AlgebraicGeometry.Morphisms.FppfLocalAtTarget

/-! # Smoothness of supplied multiplicative-type centralizer representatives -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.AlgebraicGeometry

/-- Smoothness is detected on arbitrary small fppf covering families of the base. -/
theorem smooth_of_fppf_cover_pullbacks {S X : Scheme.{u}}
    (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage S) (f : X ⟶ S)
    (h : ∀ k, Smooth (pullback.snd f (𝒰.f k))) : Smooth f := by
  have : MorphismProperty.IsLocalAtTarget (@Smooth : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
    FppfLocal.isLocalAtTarget_fppfPrecoverage _
  exact MorphismProperty.IsLocalAtTarget.of_zeroHypercover 𝒰 h

end Langlands.AlgebraicGeometry

namespace Langlands.GroupScheme

open RelativeMultiplicativeType

/-- Choose an actual smooth closed centralizer over a ring for an arbitrary
homomorphism from a diagonalizable commutative group. -/
def diagonalizableSmoothCentralizerModelOverSpec
    {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} {H : CommGroupScheme (Spec R)}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : H.toGrp ⟶ G) (hH : IsDiagonalizable H.toGrp) :
    Σ C : GroupScheme (Spec R), {c : C ⟶ G // IsClosedSubgroup c ∧
      Smooth C.X.hom ∧ (torusCentralizer i).IsRepresentedBy c} := by
  apply Classical.choice
  obtain ⟨M, _, _, ⟨e⟩⟩ := hH
  let e' : H.toGrp ≅ (Diagonalizable.groupScheme R M).toGrp :=
    e ≪≫ Diagonalizable.baseChangeIso (Gm.toSpecZ (Spec R)) M
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨C, c, hc, hC, hrep⟩ :=
    diagonalizableCentralizer_hasSmoothClosedRepresentative_overRing
      (e'.inv ≫ i) (inferInstance : Smooth G.X.hom)
  rw [torusCentralizer_eq_centralizer_range] at hrep
  change (SubgroupFunctor.range (e'.symm.hom ≫ i)).centralizer.IsRepresentedBy c at hrep
  rw [SubgroupFunctor.range_iso_comp e'.symm i] at hrep
  rw [← torusCentralizer_eq_centralizer_range] at hrep
  exact ⟨⟨C, c, hc, hC, hrep⟩⟩

/-- Over a ring, every representative of a diagonalizable centralizer is smooth
when the ambient group is smooth affine. -/
theorem diagonalizableCentralizer_smooth_overSpec
    {R : CommRingCat.{u}} {G Z : GroupScheme (Spec R)} {H : CommGroupScheme (Spec R)}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : H.toGrp ⟶ G) (hH : IsDiagonalizable H.toGrp) (z : Z ⟶ G)
    (hz : (torusCentralizer i).IsRepresentedBy z) : Smooth Z.X.hom := by
  obtain ⟨C, c, _, hC, hrep⟩ := diagonalizableSmoothCentralizerModelOverSpec i hH
  exact smooth_of_over_iso ((Grp.forget _).mapIso (hz.isoOfIsRepresentedBy hrep)) hC

/-- The same smoothness assertion over an arbitrary base for diagonalizable
subgroups; no immersion hypothesis on the original map is needed. -/
theorem diagonalizableCentralizer_smooth
    {S : Scheme.{u}} {G Z : GroupScheme S} {H : CommGroupScheme S}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : H.toGrp ⟶ G) (hH : IsDiagonalizable H.toGrp) (z : Z ⟶ G)
    (hz : (torusCentralizer i).IsRepresentedBy z) :
    Smooth Z.X.hom := by
  let 𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage S :=
    S.affineOpenCover.openCover.changeProp (Q := @Flat ⊓ @LocallyOfFinitePresentation)
      (fun _ => ⟨inferInstance, inferInstance⟩)
  apply Langlands.AlgebraicGeometry.smooth_of_fppf_cover_pullbacks 𝒰
  intro k
  let b := S.affineOpenCover.f k
  let B := GroupScheme.baseChange b
  let : Smooth (B.obj G).X.hom := MorphismProperty.pullback_snd G.X.hom b inferInstance
  let : IsAffineHom (B.obj G).X.hom :=
    MorphismProperty.pullback_snd G.X.hom b inferInstance
  have hz' := hz.baseChange b
  rw [← torusCentralizer_baseChange] at hz'
  exact diagonalizableCentralizer_smooth_overSpec (H := (CommGroupScheme.baseChange b).obj H) (B.map i) (hH.baseChange b) (B.map z) hz'

/-- Every supplied representative of the centralizer of a multiplicative-type
group in a smooth affine group is smooth over the original arbitrary base. -/
theorem relativeMultiplicativeTypeCentralizer_smooth
    {S : Scheme.{u}} {G Z : GroupScheme S} {H : CommGroupScheme S}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : H.toGrp ⟶ G) (hH : IsMultiplicativeType H.toGrp) (z : Z ⟶ G)
    (hz : (torusCentralizer i).IsRepresentedBy z) :
    Smooth Z.X.hom := by
  obtain ⟨𝒰, h𝒰⟩ := hH
  apply Langlands.AlgebraicGeometry.smooth_of_fppf_cover_pullbacks 𝒰
  intro k
  let b := 𝒰.f k
  let B := GroupScheme.baseChange b
  let : Smooth (B.obj G).X.hom := MorphismProperty.pullback_snd G.X.hom b inferInstance
  let : IsAffineHom (B.obj G).X.hom :=
    MorphismProperty.pullback_snd G.X.hom b inferInstance
  have hz' := hz.baseChange b
  rw [← torusCentralizer_baseChange] at hz'
  exact diagonalizableCentralizer_smooth (H := (CommGroupScheme.baseChange b).obj H) (B.map i) (h𝒰 k) (B.map z) hz'

end Langlands.GroupScheme
