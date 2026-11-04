import Langlands.GroupScheme.Rational.SplitSemidirectSeries
import Langlands.GroupScheme.HomImage
import Langlands.GroupScheme.Reductive.SplitUnipotentRadicalMaximal

/-! # Split unipotence of smooth affine surjective images -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]

/-- The published schematic-image theorem discharges the image hypothesis
used by the split-series induction. -/
theorem SplitSemidirect.homImageHypothesis : SplitSemidirect.HomImageHypothesis k := by
  intro A G φ hAs hAc hAa hGs hGa
  let : Smooth A.X.hom := hAs
  let : ConnectedSpace A.X.left := hAc
  let : IsAffineHom A.X.hom := hAa
  let : Smooth G.X.hom := hGs
  let : IsAffineHom G.X.hom := hGa
  obtain ⟨D, inc, fac, hc, heq, hf, hs, hqc, _hlfp, hsm, hconn, haff⟩ :=
    HomImage.exists_image φ
  exact ⟨D, inc, fac, hc, heq, hf, hs, hqc, hsm, hconn, haff⟩

variable {U Q : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth U.X.hom] [ConnectedSpace U.X.left] [IsAffineHom U.X.hom]
    [Smooth Q.X.hom] [IsAffineHom Q.X.hom]

/-- A smooth affine surjective image of a smooth connected affine split
unipotent group is split unipotent. No rational-point surjectivity is assumed. -/
theorem IsSplitUnipotent.of_surjective_to_smooth_affine (hU : IsSplitUnipotent U)
    (q : U ⟶ Q) [Surjective q.hom.hom.left] : IsSplitUnipotent Q := by
  let N : GroupScheme (Spec (CommRingCat.of k)) :=
    Grp.trivial (Over (Spec (CommRingCat.of k)))
  let j : N ⟶ Q := 0
  have hj := SplitUnipotentRadicalExistence.trivial_isSplitCandidate Q
  let : Smooth N.X.hom := hj.smooth
  let : ConnectedSpace N.X.left := hj.connectedSpace
  have hsnd : Surjective (snd N.X U.X).left := by
    change Surjective (pullback.snd (𝟙 (Spec (CommRingCat.of k))) U.X.hom)
    infer_instance
  have hjone : fst N.X U.X ≫ j.hom.hom = 1 := by
    have h : fst N.X U.X = (1 : N.X ⊗ U.X ⟶ N.X) :=
      isTerminalTensorUnit.hom_ext _ _
    rw [h, MonObj.one_comp]
  have hmul : SplitSemidirect.mulPoints j q = snd N.X U.X ≫ q.hom.hom := by
    rw [SplitSemidirect.mulPoints, hjone, one_mul]
  obtain ⟨n, hn⟩ := hU
  apply SplitSemidirect.isSplitUnipotent_of_surjective
    SplitSemidirect.homImageHypothesis n j q hj.isClosedSubgroup hj.isNormal
    hj.isSplitUnipotent hn
  rw [hmul]
  change Surjective ((snd N.X U.X).left ≫ q.hom.hom.left)
  let : Surjective (snd N.X U.X).left := hsnd
  infer_instance

/-- An actual finite split-series length and its complete represented
Ga-series witness for the supplied smooth affine surjective image. -/
def IsSplitUnipotent.surjectiveImageSeries (hU : IsSplitUnipotent U)
    (q : U ⟶ Q) [Surjective q.hom.hom.left] :
    {n : ℕ // HasSplitSeries n Q} :=
  ⟨(hU.of_surjective_to_smooth_affine q).choose,
    (hU.of_surjective_to_smooth_affine q).choose_spec⟩

end Langlands.GroupScheme.RelativeRoot
