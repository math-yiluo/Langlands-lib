import Langlands.GroupScheme.Absolute.ParabolicNormalizerReduction
import Langlands.GroupScheme.SubgroupFunctor.RationalOpenCellNormalizer
import Langlands.GroupScheme.Rational.ParabolicNormalizerStatement
import Langlands.GroupScheme.Absolute.OppositeCellProof
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.GroupScheme.Dynamic.SmoothConnectedStatement
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Dynamic.ParabolicNormalizerSeparation

/-! # All-test parabolic normalization by rational points and fpqc descent -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {P G : GroupScheme (Spec (CommRingCat.of k))}

/-- A dynamic parabolic containing an ambient Borel is self-normalizing on all
tests once the two exact Borel point statements hold. -/
theorem normalizer_eq_of_dynamic_parabolic_and_borel
    [IsAlgClosed k] [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [ConnectedSpace G.X.left] [Smooth P.X.hom] [ConnectedSpace P.X.left]
    (hconj : BorelConjugacyStatement.{u}) (hnorm : BorelNormalizerStatement.{u})
    (i : P ⟶ G) (hi : IsClosedSubgroup i)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hχ : SubgroupFunctor.range i = Dynamic.parabolic χ)
    (B : GroupScheme (Spec (CommRingCat.of k))) (j : B ⟶ G) (f : B ⟶ P)
    (hj : IsBorelSubgroup j) (hf : f ≫ i = j) :
    (SubgroupFunctor.range i).normalizer = SubgroupFunctor.range i := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  let iU := Dynamic.Affine.unipotentHom (Dynamic.oppositeCocharacter χ)
  have hU := Dynamic.Affine.isRepresentedBy_unipotentHom (Dynamic.oppositeCocharacter χ)
  have hP : (Dynamic.parabolic χ).IsRepresentedBy i := ⟨inferInstance, hχ⟩
  apply SubgroupFunctor.normalizer_eq_of_rational_points_and_open_cell iU i hi
  · exact fun n hn => mem_range_of_mem_normalizer_of_borel_statements
      hconj hnorm i hi B j f hj hf hn
  · intro T g hgU hgN
    rw [hU.2] at hgU
    rw [hχ] at hgN
    exact Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_normalizer χ hgU hgN
  · exact oppositeCellStatement k G χ _ P iU i hU hP

/-- Rational membership over the original algebraic closure suffices for the
exact all-test target. No reductivity or parabolicity ascent premise is used. -/
theorem parabolicSelfNormalizerStatement_of_rational_descent
    (hconj : BorelConjugacyStatement.{u}) (hnorm : BorelNormalizerStatement.{u})
    (hpar : ParabolicDynamicStatement.{u}) (hconn : DynamicConnectedStatement.{u}) :
    ParabolicSelfNormalizerStatement.{u} := by
  intro k _ G hG P i hi
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth P.X.hom := hi.smooth
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  obtain ⟨χ, hχ⟩ := (hpar k G hG P i hi.isClosedSubgroup).mp hi
  let b := toAlgebraicClosure k
  let F := GroupScheme.baseChange b
  have : Smooth (F.obj G).X.hom := by
    change Smooth (CategoryTheory.Limits.pullback.snd G.X.hom b)
    infer_instance
  have : IsAffineHom (F.obj G).X.hom := by
    change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
    infer_instance
  have : ConnectedSpace (F.obj G).X.left := hG.connectedSpace_toAlgebraicClosure
  have : Smooth (F.obj P).X.hom := by
    change Smooth (CategoryTheory.Limits.pullback.snd P.X.hom b)
    infer_instance
  have hiclosed : IsClosedSubgroup (F.map i) := hi.isClosedSubgroup.baseChange b
  have : IsClosedImmersion (F.map i).hom.hom.left := hiclosed
  have : Mono (F.map i).hom.hom := Over.mono_of_mono_left _
  have hχb : SubgroupFunctor.range (F.map i) =
      Dynamic.parabolic (Dynamic.baseChangeCocharacter b χ) := by
    rw [SubgroupFunctor.range_baseChangeHom, hχ, Dynamic.parabolic_baseChange]
  have : ConnectedSpace (F.obj P).X.left :=
    ((hconn (AlgebraicClosure k) (F.obj G) (Dynamic.baseChangeCocharacter b χ)
      (F.obj P) (F.map i)).2 inferInstance).1 ⟨inferInstance, hχb⟩
  obtain ⟨B, j, f, hj, hf⟩ := hi.exists_isBorelSubgroup
  have heq := normalizer_eq_of_dynamic_parabolic_and_borel hconj hnorm
    (F.map i) hiclosed (Dynamic.baseChangeCocharacter b χ) hχb B j f hj hf
  obtain ⟨hbSurjective, hbFlat, hbQuasiCompact⟩ := fieldExtension_fpqc k (AlgebraicClosure k)
  have : Surjective b := hbSurjective
  have : Flat b := hbFlat
  have : QuasiCompact b := hbQuasiCompact
  apply SubgroupFunctor.normalizer_eq_of_baseChange_eq b i
  simpa only [F, SubgroupFunctor.range_baseChangeHom] using heq

/-- Under the retained structural statements, lift each normalizer point to the
original parabolic source over the original base field. -/
def normalizerPointsEquivOfRationalDescent
    (hconj : BorelConjugacyStatement.{u}) (hnorm : BorelNormalizerStatement.{u})
    (hpar : ParabolicDynamicStatement.{u}) (hconn : DynamicConnectedStatement.{u})
    (hG : IsConnectedReductive G) (i : P ⟶ G) (hi : IsParabolicSubgroup i)
    (T : Over (Spec (CommRingCat.of k))) :
    (SubgroupFunctor.range i).normalizer.carrier T ≃* (T ⟶ P.X) := by
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  exact (MulEquiv.subgroupCongr
    (congrArg (fun F : SubgroupFunctor G => F.carrier T)
      (parabolicSelfNormalizerStatement_of_rational_descent
        hconj hnorm hpar hconn k G hG P i hi))).trans
    ((show (SubgroupFunctor.range i).IsRepresentedBy i from
      ⟨inferInstance, rfl⟩).pointsEquiv T).symm

/-- The descended point equivalence lifts along the specified inclusion. -/
theorem normalizerPointsEquivOfRationalDescent_comp
    (hconj : BorelConjugacyStatement.{u}) (hnorm : BorelNormalizerStatement.{u})
    (hpar : ParabolicDynamicStatement.{u}) (hconn : DynamicConnectedStatement.{u})
    (hG : IsConnectedReductive G) (i : P ⟶ G) (hi : IsParabolicSubgroup i)
    (T : Over (Spec (CommRingCat.of k)))
    (g : (SubgroupFunctor.range i).normalizer.carrier T) :
    normalizerPointsEquivOfRationalDescent hconj hnorm hpar hconn hG i hi T g ≫
      i.hom.hom = g := by
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  exact (show (SubgroupFunctor.range i).IsRepresentedBy i from
    ⟨inferInstance, rfl⟩).pointsEquiv_symm_comp _

end Langlands.GroupScheme
