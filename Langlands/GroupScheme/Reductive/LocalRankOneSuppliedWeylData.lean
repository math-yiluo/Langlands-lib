import Langlands.GroupScheme.Reductive.LocalRankOneNormalizationDescent
import Langlands.GroupScheme.Reductive.RankOneRingWeylUniqueness
import Langlands.GroupScheme.Rational.RootKernelTorus

/-! # Etale cell normalization for supplied Weyl root maps -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme

namespace RingRootCell.WeylData

/-- The unscaled product is the actual Weyl point of the supplied root maps. -/
theorem unscaledWeylPoint_base_eq {R : Type u} [CommRing R] (D : WeylData R) :
    D.unscaledWeylPoint (base R) = LocalSplitCell.weylPoint D.xp D.xm := by
  simp only [unscaledWeylPoint, LocalSplitCell.weylPoint, CellData.A, CellData.B,
    LocalSplitCell.rootPoint, RingRootCell.gpt, mul_assoc]
  rfl

end RingRootCell.WeylData

namespace splitTorus.RelativeCocharacterCentralizer

open LocalSplitCell LocalSplitRootBaseChange

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {I : Type u} [Fintype I] [DecidableEq I]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (mu : I → ℤ)
  (hG : IsReductive G)
  (hmax : IsFibrewiseMaximalTorus (T := commGroupScheme _ I) i)
  {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}
  (hP : IsFibrewiseRootDatumOf I G i P) (a : J)
  (ha : ∑ j, P.root a j * mu j = 0)
  (hmu : ∀ b : J, ∑ j, P.root b j * mu j = 0 →
    P.root b = P.root a ∨ P.root b = -P.root a)
  {xp xm : Ga R ⟶ G}
  (hp : IsRootParametrization i (P.root a) xp)
  (hm : IsRootParametrization i (-P.root a) xm)

include hp hm in
omit [IsLocalRing R] in
/-- A supplied Weyl-normalized opposite pair retains its reflection after
lifting to the actual rank-one centralizer. -/
theorem isWeylPoint_rootLift
    (hn : IsWeylPoint i (weylPoint xp xm) (P.reflection a)) :
    IsWeylPoint (torusHom I G i mu)
      (weylPoint (rootLift i mu hp ha)
        (rootLift i mu hm (by
          simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_zero] using
            congrArg Neg.neg ha))) (P.reflection a) := by
  let j := inclusion I G i mu
  let : IsClosedImmersion j.hom.hom.left := isClosedSubgroup_inclusion I G i mu
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  apply isWeylPoint_of_isNormalizingPoint
  apply IsNormalizingPoint.of_comp j
  rw [torusHom_comp, ← weylPoint_comp, rootLift_comp, rootLift_comp]
  exact hn.isNormalizingPoint

variable {s : Spec (CommRingCat.of R)}
  {n₀ : Over.mk ((Spec (CommRingCat.of R)).fromSpecResidueField s) ⟶
    (groupScheme I G i mu).X}
  (E : RingRootCell.AffineEtaleUnitCellData
    (corootCellData i mu hG hmax hP a ha hmu hp hm)
    (LocalRankOneWeylData.corootReflectionIso hP a) s n₀)

/-- The actual affine etale cell has beta equal to one whenever the
original supplied opposite maps already realize the prescribed reflection. -/
theorem affineEtaleWeylData_beta_eq_one (hi : IsClosedSubgroup i)
    (hn : IsWeylPoint i (weylPoint xp xm) (P.reflection a)) :
    letI := E.coefficientAlgebra
    (affineEtaleWeylData i mu hG hmax hP a ha hmu hp hm E hi).cβ = 1 := by
  let := E.coefficientAlgebra
  let C := groupScheme I G i mu
  let hC := isReductive i mu hG
  let : Smooth C.X.hom := hC.smooth
  let W := affineEtaleWeylData i mu hG hmax hP a ha hmu hp hm E hi
  let b := algebraBaseMap R E.ring
  let : IsAffineHom W.G.X.hom := by
    change IsAffineHom (((GroupScheme.baseChange b).obj C).X.hom)
    exact inferInstanceAs (IsAffineHom (Limits.pullback.snd C.X.hom b))
  let : IsAffine W.G.X.left := isAffine_of_isAffineHom W.G.X.hom
  apply W.cβ_eq_one_of_unscaled_normalizes
  · apply splitTorusCentralizer_eq_range_of_fibrewiseMaximal
      ((isReductive i mu hG).baseChange b) (isSplitTorus_splitTorus I)
    · exact isClosedSubgroup_coordinateBaseChange I C (torusHom I G i mu) b
        (isClosedSubgroup_torusHom I G i mu hi)
    · exact isFibrewiseMaximalTorus_coordinateBaseChange I C (torusHom I G i mu) b
        (isFibrewiseMaximalTorus i mu hmax)
  · rw [W.unscaledWeylPoint_base_eq]
    have h := (isWeylPoint_baseChange E.ring
      (isWeylPoint_rootLift i mu (a := a) ha hp hm hn)).isNormalizingPoint
    have he : RingRootCell.reflectionIso W.α W.h W.hh =
        exponentCommIso (Spec (CommRingCat.of E.ring)) I (P.reflection a) :=
      LocalRankOneWeylData.reflectionIso_eq_exponentCommIso_over hP a E.ring
    rw [he]
    exact h

/-- The affine etale Weyl data, together with the exact supplied-coordinate
normalization forced by the original Weyl action. -/
def suppliedAffineEtaleWeylData (hi : IsClosedSubgroup i)
    (hn : IsWeylPoint i (weylPoint xp xm) (P.reflection a)) :
    letI := E.coefficientAlgebra
    {W : RingRootCell.WeylData E.ring // W.cβ = 1} := by
  letI := E.coefficientAlgebra
  exact ⟨affineEtaleWeylData i mu hG hmax hP a ha hmu hp hm E hi,
    affineEtaleWeylData_beta_eq_one i mu hG hmax hP a ha hmu hp hm E hi hn⟩

end splitTorus.RelativeCocharacterCentralizer

end Langlands.GroupScheme
