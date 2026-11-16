import Langlands.GroupScheme.Reductive.LocalRankOneCellBaseChange
import Langlands.GroupScheme.Reductive.LocalRankOneEtaleWeylData
import Langlands.GroupScheme.Reductive.LocalRankOneUnitCellData
import Langlands.GroupScheme.Reductive.FibrewiseRootDatumBaseChange
import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.GroupScheme.Torus.FibrewiseMaximalBaseChange

/-! # Unit cell coordinates for actual rank-one reflections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.splitTorus.RelativeCocharacterCentralizer

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

/-- The actual centralizer cell after arbitrary coefficient base change,
with its original root coordinates. -/
def corootBaseChangeCellData (A : Type u) [CommRing A] [Algebra R A] :
    RingRootCell.CellData A :=
  LocalRankOneCell.baseChangeCellData (torusHom I G i mu) (P.root a)
    (rootLift i mu hm (by
      simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_zero] using
        congrArg Neg.neg ha))
    (rootLift i mu hp ha)
    (isRootParametrization_rootLift i mu hm _)
    (isRootParametrization_rootLift i mu hp ha)
    (corootCellData i mu hG hmax hP a ha hmu hp hm).open_cell A

/-- On every supplied field fibre there is a nonzero-scaled actual Weyl
product for which multiplication by the positive root at one has unit
negative and positive cell coordinates. -/
theorem exists_fieldUnitCellCoordinates (hi : IsClosedSubgroup i)
    (k : Type u) [Field k] [Algebra R k] :
    let D := corootBaseChangeCellData i mu hG hmax hP a ha hmu hp hm k
    ∃ d : k, d ≠ 0 ∧
      IsNormalizingPoint (T := commGroupScheme _ I) D.i
        (weylPoint D.xp (scaleHom d ≫ D.xm))
        (exponentCommIso (Spec (CommRingCat.of k)) I (P.reflection a)) ∧
      ∃ beta : Γ(Spec (CommRingCat.of k), ⊤),
      ∃ t : RingRootCell.base k ⟶ D.T.X,
      ∃ delta : Γ(Spec (CommRingCat.of k), ⊤),
        IsUnit beta ∧ IsUnit delta ∧
          D.A 1 * weylPoint D.xp (scaleHom d ≫ D.xm) = D.cellPt beta t delta := by
  let C := groupScheme I G i mu
  let b := algebraBaseMap R k
  let D := corootBaseChangeCellData i mu hG hmax hP a ha hmu hp hm k
  let hC := isReductive i mu hG
  let : Smooth G.X.hom := hG.smooth
  let : Smooth C.X.hom := hC.smooth
  have hCk := hC.isConnectedReductive_baseChange b
  let : Smooth D.G.X.hom := hCk.smooth
  let : ConnectedSpace D.G.X.left := hCk.connectedSpace
  have hPk : IsFibrewiseRootDatumOf I ((GroupScheme.baseChange b).obj G)
      (baseChangeHom (K := k) G I i) P := hP.baseChange_implicit
  let h := exponentCocharacter (Spec (CommRingCat.of k)) I (P.coroot a)
  have hh : h ≫ D.α = (2 : ℤ) • 𝟙 (Gm (Spec (CommRingCat.of k))) :=
    LocalRankOneWeylData.coroot_comp_root hPk a
  have hpair : latticePairing D.T D.α h = 2 := by
    change latticePairing (commGroupScheme (Spec (CommRingCat.of k)) I)
      (exponentCharacter (Spec (CommRingCat.of k)) I (P.root a))
      (exponentCocharacter (Spec (CommRingCat.of k)) I (P.coroot a)) = 2
    rw [latticePairing_exponentCharacter_exponentCocharacter,
      ← hP.pairing k, P.root_coroot_two]
  obtain ⟨d, hd, hn⟩ := exists_fieldReflection i mu hG hmax hP a ha hp hm k
  have hn' : IsNormalizingPoint D.i (weylPoint D.xp (scaleHom d ≫ D.xm))
      (RingRootCell.reflectionIso D.α h hh) := by
    have he : RingRootCell.reflectionIso D.α h hh =
        exponentCommIso (Spec (CommRingCat.of k)) I (P.reflection a) :=
      LocalRankOneWeylData.reflectionIso_eq_exponentCommIso hPk a
    rw [he]
    exact hn
  have hiD : IsClosedSubgroup D.i :=
    isClosedSubgroup_coordinateBaseChange I C (torusHom I G i mu) b
      (isClosedSubgroup_torusHom I G i mu hi)
  have hmaxD : IsFibrewiseMaximalTorus (T := D.T) D.i :=
    isFibrewiseMaximalTorus_coordinateBaseChange I C (torusHom I G i mu) b
      (isFibrewiseMaximalTorus i mu hmax)
  have hn2 := hn'.exists_sq_eq_of_fibrewiseMaximal
    (RingRootCell.reflectionIso_trans_self D.α h hh) (hC.baseChange b)
    (isSplitTorus_splitTorus I) hiD hmaxD
  obtain ⟨beta, t, delta, hb, hd', hf⟩ :=
    D.exists_unitFieldCellCoordinates h hh hpair _ hn' hn2
      (DynamicConnected.irreducibleSpace_of_smooth D.G)
  exact ⟨d, hd, hn, beta, t, delta, hb, hd', hf⟩

end Langlands.GroupScheme.splitTorus.RelativeCocharacterCentralizer
