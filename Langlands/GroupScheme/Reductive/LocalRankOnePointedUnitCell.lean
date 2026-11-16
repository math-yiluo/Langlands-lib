import Langlands.GroupScheme.Reductive.LocalRankOneActualWeylData

/-! # Pointed etale lifts with unit residue-cell coordinates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme

namespace RingRootCell

/-- A prescribed-action pointed etale normalizer lift, with unit cell
coordinates for its exact residue point after multiplication by `xp(1)`. -/
structure PointedEtaleUnitCellData {R : Type u} [CommRing R]
    (D : CellData R) (σ : D.T ≅ D.T) (s : Spec (CommRingCat.of R)) where
  residueNormalizer : Over.mk ((Spec (CommRingCat.of R)).fromSpecResidueField s) ⟶ D.G.X
  lift : PointedEtaleNormalizerData D.i σ s residueNormalizer
  beta : Γ(Spec ((Spec (CommRingCat.of R)).residueField s), ⊤)
  torus : Over.mk ((Spec (CommRingCat.of R)).fromSpecResidueField s) ⟶ D.T.X
  delta : Γ(Spec ((Spec (CommRingCat.of R)).residueField s), ⊤)
  unit_beta : IsUnit beta
  unit_delta : IsUnit delta
  factorization : D.A 1 * residueNormalizer = D.cellPt beta torus delta

end RingRootCell

namespace LocalRankOneCell

open LocalSplitCell LocalSplitRootBaseChange

/-- Transport a unit-cell factorization before specializing its group or roots. -/
theorem baseChangePointsEquiv_factorization
    {R : Type u} [CommRing R] {I : Type u} [Fintype I]
    {G : GroupScheme (Spec (CommRingCat.of R))}
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (a : I → ℤ) (xm xp : Ga R ⟶ G)
    (hm : IsRootParametrization i (-a) xm) (hp : IsRootParametrization i a xp)
    (hopen : IsOpenImmersion (Dynamic.tripleCellMultiplication xm i xp).left)
    (A : Type u) [CommRing A] [Algebra R A]
    {Z : Over (Spec (CommRingCat.of A))}
    (n : Z ⟶ ((GroupScheme.baseChange (algebraBaseMap R A)).obj G).X)
    (y : Γ(Z.left, ⊤)) (t : Z ⟶ (splitTorus (Spec (CommRingCat.of A)) I).X)
    (x : Γ(Z.left, ⊤))
    (hf : (baseChangeCellData i a xm xp hm hp hopen A).A 1 * n =
      (baseChangeCellData i a xm xp hm hp hopen A).cellPt y t x) :
    rootPoint xp ((Over.map (algebraBaseMap R A)).obj Z) 1 *
        GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) G Z n =
      rootPoint xm ((Over.map (algebraBaseMap R A)).obj Z) y *
        ((GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) (splitTorus _ I) Z
          (t ≫ (splitTorus.baseChangeIso (algebraBaseMap R A) I).inv.hom.hom) ≫ i.hom.hom) *
            rootPoint xp ((Over.map (algebraBaseMap R A)).obj Z) x) := by
  have h := congrArg (GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) G Z) hf
  change GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) G Z
    (rootPoint (baseChangeRoot A xp) Z 1 * n) = _ at h
  rw [map_mul, baseChangePointsEquiv_rootPoint,
    baseChangePointsEquiv_cellPt] at h
  exact h

end LocalRankOneCell

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

/-- Choose the field unit coordinates first, then lift precisely that
normalizer, with its prescribed whole-base reflection. -/
def pointedEtaleUnitCellReflection (hi : IsClosedSubgroup i)
    (s : Spec (CommRingCat.of R)) :
    RingRootCell.PointedEtaleUnitCellData
      (corootCellData i mu hG hmax hP a ha hmu hp hm)
      (LocalRankOneWeylData.corootReflectionIso hP a) s := Classical.choice <| by
  let k := (Spec (CommRingCat.of R)).residueField s
  let := LocalRankOneEtaleWeylData.residueFieldAlgebra R s
  let b := algebraBaseMap R k
  have hb : b = (Spec (CommRingCat.of R)).fromSpecResidueField s :=
    LocalRankOneEtaleWeylData.residueFieldAlgebra_baseMap R s
  let C := groupScheme I G i mu
  let D := corootCellData i mu hG hmax hP a ha hmu hp hm
  let E := corootBaseChangeCellData i mu hG hmax hP a ha hmu hp hm k
  let σ := LocalRankOneWeylData.corootReflectionIso hP a
  obtain ⟨d, -, hn, beta, t, delta, hbeta, hdelta, hfactor⟩ :=
    exists_fieldUnitCellCoordinates i mu hG hmax hP a ha hmu hp hm hi k
  let n := weylPoint E.xp (scaleHom d ≫ E.xm)
  let n' := GroupScheme.baseChangePointsEquiv b C (RingRootCell.base k) n
  let t' := GroupScheme.baseChangePointsEquiv b (splitTorus _ I) (RingRootCell.base k)
    (t ≫ (baseChangeIso b I).inv.hom.hom)
  let c : Over.mk ((Spec (CommRingCat.of R)).fromSpecResidueField s) ⟶
      (Over.map b).obj (RingRootCell.base k) :=
    Over.homMk (𝟙 _) (by
      change (𝟙 _ ≫ (𝟙 _ ≫ b)) = (Spec (CommRingCat.of R)).fromSpecResidueField s
      simpa only [Category.id_comp] using hb)
  let n₀ := c ≫ n'
  have hn' : IsNormalizingPoint ((GroupScheme.baseChange b).map D.i) n
      ((CommGroupScheme.baseChange b).mapIso σ) := by
    change IsNormalizingPoint _ _
      ((CommGroupScheme.baseChange b).mapIso
        (RingRootCell.reflectionIso _ _ (LocalRankOneWeylData.coroot_comp_root hP a)))
    rw [LocalRankOneWeylData.reflectionIso_eq_exponentCommIso hP a]
    exact isNormalizingPoint_baseChange_of_coordinates D.i b (P.reflection a) hn
  have ht : PointwiseSchemeAction.IsTransporter
      ((GroupScheme.baseChange b).map (CommGroupScheme.groupHom σ.hom ≫ D.i))
      ((GroupScheme.baseChange b).map D.i) n := by
    rw [Functor.map_comp]
    exact hn'.isTransporter
  have hn₀ : PointwiseSchemeAction.IsTransporter
      (CommGroupScheme.groupHom σ.hom ≫ D.i) D.i n₀ :=
    (ht.baseChangePointsEquiv b).restrict c
  have hf : D.A 1 * n' = D.cellPt beta t' delta := by
    exact LocalRankOneCell.baseChangePointsEquiv_factorization
      (torusHom I G i mu) (P.root a)
      (rootLift i mu hm (by
        simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_zero] using
          congrArg Neg.neg ha))
      (rootLift i mu hp ha)
      (isRootParametrization_rootLift i mu hm _)
      (isRootParametrization_rootLift i mu hp ha) D.open_cell k n beta t delta hfactor
  have hf₀ : D.A 1 * n₀ = D.cellPt beta (c ≫ t') delta := by
    have hf₀ := congrArg (fun v => c ≫ v) hf
    rw [MonObj.comp_mul, D.comp_A, D.comp_cellPt] at hf₀
    exact hf₀
  let hC := isReductive i mu hG
  let : IsAffine D.G.X.left := isAffine_of_isAffineHom C.X.hom
  exact ⟨{ residueNormalizer := n₀
           lift := pointedEtaleNormalizerOfTransporter D.i σ (isSplitTorus_splitTorus I)
             hC.smooth s n₀ hn₀
           beta := beta, torus := c ≫ t', delta := delta
           unit_beta := hbeta, unit_delta := hdelta, factorization := hf₀ }⟩

end splitTorus.RelativeCocharacterCentralizer

end Langlands.GroupScheme
