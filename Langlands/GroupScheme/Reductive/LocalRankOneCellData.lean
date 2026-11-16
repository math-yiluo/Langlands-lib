import Langlands.GroupScheme.Reductive.LocalRankOneCentralizer
import Langlands.GroupScheme.Reductive.LocalRankOneCell

/-! # Actual rank-one centralizer cell data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme

namespace LocalSplitCell.IsRootParametrization

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I]
  {G : GroupScheme (Spec (CommRingCat.of R))}
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {a : I → ℤ} {xp : LocalSplitCell.Ga R ⟶ G}

/-- The scalar equivariance of a root parametrization gives equivariance
on arbitrary points of the actual additive group. -/
theorem equivariant_point (hp : LocalSplitCell.IsRootParametrization i a xp)
    (Z : Over (Spec (CommRingCat.of R)))
    (t : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X)
    (x : Z ⟶ (LocalSplitCell.Ga R).X) :
    (t ≫ i.hom.hom) * (x ≫ xp.hom.hom) * (t ≫ i.hom.hom)⁻¹ =
      VectorGroup.weightPointAction
        (splitTorus.exponentCharacter (Spec (CommRingCat.of R)) I a) Z t x ≫
          xp.hom.hom := by
  rw [RingRootCell.eq_gpt x, RingRootCell.weightPointAction_gpt]
  exact hp.equivariant Z t _

end LocalSplitCell.IsRootParametrization

namespace LocalRankOneCell

open LocalSplitCell

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
  (a nu : I → ℤ) (xm xp : Ga R ⟶ G)

/-- Actual opposite parametrizations and fieldwise two-root support define
the ring cell data used by the exact rank-one calculus. -/
def cellData (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hpos : 0 < ∑ j, a j * nu j)
    (hm : IsRootParametrization i (-a) xm) (hp : IsRootParametrization i a xp)
    (hsupport : ∀ (k : Type u) [Field k] [Algebra R k] (m : I → ℤ),
      splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I m ∈
        roots (T := splitTorus.commGroupScheme _ I)
          (splitTorus.baseChangeHom (K := k) G I i) ↔ m = a ∨ m = -a) :
    RingRootCell.CellData R where
  G := G
  T := splitTorus.commGroupScheme _ I
  i := i
  xp := xp
  xm := xm
  α := splitTorus.exponentCharacter _ I a
  hxp := hp.equivariant_point
  hxm := by
    classical
    have hneg : splitTorus.exponentCharacter (Spec (CommRingCat.of R)) I (-a) =
        -splitTorus.exponentCharacter (Spec (CommRingCat.of R)) I a :=
      (splitTorus.exponentCharacterLinear _ I).map_neg a
    simpa only [hneg] using hm.equivariant_point
  open_cell := isOpenImmersion i a nu xm xp hG hmax hpos hm hp hsupport

end LocalRankOneCell

namespace splitTorus.RelativeCocharacterCentralizer

open LocalSplitCell

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (mu : I → ℤ)
  {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}
  (hG : IsReductive G)
  (hmax : IsFibrewiseMaximalTorus (T := commGroupScheme _ I) i)
  (hP : IsFibrewiseRootDatumOf I G i P) (a : J)
  (ha : ∑ j, P.root a j * mu j = 0)
  (hmu : ∀ b : J, ∑ j, P.root b j * mu j = 0 →
    P.root b = P.root a ∨ P.root b = -P.root a)
  (nu : I → ℤ) (hpos : 0 < ∑ j, P.root a j * nu j)
  {xp xm : Ga R ⟶ G}
  (hp : IsRootParametrization i (P.root a) xp)
  (hm : IsRootParametrization i (-P.root a) xm)

/-- The actual relative cocharacter centralizer, with the actual lifted
opposite root maps, supplies the ring rank-one open-cell data. -/
def cellData : RingRootCell.CellData R :=
  LocalRankOneCell.cellData (torusHom I G i mu) (P.root a) nu
    (rootLift i mu hm (by
      simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_zero] using
        congrArg Neg.neg ha))
    (rootLift i mu hp ha)
    (isReductive i mu hG) (isFibrewiseMaximalTorus i mu hmax) hpos
    (isRootParametrization_rootLift i mu hm _)
    (isRootParametrization_rootLift i mu hp ha)
    (fun k _ _ m => mem_roots_baseChangeHom_iff_eq_or_neg i mu k hG hP a ha hmu m)

/-- Over a local ring the supplied coroot has pairing two, so no positive
cocharacter needs to be chosen separately for the actual centralizer cell. -/
def corootCellData [IsLocalRing R] : RingRootCell.CellData R :=
  cellData i mu hG hmax hP a ha hmu (P.coroot a) (by
    have htwo : ∑ j, P.root a j * P.coroot a j = 2 := by
      rw [← hP.pairing (IsLocalRing.ResidueField R), P.root_coroot_two]
    rw [htwo]
    norm_num) hp hm

end splitTorus.RelativeCocharacterCentralizer

end Langlands.GroupScheme
