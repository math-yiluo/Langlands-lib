import Langlands.GroupScheme.Reductive.LocalSplitRootPairLaws
import Langlands.GroupScheme.Reductive.LocalRootParametrizationRigidity

/-! # Uniqueness of Weyl-normalized root partners -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

namespace RingRootCell.CellData

open LocalSplitCell

variable {R : Type u} [CommRing R] (D : CellData R)

/-- A scalar change of the negative partner has a quotient in the rank-one
cell whenever the supplied Weyl product has the negative-root conjugation law. -/
theorem scalarWeylPoint_mul_weylPoint_inv (d : R)
    (hconj : ∀ x : Γ((base R).left, ⊤),
      D.G.constantPoint (weylPoint D.xp D.xm) (base R) * D.B x *
        (D.G.constantPoint (weylPoint D.xp D.xm) (base R))⁻¹ = D.A (-x)) :
    D.G.constantPoint (scalarWeylPoint D.xp D.xm d) (base R) *
      (D.G.constantPoint (weylPoint D.xp D.xm) (base R))⁻¹ =
      D.cellPt (1 - baseScalar (base R) d) 1 (baseScalar (base R) d - 1) := by
  let c := baseScalar (base R) d
  have hfactor : D.G.constantPoint (scalarWeylPoint D.xp D.xm d) (base R) =
      D.B (1 - c) * (D.G.constantPoint (weylPoint D.xp D.xm) (base R) * D.B (1 - c)) := by
    have h₁ : (1 - c) + -1 = -c := by ring
    have h₂ : -1 + (1 - c) = -c := by ring
    rw [constantPoint_scalarWeylPoint]
    change D.B (-c) * (D.A 1 * D.B (-c)) = _
    calc
      _ = D.B (1 - c + -1) * (D.A 1 * D.B (-1 + (1 - c))) := by rw [h₁, h₂]
      _ = _ := by
        rw [B_add, B_add]
        simp only [constantPoint_weylPoint, A, B, rootPoint, gpt, mul_assoc]
  rw [hfactor, mul_assoc, hconj, cellPt, I_one, one_mul]
  congr 1
  congr 1
  ring

/-- Cell-coordinate uniqueness and self-centralization of the torus force
any scalar partner with the same Weyl action to be the original partner. -/
theorem scalar_eq_one_of_same_weyl_action (d : R)
    (hself : torusCentralizer D.i = SubgroupFunctor.range D.i)
    (σ : D.T ≅ D.T)
    (hn : IsNormalizingPoint D.i (weylPoint D.xp D.xm) σ)
    (hn' : IsNormalizingPoint D.i (scalarWeylPoint D.xp D.xm d) σ)
    (hconj : ∀ x : Γ((base R).left, ⊤),
      D.G.constantPoint (weylPoint D.xp D.xm) (base R) * D.B x *
        (D.G.constantPoint (weylPoint D.xp D.xm) (base R))⁻¹ = D.A (-x)) :
    d = 1 := by
  have hc : D.G.constantPoint (scalarWeylPoint D.xp D.xm d) (base R) *
      (D.G.constantPoint (weylPoint D.xp D.xm) (base R))⁻¹ ∈
      centralizerPoints D.i := by
    change IsNormalizingPoint D.i _ (Iso.refl D.T)
    have hn₀ : IsNormalizingPoint D.i
        (D.G.constantPoint (weylPoint D.xp D.xm) (base R)) σ := by
      simpa only [constantPoint_self] using hn
    have hn₀' : IsNormalizingPoint D.i
        (D.G.constantPoint (scalarWeylPoint D.xp D.xm d) (base R)) σ := by
      simpa only [constantPoint_self] using hn'
    simpa only [Iso.symm_self_id] using hn₀'.mul hn₀.inv
  have hr := centralizerPoints_le_torusCentralizer D.i hc
  rw [hself] at hr
  change ∃ z : base R ⟶ D.T.X, z ≫ D.i.hom.hom =
    D.G.constantPoint (scalarWeylPoint D.xp D.xm d) (base R) *
      (D.G.constantPoint (weylPoint D.xp D.xm) (base R))⁻¹ at hr
  obtain ⟨z, hz⟩ := hr
  have hcell : D.cellPt (1 - baseScalar (base R) d) 1
      (baseScalar (base R) d - 1) = D.cellPt 0 z 0 := by
    rw [← scalarWeylPoint_mul_weylPoint_inv D d hconj, ← I_eq_cellPt]
    exact hz.symm
  have hc : baseScalar (base R) d = 1 := (sub_eq_zero.mp (D.cellPt_inj hcell).1).symm
  have he := congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).hom hc
  change (Scheme.ΓSpecIso (CommRingCat.of R)).hom
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv d) = _ at he
  simpa only [Iso.inv_hom_id_apply, map_one] using he

end RingRootCell.CellData

namespace splitTorus.RelativeCocharacterCentralizer

open LocalSplitCell

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
  {xp xm xm' : Ga R ⟶ G}
  (hp : IsRootParametrization i (P.root a) xp)
  (hm : IsRootParametrization i (-P.root a) xm)
  (hm' : IsRootParametrization i (-P.root a) xm')

include mu hG hmax hP ha hmu hp hm hm' in
/-- In the actual isolated rank-one centralizer, a fixed positive root has
at most one opposite partner with the prescribed Weyl action. -/
theorem rootPartner_unique_of_isolating_cocharacter (hi : IsClosedSubgroup i)
    (hn : IsWeylPoint i (weylPoint xp xm) (P.reflection a))
    (hn' : IsWeylPoint i (weylPoint xp xm') (P.reflection a)) : xm' = xm := by
  have hma : ∑ j, (-P.root a) j * mu j = 0 := by
    simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_zero] using
      congrArg Neg.neg ha
  let D := corootCellData i mu hG hmax hP a ha hmu hp hm
  have hpair : ∑ j, (-P.root a) j * (-P.coroot a) j = (2 : ℤ) := by
    simp only [Pi.neg_apply, neg_mul_neg]
    rw [← hP.pairing (IsLocalRing.ResidueField R), P.root_coroot_two]
  obtain ⟨d, hd, _⟩ :=
    (isRootParametrization_rootLift i mu hm' hma).existsUnique_unit
      (isRootParametrization_rootLift i mu hm hma) (-P.coroot a) (d := 2) two_pos hpair
  have h := rankOneLaws_rootLift i mu hG hmax hP a ha hmu hp hm hi hn
  have hn₁ := (isWeylPoint_rootLift i mu (a := a) ha hp hm hn).isNormalizingPoint
  have hn₂ := (isWeylPoint_rootLift i mu (a := a) ha hp hm' hn').isNormalizingPoint
  rw [hd] at hn₂
  have hd₁ : (d : R) = 1 := by
    have hf := D.scalar_eq_one_of_same_weyl_action (d : R)
    dsimp only [D, corootCellData, cellData, LocalRankOneCell.cellData] at hf
    have hs : torusCentralizer (T := commGroupScheme _ I) (torusHom I G i mu) =
        SubgroupFunctor.range (torusHom I G i mu) :=
      splitTorusCentralizer_eq_range_of_fibrewiseMaximal
        (G := groupScheme I G i mu) (T := commGroupScheme _ I)
        (isReductive i mu hG) (isSplitTorus_splitTorus I) (torusHom I G i mu)
        (isClosedSubgroup_torusHom I G i mu hi) (isFibrewiseMaximalTorus i mu hmax)
    apply hf hs (exponentCommIso (Spec (CommRingCat.of R)) I (P.reflection a)) hn₁ hn₂
    intro x
    exact h.2.1 (RingRootCell.base R) x
  have hmaps : rootLift i mu hm' hma = rootLift i mu hm hma := by
    rw [hd, hd₁, scaleHom_one, Category.id_comp]
  simpa only [rootLift_comp] using
    congrArg (fun f => f ≫ inclusion I G i mu) hmaps

end splitTorus.RelativeCocharacterCentralizer

namespace LocalSplitCell

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {I : Type u} [Fintype I] [DecidableEq I]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}

/-- For any root of an actual fibrewise datum over a local ring, a fixed
parametrization has at most one opposite partner realizing its reflection. -/
theorem rootPartner_unique (hG : IsReductive G) (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) (a : J)
    {xp xm xm' : Ga R ⟶ G}
    (hp : IsRootParametrization i (P.root a) xp)
    (hm : IsRootParametrization i (-P.root a) xm)
    (hm' : IsRootParametrization i (-P.root a) xm')
    (hn : IsWeylPoint i (weylPoint xp xm) (P.reflection a))
    (hn' : IsWeylPoint i (weylPoint xp xm') (P.reflection a)) : xm' = xm := by
  have : Finite J := hP.finite
  have := hP.isReduced
  obtain ⟨mu, ha, hmu⟩ :=
    LocalRootGroup.exists_kernel_exponent P (IsLocalRing.ResidueField R) a
  exact splitTorus.RelativeCocharacterCentralizer.rootPartner_unique_of_isolating_cocharacter
    i mu hG hmax hP a ha hmu hp hm hm' hi hn hn'

end LocalSplitCell

open LocalSplitCell

/-- A fixed actual root parametrization has at most one opposite partner
whose Weyl product realizes the prescribed reflection. -/
def LocalSplitRootPartnerUniquenessStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R]
    (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom],
    IsReductive G →
    ∀ (I : Type u) [Fintype I] [DecidableEq I]
      (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G),
      IsClosedSubgroup i →
      IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i →
      ∀ (J : Type u) (P : RootDatum J (I → ℤ) (I → ℤ)),
        IsFibrewiseRootDatumOf I G i P →
        ∀ (a : J) (xp xm xm' : Ga R ⟶ G),
          IsRootParametrization i (P.root a) xp →
          IsRootParametrization i (-P.root a) xm →
          IsRootParametrization i (-P.root a) xm' →
          IsWeylPoint i (weylPoint xp xm) (P.reflection a) →
          IsWeylPoint i (weylPoint xp xm') (P.reflection a) →
          xm' = xm

/-- The actual centralizer and its open cell establish partner uniqueness
for every root over an arbitrary local ring. -/
theorem localSplitRootPartnerUniqueness : LocalSplitRootPartnerUniquenessStatement.{u} := by
  intro R _ _ G _ hG I _ _ i hi hmax J P hP a xp xm xm' hp hm hm' hn hn'
  exact rootPartner_unique hG hi hmax hP a hp hm hm' hn hn'

end Langlands.GroupScheme
