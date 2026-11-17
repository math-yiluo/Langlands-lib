import Langlands.GroupScheme.Rational.SemistandardSpectralIndex
import Langlands.GroupScheme.Rational.RelativeRankProof
import Langlands.GroupScheme.Rational.MaximalSplitTorusSubgroup
import Langlands.GroupScheme.ClosedSubgroupMonomorphism

/-! # The actual induction rank for proper semistandard Levis -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G M : GroupScheme (Spec (CommRingCat.of k))}
  {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} {j : M ⟶ G}

/-- The original split torus lifted to a representative of the literal Levi.
The factorization uses the index's containment on every test scheme. -/
def semistandardLeviSplitTorus (p : SemistandardSpectralIndex i)
    (hj : p.levi.IsRepresentedBy j) : T.toGrp ⟶ M :=
  hj.factorHom i p.torus_le_levi

@[reassoc (attr := simp)]
theorem semistandardLeviSplitTorus_comp (p : SemistandardSpectralIndex i)
    (hj : p.levi.IsRepresentedBy j) :
    semistandardLeviSplitTorus p hj ≫ j = i :=
  hj.factorHom_comp i p.torus_le_levi

/-- Lifting the ambient maximal split torus to the literal Levi preserves
maximal splitness, without any conjugacy choice. -/
theorem isMaximalSplitTorus_semistandardLeviSplitTorus
    (p : SemistandardSpectralIndex i) (hj : p.levi.IsRepresentedBy j)
    (hjc : IsClosedSubgroup j) (hi : IsMaximalSplitTorus i) :
    IsMaximalSplitTorus (semistandardLeviSplitTorus p hj) := by
  apply IsMaximalSplitTorus.of_comp hjc
  rwa [semistandardLeviSplitTorus_comp]

/-- The actual relative-root-span rank is independent of the maximal split
torus. This follows from the published split-rank/character-rank identities. -/
theorem relativeRootRank_eq_of_maximalSplitTori
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (hi' : IsMaximalSplitTorus i') :
    haveI := hG.isAffineHom
    relativeRootRank i = relativeRootRank i' := by
  let := hG.isAffineHom
  have h := relativeRankIdentity k G hG T i hi
  have h' := relativeRankIdentity k G hG T' i' hi'
  have htorus : splitTorusRank T = splitTorusRank T' := by
    exact_mod_cast h.2.2.2.1.symm.trans h'.2.2.2.1
  exact Nat.add_right_cancel (h.2.2.2.2.1.symm.trans
    (htorus.trans h'.2.2.2.2.1))

/-- Exact structural rank-decrease target for the induction preceding VIII.2.
Both ranks are the dimensions of the actual relative-root spans. The Levi is
any closed reductive model of the index's literal all-test subgroup. -/
def SemistandardProperLeviRankStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (_hi : IsMaximalSplitTorus i)
    (p : SemistandardSpectralIndex i), p.parabolic ≠ ⊤ →
    ∀ (M : GroupScheme (Spec (CommRingCat.of k))) (j : M ⟶ G)
      (hj : p.levi.IsRepresentedBy j) (_hjc : IsClosedSubgroup j)
      (hM : IsConnectedReductive M),
      haveI := hG.isAffineHom
      haveI := hM.isAffineHom
      relativeRootRank (semistandardLeviSplitTorus p hj) < relativeRootRank i

/-- The same exact decrease for any maximal split torus chosen in that Levi.
Changing torus cannot change which groups are strictly below the ambient one. -/
theorem relativeRootRank_properLevi_lt
    (hrank : SemistandardProperLeviRankStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (p : SemistandardSpectralIndex i) (hp : p.parabolic ≠ ⊤)
    (hj : p.levi.IsRepresentedBy j) (hjc : IsClosedSubgroup j)
    (hM : IsConnectedReductive M) (a : T'.toGrp ⟶ M)
    (ha : IsMaximalSplitTorus a) :
    haveI := hG.isAffineHom
    haveI := hM.isAffineHom
    relativeRootRank a < relativeRootRank i := by
  let := hG.isAffineHom
  let := hM.isAffineHom
  rw [relativeRootRank_eq_of_maximalSplitTori hM a
    (semistandardLeviSplitTorus p hj) ha
    (isMaximalSplitTorus_semistandardLeviSplitTorus p hj hjc hi)]
  exact hrank k G hG T i hi p hp M j hj hjc hM

/-- Conditional rank-zero boundary: every semistandard parabolic is G.
The proof extracts an actual reductive closed Levi model from the index. -/
theorem semistandardParabolic_eq_top_of_rank_zero
    (hrank : SemistandardProperLeviRankStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hzero : haveI := hG.isAffineHom; relativeRootRank i = 0)
    (p : SemistandardSpectralIndex i) : p.parabolic = ⊤ := by
  let := hG.isAffineHom
  by_contra hp
  obtain ⟨P, M, U, q, l, r, hq, hP, hl, hM, hMl, hUr, hUr', hdec⟩ :=
    p.isParabolicWithLeviAndRadical
  have hjc := hl.comp hP.isClosedSubgroup
  have hj : p.levi.IsRepresentedBy (l ≫ q) := ⟨IsClosedSubgroup.mono_overHom hjc, hMl⟩
  have hlt := hrank k G hG T i hi p hp M (l ≫ q) hj hjc hM
  rw [hzero] at hlt
  exact Nat.not_lt_zero _ hlt

/-- The proper parabolic carrier is empty in semisimple rank zero. -/
theorem isEmpty_properSemistandard_of_rank_zero
    (hrank : SemistandardProperLeviRankStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hzero : haveI := hG.isAffineHom; relativeRootRank i = 0) :
    IsEmpty {p : SemistandardSpectralIndex i // p.parabolic ≠ ⊤} :=
  ⟨fun p => p.property
    (semistandardParabolic_eq_top_of_rank_zero hrank hG hi hzero p.val)⟩

end Langlands.GroupScheme
