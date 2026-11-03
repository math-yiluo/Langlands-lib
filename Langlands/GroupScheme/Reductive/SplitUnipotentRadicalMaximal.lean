import Langlands.GroupScheme.Reductive.UnipotentRadicalMaximal
import Langlands.GroupScheme.Reductive.SplitUnipotentRadicalExistenceStatement

/-! # Finite-height maximal split normal unipotent subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.SplitUnipotentRadicalExistence

open BorelExistence UnipotentRadicalExistence

variable {k : Type u} [Field k]

/-- The conditions on a represented split radical before greatestness is imposed:
the ordinary candidate conditions together with a finite split series. -/
structure IsSplitCandidate {U G : GroupScheme (Spec (CommRingCat.of k))} (i : U ⟶ G) :
    Prop extends IsCandidate i where
  isSplitUnipotent : RelativeRoot.IsSplitUnipotent U

/-- The trivial group over a field has the empty split series. -/
theorem trivial_hasSplitSeries_zero :
    RelativeRoot.HasSplitSeries 0 (Grp.trivial (Over (Spec (CommRingCat.of k)))) :=
  range_trivial_eq_bot _ (𝟙 _)

/-- The unit inclusion is a split candidate. -/
theorem trivial_isSplitCandidate (G : GroupScheme (Spec (CommRingCat.of k))) :
    IsSplitCandidate (0 : Grp.trivial (Over (Spec (CommRingCat.of k))) ⟶ G) where
  toIsCandidate := trivial_isCandidate G
  isSplitUnipotent := ⟨0, trivial_hasSplitSeries_zero⟩

/-- Split candidates attain a globally minimal finite coordinate-kernel height. -/
theorem exists_minimal_height_splitCandidate (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] :
    ∃ (U : GroupScheme (Spec (CommRingCat.of k))) (i : U ⟶ G), IsSplitCandidate i ∧
      ∀ (V : GroupScheme (Spec (CommRingCat.of k))) (j : V ⟶ G), IsSplitCandidate j →
        (coordinateKernel i).height ≤ (coordinateKernel j).height := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ (U : GroupScheme (Spec (CommRingCat.of k))) (i : U ⟶ G),
      IsSplitCandidate i ∧ (coordinateKernel i).height.toNat = n
  have hP : ∃ n, P n :=
    ⟨_, Grp.trivial _, 0, trivial_isSplitCandidate G, rfl⟩
  obtain ⟨U, i, hi, hheight⟩ := Nat.find_spec hP
  refine ⟨U, i, hi, ?_⟩
  intro V j hj
  have := hi.smooth
  have := hi.connectedSpace
  have := hj.smooth
  have := hj.connectedSpace
  have hmin : (coordinateKernel i).height.toNat ≤ (coordinateKernel j).height.toNat := by
    rw [hheight]
    exact Nat.find_min' hP ⟨V, j, hj, rfl⟩
  have hfinite := coordinateKernel_height_ne_top i
  have hfinite' := coordinateKernel_height_ne_top j
  rw [← ENat.natCast_toNat hfinite, ← ENat.natCast_toNat hfinite']
  exact_mod_cast hmin

/-- A minimal-height split candidate is a split radical if every split competitor has a
common split-candidate upper bound with it. The upper-bound hypothesis is an explicit
structural obligation. -/
theorem isSplitUnipotentRadical_of_minimal_height
    {G U : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] {i : U ⟶ G}
    (hi : IsSplitCandidate i)
    (hmin : ∀ (V : GroupScheme (Spec (CommRingCat.of k))) (j : V ⟶ G), IsSplitCandidate j →
      (coordinateKernel i).height ≤ (coordinateKernel j).height)
    (hupper : ∀ (V : GroupScheme (Spec (CommRingCat.of k))) (j : V ⟶ G),
      IsSplitCandidate j →
      ∃ (P : GroupScheme (Spec (CommRingCat.of k))) (p : P ⟶ G),
        IsSplitCandidate p ∧ SubgroupFunctor.range i ≤ SubgroupFunctor.range p ∧
          SubgroupFunctor.range j ≤ SubgroupFunctor.range p) :
    IsSplitUnipotentRadical i where
  isClosedSubgroup := hi.isClosedSubgroup
  smooth := hi.smooth
  connectedSpace := hi.connectedSpace
  isUnipotent := hi.isUnipotent
  isSplitUnipotent := hi.isSplitUnipotent
  isNormal := hi.isNormal
  greatest V j hc hs hcon hu hsplit hn := by
    obtain ⟨P, p, hp, hip, hjp⟩ := hupper V j ⟨⟨hc, hs, hcon, hu, hn⟩, hsplit⟩
    exact hjp.trans (range_eq_of_minimal_height hi.toIsCandidate hp.toIsCandidate
      (hmin P p hp) hip).ge

end Langlands.GroupScheme.SplitUnipotentRadicalExistence
