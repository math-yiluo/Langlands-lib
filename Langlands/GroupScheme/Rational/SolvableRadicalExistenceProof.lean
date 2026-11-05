import Langlands.GroupScheme.Rational.SolvableRadicalExistenceStatement
import Langlands.GroupScheme.Rational.SolvableSchemeComparison
import Langlands.GroupScheme.Reductive.UnipotentRadicalMaximal
import Langlands.GroupScheme.SubgroupFunctor.FppfProductSolvable
import Langlands.GroupScheme.SubgroupFunctor.SmoothConnectedNormalProductExistenceProof

/-! # Existence of the represented ground-field solvable radical -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SolvableRadicalExistence

open BorelExistence

variable {k : Type u} [Field k]

/-- The conditions on a represented solvable radical before greatestness is imposed. -/
structure IsCandidate {U G : GroupScheme (Spec (CommRingCat.of k))} (i : U ⟶ G) : Prop where
  isClosedSubgroup : IsClosedSubgroup i
  smooth : Smooth U.X.hom
  connectedSpace : ConnectedSpace U.X.left
  isSolvableGroupScheme : IsSolvableGroupScheme U
  isNormal : (SubgroupFunctor.range i).IsNormal

/-- Every point group of the trivial group scheme is trivial, so it is uniformly
solvable with derived length zero. -/
theorem trivial_isSolvableScheme :
    RelativeRoot.IsSolvableScheme (Grp.trivial (Over (Spec (CommRingCat.of k)))) := by
  refine ⟨0, fun T => ?_⟩
  rw [derivedSeries_zero]
  apply Subgroup.ext
  intro g
  simp only [Subgroup.mem_top, true_iff]
  exact Subgroup.mem_bot.mpr (isTerminalTensorUnit.hom_ext g 1)

/-- The unit inclusion gives a smooth connected normal solvable closed subgroup. -/
theorem trivial_isCandidate (G : GroupScheme (Spec (CommRingCat.of k))) :
    IsCandidate (0 : Grp.trivial (Over (Spec (CommRingCat.of k))) ⟶ G) where
  isClosedSubgroup := (UnipotentRadicalExistence.trivial_isCandidate G).isClosedSubgroup
  smooth := (UnipotentRadicalExistence.trivial_isCandidate G).smooth
  connectedSpace := (UnipotentRadicalExistence.trivial_isCandidate G).connectedSpace
  isSolvableGroupScheme := trivial_isSolvableScheme.isSolvableGroupScheme
  isNormal := (UnipotentRadicalExistence.trivial_isCandidate G).isNormal

/-- Candidate coordinate kernels attain a globally minimal finite height. -/
theorem exists_minimal_height_candidate (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] :
    ∃ (U : GroupScheme (Spec (CommRingCat.of k))) (i : U ⟶ G), IsCandidate i ∧
      ∀ (V : GroupScheme (Spec (CommRingCat.of k))) (j : V ⟶ G), IsCandidate j →
        (coordinateKernel i).height ≤ (coordinateKernel j).height := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ (U : GroupScheme (Spec (CommRingCat.of k))) (i : U ⟶ G),
      IsCandidate i ∧ (coordinateKernel i).height.toNat = n
  have hP : ∃ n, P n :=
    ⟨_, Grp.trivial _, 0, trivial_isCandidate G, rfl⟩
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

/-- Minimal height makes every inclusion into another candidate an equality of images. -/
theorem range_eq_of_minimal_height {G U V : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    {i : U ⟶ G} {j : V ⟶ G} (hi : IsCandidate i) (hj : IsCandidate j)
    (hheight : (coordinateKernel i).height ≤ (coordinateKernel j).height)
    (hle : SubgroupFunctor.range i ≤ SubgroupFunctor.range j) :
    SubgroupFunctor.range i = SubgroupFunctor.range j := by
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : IsClosedImmersion j.hom.hom.left := hj.isClosedSubgroup
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  have := hj.smooth
  have := hj.connectedSpace
  let f := SubgroupFunctor.factorOfRangeLE hle
  have hf : f ≫ j = i := SubgroupFunctor.factorOfRangeLE_comp hle
  have : IsIso f := isIso_of_coordinateKernel_height_le i j f hi.isClosedSubgroup
    hj.isClosedSubgroup hf hheight
  apply le_antisymm hle
  exact SubgroupFunctor.range_le_of_factor (inv f) (by rw [← hf, IsIso.inv_hom_id_assoc])

/-- A minimal-height candidate is the solvable radical if every competitor has a
common candidate upper bound with it. -/
theorem isSolvableRadical_of_minimal_height {G U : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] {i : U ⟶ G} (hi : IsCandidate i)
    (hmin : ∀ (V : GroupScheme (Spec (CommRingCat.of k))) (j : V ⟶ G), IsCandidate j →
      (coordinateKernel i).height ≤ (coordinateKernel j).height)
    (hupper : ∀ (V : GroupScheme (Spec (CommRingCat.of k))) (j : V ⟶ G), IsCandidate j →
      ∃ (P : GroupScheme (Spec (CommRingCat.of k))) (p : P ⟶ G),
        IsCandidate p ∧ SubgroupFunctor.range i ≤ SubgroupFunctor.range p ∧
          SubgroupFunctor.range j ≤ SubgroupFunctor.range p) : IsSolvableRadical i where
  isClosedSubgroup := hi.isClosedSubgroup
  smooth := hi.smooth
  connectedSpace := hi.connectedSpace
  isSolvableGroupScheme := hi.isSolvableGroupScheme
  isNormal := hi.isNormal
  greatest V j hc hs hcon hsol hn := by
    obtain ⟨P, p, hp, hip, hjp⟩ := hupper V j ⟨hc, hs, hcon, hsol, hn⟩
    exact hjp.trans (range_eq_of_minimal_height hi hp (hmin P p hp) hip).ge

/-- A candidate in an affine group is uniformly solvable on all tests. -/
theorem IsCandidate.isSolvableScheme {U G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] {i : U ⟶ G} (hi : IsCandidate i) :
    RelativeRoot.IsSolvableScheme U := by
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : IsAffineHom U.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  exact RelativeRoot.isSolvableScheme_of_isSolvableGroupScheme hi.smooth
    hi.isSolvableGroupScheme

end SolvableRadicalExistence

open SolvableRadicalExistence

/-- Every smooth connected affine group scheme over a field admits its
represented ground-field solvable radical. -/
theorem solvableRadicalExistence :
    SolvableRadicalExistenceStatement.{u} := by
  intro k _ G _ _ _
  obtain ⟨U, i, hi, hmin⟩ := exists_minimal_height_candidate G
  refine ⟨U, i, isSolvableRadical_of_minimal_height hi hmin ?_⟩
  intro V j hj
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  obtain ⟨P, p, hprod, hs, hconn⟩ :=
    smoothConnectedNormalFppfProductExistence k G inferInstance inferInstance
    U V i j hi.isClosedSubgroup hi.smooth hi.connectedSpace hi.isNormal
    hj.isClosedSubgroup hj.smooth hj.connectedSpace hj.isNormal
  have hsol : IsSolvableGroupScheme P :=
    (SubgroupFunctor.isSolvableScheme_of_isFppfProduct i j p hprod hi.isNormal
      hi.isSolvableScheme hj.isSolvableScheme).isSolvableGroupScheme
  exact ⟨P, p, ⟨hprod.isClosedSubgroup, hs, hconn, hsol,
    hprod.isNormal hi.isNormal hj.isNormal⟩, hprod.left_le, hprod.right_le⟩

end Langlands.GroupScheme
