import Langlands.GroupScheme.Absolute.BorelExistenceCoordinates
import Langlands.GroupScheme.Absolute.ParabolicTransport
import Langlands.GroupScheme.Reductive.UnipotentRadicalExistenceStatement

/-! # Finite-height maximal normal unipotent subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Limits
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.UnipotentRadicalExistence

open BorelExistence

variable {k : Type u} [Field k]

/-- The conditions on a represented radical before greatestness is imposed. -/
structure IsCandidate {U G : GroupScheme (Spec (CommRingCat.of k))} (i : U ⟶ G) : Prop where
  isClosedSubgroup : IsClosedSubgroup i
  smooth : Smooth U.X.hom
  connectedSpace : ConnectedSpace U.X.left
  isUnipotent : IsUnipotent U
  isNormal : (SubgroupFunctor.range i).IsNormal

/-- Every coefficient representation of the trivial group fixes every vector. -/
theorem trivial_isUnipotent :
    IsUnipotent (Grp.trivial (Over (Spec (CommRingCat.of k)))) := by
  classical
  intro n _ _ _ ρ
  refine ⟨fun _ => 1, ?_, ?_⟩
  · intro h
    exact one_ne_zero (congrFun h (Classical.arbitrary n))
  · intro T g
    have hg : g = 1 := isTerminalTensorUnit.hom_ext g 1
    rw [hg, map_one, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]

/-- A homomorphism from the trivial group has identity image on every test. -/
theorem range_trivial_eq_bot (G : GroupScheme (Spec (CommRingCat.of k)))
    (i : Grp.trivial (Over (Spec (CommRingCat.of k))) ⟶ G) :
    SubgroupFunctor.range i = ⊥ := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  constructor
  · intro hx
    obtain ⟨g, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    have hg : g = 1 := isTerminalTensorUnit.hom_ext g 1
    change g ≫ i.hom.hom ∈ (⊥ : Subgroup (T ⟶ G.X))
    rw [hg, MonObj.one_comp]
    exact (⊥ : Subgroup (T ⟶ G.X)).one_mem
  · intro hx
    have hx1 : x = 1 := Subgroup.mem_bot.mp hx
    exact ⟨1, (MonObj.one_comp _).trans hx1.symm⟩

/-- The unit inclusion gives a smooth connected normal unipotent closed subgroup. -/
theorem trivial_isCandidate (G : GroupScheme (Spec (CommRingCat.of k))) :
    IsCandidate (0 : Grp.trivial (Over (Spec (CommRingCat.of k))) ⟶ G) where
  isClosedSubgroup := isClosedImmersion_of_comp_eq_id G.X.hom _ (Over.w _)
  smooth := by
    change Smooth (𝟙 (Spec (CommRingCat.of k)))
    infer_instance
  connectedSpace := by
    change ConnectedSpace (Spec (CommRingCat.of k))
    infer_instance
  isUnipotent := trivial_isUnipotent
  isNormal := by
    rw [range_trivial_eq_bot]
    intro T g x _ hx
    have hx1 : x = 1 := Subgroup.mem_bot.mp hx
    change g * x * g⁻¹ ∈ (⊥ : Subgroup (T ⟶ G.X))
    simpa only [hx1, mul_one, mul_inv_cancel] using (⊥ : Subgroup (T ⟶ G.X)).one_mem

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

/-- A minimal-height candidate is a radical if every competitor has a common candidate
upper bound with it. The upper-bound hypothesis is an explicit structural obligation. -/
theorem isUnipotentRadical_of_minimal_height {G U : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] {i : U ⟶ G} (hi : IsCandidate i)
    (hmin : ∀ (V : GroupScheme (Spec (CommRingCat.of k))) (j : V ⟶ G), IsCandidate j →
      (coordinateKernel i).height ≤ (coordinateKernel j).height)
    (hupper : ∀ (V : GroupScheme (Spec (CommRingCat.of k))) (j : V ⟶ G), IsCandidate j →
      ∃ (P : GroupScheme (Spec (CommRingCat.of k))) (p : P ⟶ G),
        IsCandidate p ∧ SubgroupFunctor.range i ≤ SubgroupFunctor.range p ∧
          SubgroupFunctor.range j ≤ SubgroupFunctor.range p) : IsUnipotentRadical i where
  isClosedSubgroup := hi.isClosedSubgroup
  smooth := hi.smooth
  connectedSpace := hi.connectedSpace
  isUnipotent := hi.isUnipotent
  isNormal := hi.isNormal
  greatest V j hc hs hcon hu hn := by
    obtain ⟨P, p, hp, hip, hjp⟩ := hupper V j ⟨hc, hs, hcon, hu, hn⟩
    exact hjp.trans (range_eq_of_minimal_height hi hp (hmin P p hp) hip).ge

end Langlands.GroupScheme.UnipotentRadicalExistence
