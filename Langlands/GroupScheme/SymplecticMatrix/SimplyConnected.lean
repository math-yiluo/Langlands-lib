import Langlands.GroupScheme.SymplecticMatrix.Roots
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.Reductive.SplitSemisimplicity
import Langlands.GroupScheme.SimplyConnected.SplitCriterion
import Langlands.GroupScheme.SymplecticMatrix.StandardComparison

/-! # The split symplectic group over a field is simply connected -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SymplecticMatrix

variable {l : Type} [Fintype l] [DecidableEq l] {k : Type u} [Field k]

local notation "𝔻" => splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift l)

/-! ### Long coroots -/

/-- The pairing of the long root `2 e_b` with a cocharacter `ν` is `2 ν_b`. -/
theorem latticePairing_longRoot (b : l) (ν : cocharacterLattice 𝔻) :
    latticePairing 𝔻 (longRoot l k b) ν = 2 * GeneralLinear.cocharacterCoordEquiv l k ν b := by
  rw [GeneralLinear.latticePairing_coord, characterCoordEquiv_longRoot,
    Finset.sum_eq_single b (fun c _ hc => by rw [Pi.single_eq_of_ne hc, zero_mul]) (by simp),
    Pi.single_eq_same]

/-- **Long coroots.** In a root datum of the diagonal torus, the coroot of the long root `2 e_a`
is the cocharacter `e_a^∨`. -/
theorem cocharacterCoordEquiv_coroot_of_root_eq_longRoot {J : Type u}
    {P : RootDatum J (characterLattice 𝔻) (cocharacterLattice 𝔻)}
    (hP : IsRootDatumOf (diagonalTorus l (CommRingCat.of k)) P) {j : J} {a : l}
    (hj : P.root j = longRoot l k a) :
    GeneralLinear.cocharacterCoordEquiv l k (P.coroot j) = Pi.single a 1 := by
  have hpair : ∀ j', P.pairing j' j = latticePairing 𝔻 (P.root j') (P.coroot j) := fun j' => by
    rw [← P.root_coroot_eq_pairing, hP.1]
  funext b
  by_cases hab : b = a
  · subst hab
    have h := hpair j
    rw [P.pairing_same, hj, latticePairing_longRoot] at h
    rw [Pi.single_eq_same]
    omega
  · rw [Pi.single_eq_of_ne hab]
    obtain ⟨j', hj'⟩ : longRoot l k b ∈ Set.range P.root := by
      rw [hP.2.1]
      exact longRoot_mem_roots b
    have hmem : P.root (P.reflectionPerm j j') ∈ roots (diagonalTorus l (CommRingCat.of k)) := by
      rw [← hP.2.1]
      exact ⟨_, rfl⟩
    rw [P.root_reflectionPerm, P.reflection_apply_root, hj, hj'] at hmem
    have hc := hpair j'
    rw [hj', latticePairing_longRoot] at hc
    have hcoord : GeneralLinear.characterCoordEquiv l k
        (longRoot l k b - P.pairing j' j • longRoot l k a) =
        Pi.single b 2 - P.pairing j' j • Pi.single a 2 := by
      rw [map_sub, map_zsmul, characterCoordEquiv_longRoot, characterCoordEquiv_longRoot]
    have h2 := eq_single_two_of_mem_roots hmem (b := b) (by
      rw [hcoord, Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne hab,
        smul_zero, sub_zero])
    rw [hcoord] at h2
    have h3 := congrFun h2 a
    rw [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hab),
      smul_eq_mul] at h3
    omega

/-- **Coroot span.** The coroots of a root datum of the diagonal torus span the cocharacter
lattice: they contain the basis `e_a^∨` of long coroots. -/
theorem corootSpan_eq_top {J : Type u}
    {P : RootDatum J (characterLattice 𝔻) (cocharacterLattice 𝔻)}
    (hP : IsRootDatumOf (diagonalTorus l (CommRingCat.of k)) P) :
    P.corootSpan ℤ = ⊤ := by
  rw [eq_top_iff,
    ← ((Pi.basisFun ℤ l).map (GeneralLinear.cocharacterCoordEquiv l k).symm).span_eq,
    Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  obtain ⟨j, hj⟩ : longRoot l k a ∈ Set.range P.root := by
    rw [hP.2.1]
    exact longRoot_mem_roots a
  rw [Module.Basis.map_apply, Pi.basisFun_apply,
    ← cocharacterCoordEquiv_coroot_of_root_eq_longRoot hP hj, LinearEquiv.symm_apply_apply]
  exact Submodule.subset_span ⟨j, rfl⟩

/-! ### Simple connectedness -/

variable (l k)

/-- The diagonal torus of `Sp_{2l}` over a field has a reduced root datum. -/
theorem exists_rootDatum :
    ∃ (J : Type u) (_ : Finite J)
      (P : RootDatum J (characterLattice 𝔻) (cocharacterLattice 𝔻)),
      IsRootDatumOf (diagonalTorus l (CommRingCat.of k)) P ∧ P.IsReduced :=
  rootDatumExistence k (groupScheme l (CommRingCat.of k)) (isConnectedReductive l k) 𝔻
    (isSplitTorus_diagonalTorus l k) (diagonalTorus l (CommRingCat.of k))
    (isMaximalTorus_diagonalTorus l k)

/-- **Simple connectedness.** The split symplectic group over a field is simply connected: it is
semisimple and simply connected because the coroots span the cocharacter lattice. -/
theorem isSimplyConnected : IsSimplyConnected (groupScheme l (CommRingCat.of k)) := by
  obtain ⟨J, _, P, hP, -⟩ := exists_rootDatum l k
  have hss : IsSemisimple (groupScheme l (CommRingCat.of k)) := by
    refine ((splitSemisimpleRootDatum k _ (isConnectedReductive l k) 𝔻
      (isSplitTorus_diagonalTorus l k) _ (isMaximalTorus_diagonalTorus l k) J P hP).2).mpr ?_
    rw [corootSpan_eq_top hP]
    infer_instance
  exact splitCorootSpanSimplyConnected k _ hss 𝔻 (isSplitTorus_diagonalTorus l k)
    _ (isMaximalTorus_diagonalTorus l k) J P hP (corootSpan_eq_top hP)

end Langlands.GroupScheme.SymplecticMatrix

namespace Langlands.GroupScheme.Symplectic

/-- **Simple connectedness of the standard model.** The standard symplectic group `Sp_{2n}`
over a field is simply connected, by transport along `SymplecticMatrix.comparisonIso`. -/
theorem isSimplyConnected_groupScheme (K : Type u) [Field K] (n : ℕ) :
    IsSimplyConnected (groupScheme K n) :=
  IsSimplyConnected.of_iso (SymplecticMatrix.comparisonIso K n).symm
    (SymplecticMatrix.isSimplyConnected (Fin n) K)

end Langlands.GroupScheme.Symplectic
