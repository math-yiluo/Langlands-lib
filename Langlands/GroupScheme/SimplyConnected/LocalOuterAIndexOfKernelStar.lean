import Langlands.GroupScheme.SimplyConnected.TypeARankOneOrbit
import Langlands.GroupScheme.Reductive.TitsKernelVertexComparison
import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerDerivedProof
import Langlands.GroupScheme.SimplyConnected.LocalAnisotropicTypeAInnerProof

/-!
# Outer type-A rank-one indices with trivial star action on the zero vertices

The full star action restricts to a permutation-valued homomorphism on the actual
zero vertices. If this restricted action is trivial, an outer type-A rank-one
index has rank two or three and distinguished endpoints. Local arithmetic
supplies triviality for an actual anisotropic kernel that is absolutely almost
simple and has a supplied type-A Cartan numbering. Reducible kernels are not
covered by that application.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.TitsIndexData

variable {K : Type u} [Field K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G)

/-- The full absolute Galois star action on the actual zero vertices. -/
def zeroStarHom :
    (SeparableClosure K ≃ₐ[K] SeparableClosure K) →* Equiv.Perm d.zeroVertices where
  toFun σ :=
    { toFun := d.zeroStar σ
      invFun := d.zeroStar σ⁻¹
      left_inv := by
        intro a
        apply Subtype.ext
        change d.star σ⁻¹ (d.star σ a.val) = a.val
        rw [← d.star_mul, inv_mul_cancel, d.star_one]
      right_inv := by
        intro a
        apply Subtype.ext
        change d.star σ (d.star σ⁻¹ a.val) = a.val
        rw [← d.star_mul, mul_inv_cancel, d.star_one] }
  map_one' := by
    apply Equiv.ext
    intro a
    apply Subtype.ext
    exact d.star_one a.val
  map_mul' σ τ := by
    apply Equiv.ext
    intro a
    apply Subtype.ext
    exact d.star_mul σ τ a.val

@[simp] theorem zeroStarHom_apply
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : d.zeroVertices) :
    (d.zeroStarHom σ a).val = d.star σ a.val := rfl

/-- The restricted permutation is the identity exactly when all zero vertices
are fixed by the same full Galois element. -/
theorem zeroStarHom_eq_one_iff
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) :
    d.zeroStarHom σ = 1 ↔ ∀ a : d.zeroVertices, d.star σ a.val = a.val := by
  constructor
  · intro h a
    have h' := congrArg (fun f : Equiv.Perm d.zeroVertices => (f a).val) h
    exact h'
  · intro h
    apply Equiv.ext
    intro a
    apply Subtype.ext
    exact h a

/-- A nontrivial type-A full star action at split rank one has one of the two
listed outer indices if its action on every zero vertex is trivial. -/
theorem hasRankOneOuterAIndex_of_zero_star_trivial {n : ℕ}
    (hrank : splitRank G = 1) (e : d.Vertex ≃ Fin n)
    (hA : ∀ a b, d.cartan a b = CartanMatrix.A n (e a) (e b))
    (hnot : ¬ d.StarIsTrivial)
    (hzero : ∀ (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
      (a : d.zeroVertices), d.star σ a.val = a.val) :
    d.HasRankOneOuterAIndex n := by
  classical
  have hpair := d.starImagePair_of_A e hA hnot
  let j := e (d.rankOneDistinguishedVertex hrank).val
  have hmark (a : d.Vertex) :
      a ∈ d.distinguishedVertices ↔ e a = j ∨ e a = Fin.revPerm j :=
    d.mem_distinguishedVertices_iff_of_rank_one_starImagePair hrank e Fin.revPerm hpair a
  obtain ⟨σ, hσ⟩ := hpair.2.2
  have hnonfixed (i : Fin n) (hi : i ≠ Fin.revPerm i) :
      i = j ∨ i = Fin.revPerm j := by
    have hdist : e.symm i ∈ d.distinguishedVertices := by
      by_contra hdist
      have hz : e.symm i ∈ d.zeroVertices := by
        simpa only [distinguishedVertices, Set.mem_compl_iff, not_not] using hdist
      have hfix := congrArg e (hzero σ ⟨e.symm i, hz⟩)
      have hrev := hσ (e.symm i)
      exact hi (by simpa only [Equiv.apply_symm_apply] using hfix.symm.trans hrev)
    simpa only [Equiv.apply_symm_apply] using (hmark (e.symm i)).mp hdist
  have hn : 2 ≤ n := by
    by_contra hn
    apply hpair.1
    apply Equiv.ext
    intro i
    apply Fin.ext
    have hi := i.isLt
    have hri := (Fin.revPerm i).isLt
    omega
  have hzero_end := hnonfixed ⟨0, by omega⟩ (by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.revPerm_apply, Fin.val_rev] at hv
    omega)
  have hj : j.val = 0 ∨ j.val + 1 = n := by
    rcases hzero_end with h | h
    · have hv := congrArg Fin.val h
      exact Or.inl hv.symm
    · have hv := congrArg Fin.val h
      simp only [Fin.revPerm_apply, Fin.val_rev] at hv
      have hjlt := j.isLt
      omega
  have hn3 : n ≤ 3 := by
    by_contra hn3
    have hn4 : 4 ≤ n := by omega
    have hone := hnonfixed ⟨1, by omega⟩ (by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.revPerm_apply, Fin.val_rev] at hv
      omega)
    rcases hone with h | h
    · have hv : 1 = j.val := congrArg Fin.val h
      clear h
      rcases hj with hj | hj <;> omega
    · have hv := congrArg Fin.val h
      simp only [Fin.revPerm_apply, Fin.val_rev] at hv
      rcases hj with hj | hj <;> omega
  refine ⟨by omega, e, ⟨hA, ?_⟩, hpair⟩
  intro a
  rw [hmark a]
  simp only [Fin.ext_iff, Fin.revPerm_apply, Fin.val_rev]
  have ha := (e a).isLt
  rcases hj with hj | hj <;> omega

section LocalKernel

variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {M D : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom]
  {j : M ⟶ G} {i : D ⟶ M}

/-- Local innerness transports to the actual zero vertices when the actual
anisotropic kernel is absolutely almost simple and has type A. -/
theorem zeroStarHom_eq_one_of_simple_typeA_kernel
    (hsc : IsSimplyConnected G)
    (hj : (torusCentralizer d.splitInclusion).IsRepresentedBy j)
    (hi : IsDerivedSubgroup i) (eD : TitsIndexData D)
    (hcomp : d.KernelComparison (i ≫ j) eD)
    (habs : IsAbsolutelyAlmostSimple D) {m : ℕ} (q : eD.Vertex ≃ Fin m)
    (hA : ∀ a b, eD.cartan a b = CartanMatrix.A m (q a) (q b))
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) :
    d.zeroStarHom σ = 1 := by
  have hDsc : IsSimplyConnected D :=
    splitTorusCentralizerDerivedSimplyConnected K G hsc d.splitTorus
      d.splitInclusion d.maximalSplit.1 M j hj D i hi
  have hDan : IsAnisotropic D := (titsAnisotropicKernel K G d M j hj D i hi).2
  have hstar := localAnisotropicTypeAInner K D eD m hDsc habs hDan ⟨q, hA⟩
  exact (d.zeroStarHom_eq_one_iff σ).mpr ((hcomp.star_trivial_iff.mp hstar) σ)

/-- The listed outer-A rank-one alternative for a group whose actual
anisotropic kernel is absolutely almost simple of type A. The supplied
numberings compare every actual ambient and kernel Cartan entry. -/
theorem hasRankOneOuterAIndex_of_simple_typeA_kernel
    (hsc : IsSimplyConnected G)
    (hj : (torusCentralizer d.splitInclusion).IsRepresentedBy j)
    (hi : IsDerivedSubgroup i) (eD : TitsIndexData D)
    (hcomp : d.KernelComparison (i ≫ j) eD)
    (habs : IsAbsolutelyAlmostSimple D) {m : ℕ} (q : eD.Vertex ≃ Fin m)
    (hDA : ∀ a b, eD.cartan a b = CartanMatrix.A m (q a) (q b))
    {n : ℕ} (hrank : splitRank G = 1) (e : d.Vertex ≃ Fin n)
    (hA : ∀ a b, d.cartan a b = CartanMatrix.A n (e a) (e b))
    (hnot : ¬ d.StarIsTrivial) :
    d.HasRankOneOuterAIndex n := by
  apply d.hasRankOneOuterAIndex_of_zero_star_trivial hrank e hA hnot
  intro σ
  exact (d.zeroStarHom_eq_one_iff σ).mp
    (d.zeroStarHom_eq_one_of_simple_typeA_kernel hsc hj hi eD hcomp habs q hDA σ)

end LocalKernel

end Langlands.GroupScheme.TitsIndexData
