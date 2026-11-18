import Langlands.GroupScheme.OddOrthogonalMatrix.Automorphisms
import Langlands.GroupScheme.OddOrthogonalMatrix.Connected
import Langlands.GroupScheme.Reductive.FullRootSpanCenter
import Langlands.GroupScheme.Adjoint.Assembly

/-! # All-field inner automorphisms for the actual type-B model -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.OddOrthogonalMatrix.TypeBNumbering

variable {K : Type u} [Field K] {n : ℕ}
    {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]

/-- The full centre of a supplied full-root type-B pinning is trivial. -/
theorem NumberedPinning.center_eq_bot (p : NumberedPinning G n) : center G = ⊥ :=
  center_eq_bot_of_full_rootSpan p.pinning.isConnectedReductive p.pinning.isSplitTorus
    p.pinning.inclusion p.pinning.isMaximalTorus p.pinning.rootDatum
    p.pinning.isRootDatum p.rootSpan

/-- Such a full-root pinned group is actually adjoint. -/
theorem NumberedPinning.isAdjoint (p : NumberedPinning G n) : IsAdjoint G :=
  isAdjoint_of_isConnectedReductive_of_center_eq_bot p.pinning.isConnectedReductive p.center_eq_bot

/-- Its identity map is an actual adjoint quotient, with the full centre as kernel. -/
theorem NumberedPinning.isAdjointQuotient_id (p : NumberedPinning G n) :
    IsAdjointQuotient (𝟙 G) := by
  apply isAdjointQuotient_of_fppf_kernel_range (𝟙 G) p.pinning.isConnectedReductive
    p.pinning.isConnectedReductive p.center_eq_bot (by infer_instance) (by infer_instance)
    (by infer_instance)
  rw [p.center_eq_bot]
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  rw [mem_range_kernelι_iff]
  change x ≫ (𝟙 G : G ⟶ G).hom.hom = 1 ↔ x = 1
  simp

/-- The adjoint-quotient inner action is ordinary inner conjugation here. -/
theorem NumberedPinning.innerHom_id (p : NumberedPinning G n)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) :
    PinnedAutomorphismGroup.innerHom p.isAdjointQuotient_id x = G.innerIso x := by
  rw [PinnedAutomorphismGroup.innerHom_apply]
  have h := SplitPinning.innerAction_basePointIso_lift p.isAdjointQuotient_id x
  simpa using h

/-- Inner conjugation identifies actual rational points with every group-scheme
automorphism, over the original field. -/
def NumberedPinning.innerAutEquiv (p : NumberedPinning G n) (hn : 2 ≤ n) :
    (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) ≃* CategoryTheory.Aut G := by
  apply MulEquiv.ofBijective G.innerAut
  constructor
  · intro x y h
    apply PinnedAutomorphismGroup.innerHom_injective p.isAdjointQuotient_id
    rw [p.innerHom_id, p.innerHom_id]
    exact h
  · intro σ
    obtain ⟨x, θ, hσ⟩ := PinnedAutomorphismGroup.exists_eq_innerHom_mul_lift
      p.isAdjointQuotient_id p.pinning σ
    rw [p.basedRootDatumAut_eq_one hn θ, map_one, mul_one, p.innerHom_id] at hσ
    exact ⟨x, hσ.symm⟩

@[simp] theorem NumberedPinning.innerAutEquiv_apply (p : NumberedPinning G n) (hn : 2 ≤ n)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) :
    p.innerAutEquiv hn x = G.innerIso x := rfl

/-- The unique original-field conjugating point implements the actual automorphism. -/
theorem NumberedPinning.innerAutEquiv_symm_spec (p : NumberedPinning G n) (hn : 2 ≤ n)
    (σ : CategoryTheory.Aut G) :
    G.innerIso ((p.innerAutEquiv hn).symm σ) = σ :=
  (p.innerAutEquiv hn).apply_symm_apply σ

/-- Original-field rational points of the actual odd identity component
identify with its full automorphism group. -/
def identityInnerAutEquiv (hn : 2 ≤ n) :
    (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (identityComponent (groupScheme (Fin n) K)).X) ≃*
      CategoryTheory.Aut (identityComponent (groupScheme (Fin n) K)) :=
  (numberedPinning (K := K) hn).innerAutEquiv hn

/-- The full odd norm-one model has trivial scheme-theoretic centre and is adjoint. -/
theorem isAdjoint_groupScheme (hn : 2 ≤ n) : IsAdjoint (groupScheme (Fin n) K) :=
  (numberedPinning (K := K) hn).isAdjoint.of_iso (identityComponentIso hn).symm

end Langlands.GroupScheme.OddOrthogonalMatrix.TypeBNumbering
