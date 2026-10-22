import Langlands.Global.ProfiniteIntegerCompletionComparison
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Topology.Homeomorph.Lemmas

noncomputable section

namespace Langlands.Global

open Langlands.Weil ProfiniteGrp CategoryTheory

private theorem residue_integer_dense : DenseRange ProfiniteIntegerRing.intCastHom := by
  classical
  apply dense_iff_inter_open.mpr
  rintro U ⟨s, hsO, hsv⟩ ⟨x, hx⟩
  rw [← hsv, Set.mem_preimage] at hx
  obtain ⟨J, V, hV, hJV⟩ := isOpen_pi_iff.mp hsO x.val hx
  let m : ℕ+ := ⟨∏ i ∈ J, (i : ℕ), Finset.prod_pos (fun i _ => i.pos)⟩
  obtain ⟨z, hz⟩ := ZMod.intCast_surjective (ProfiniteIntegerRing.reduction m x)
  refine ⟨ProfiniteIntegerRing.intCastHom z, ?_, z, rfl⟩
  rw [← hsv]
  apply hJV
  intro i hi
  have hd : (i : ℕ) ∣ (m : ℕ) := Finset.dvd_prod_of_mem (fun i : ℕ+ => (i : ℕ)) hi
  have he : (z : ZMod (i : ℕ)) = ProfiniteIntegerRing.reduction i x := by
    rw [← ResidueLimit.transition_intCast hd, hz]
    exact ResidueLimit.compatible x i m hd
  change (z : ZMod (i : ℕ)) ∈ V i
  rw [he]
  exact (hV i hi).2

private def integerHom : Degree →* Multiplicative ProfiniteIntegerRing :=
  ProfiniteIntegerRing.intCastHom.toAddMonoidHom.toMultiplicative

private def completionToResidues : ProfiniteIntegers →ₜ* Multiplicative ProfiniteIntegerRing :=
  (ProfiniteCompletion.lift (P := ProfiniteGrp.of (Multiplicative ProfiniteIntegerRing))
    (GrpCat.ofHom integerHom)).hom

private theorem completionToResidues_integer (z : Degree) :
    completionToResidues (frobenius z) = integerHom z := by
  exact ConcreteCategory.congr_hom (ProfiniteCompletion.lift_eta
    (P := ProfiniteGrp.of (Multiplicative ProfiniteIntegerRing)) (GrpCat.ofHom integerHom)) z

private theorem finite_factorization {H : Type} [Group H] [Finite H]
    (f : Degree →* H) :
    ∃ (n : ℕ+) (g : Multiplicative (ZMod (n : ℕ)) →* H),
      ∀ z : ℤ, g (Multiplicative.ofAdd (z : ZMod (n : ℕ))) = f (Multiplicative.ofAdd z) := by
  let : Finite (Additive H) := Finite.of_equiv H Additive.ofMul
  let n : ℕ+ := ⟨Nat.card (Additive H), Nat.card_pos⟩
  have hzero : f.toAdditiveRight (n : ℕ) = 0 := by
    have hn : (n : ℤ) = (n : ℕ) • (1 : ℤ) := by simp
    rw [hn, map_nsmul]
    exact card_nsmul_eq_zero'
  refine ⟨n, (ZMod.lift (n : ℕ) ⟨f.toAdditiveRight, hzero⟩).toMultiplicativeLeft, ?_⟩
  intro z
  exact congrArg Additive.toMul (ZMod.lift_coe (n : ℕ) ⟨f.toAdditiveRight, hzero⟩ z)

private theorem completionToResidues_injective : Function.Injective completionToResidues := by
  intro x y hxy
  apply Subtype.ext
  funext N
  let Q := (ProfiniteCompletion.diagram (GrpCat.of Degree)).obj N
  have : Finite Q := by
    change Finite (Degree ⧸ N.toSubgroup)
    infer_instance
  let π : ProfiniteIntegers →ₜ* Q :=
    ((limitCone (ProfiniteCompletion.diagram (GrpCat.of Degree))).π.app N).hom
  obtain ⟨n, g, hg⟩ := finite_factorization (QuotientGroup.mk' N.toSubgroup)
  let c : Multiplicative ProfiniteIntegerRing → Q :=
    fun t => g (Multiplicative.ofAdd (ProfiniteIntegerRing.reduction n t.toAdd))
  have hc : Continuous c :=
    (continuous_of_discreteTopology (f := g)).comp (ResidueLimit.continuous_reduction n)
  have heq : c ∘ completionToResidues = π := by
    apply (ProfiniteCompletion.denseRange (G := GrpCat.of Degree)).equalizer
      (hc.comp completionToResidues.continuous) π.continuous
    funext z
    change c (completionToResidues (frobenius z)) = QuotientGroup.mk' N.toSubgroup z
    rw [completionToResidues_integer]
    exact hg z.toAdd
  change π x = π y
  exact (congrFun heq x).symm.trans ((congrArg c hxy).trans (congrFun heq y))

private theorem completionToResidues_surjective : Function.Surjective completionToResidues := by
  have hd : DenseRange integerHom := residue_integer_dense
  have hsub : Set.range integerHom ⊆ Set.range completionToResidues := by
    rintro _ ⟨z, rfl⟩
    exact ⟨frobenius z, completionToResidues_integer z⟩
  have hd' : Dense (Set.range completionToResidues) := hd.mono hsub
  have hclosed : IsClosed (Set.range completionToResidues) :=
    isCompact_range completionToResidues.continuous |>.isClosed
  exact Set.range_eq_univ.mp (hclosed.closure_eq.symm.trans hd'.closure_eq)

/-- The normalized continuous additive-group comparison of the residue ring
with the actual profinite completion of the integer group. -/
theorem profiniteIntegerCompletionComparison : ProfiniteIntegerCompletionComparison := by
  let e := MulEquiv.ofBijective completionToResidues.toMonoidHom
    ⟨completionToResidues_injective, completionToResidues_surjective⟩
  have he : Continuous e := completionToResidues.continuous
  refine ⟨e.symm, he.continuous_symm_of_equiv_compact_to_t2, he, ?_⟩
  intro z
  apply e.injective
  rw [e.apply_symm_apply]
  exact (completionToResidues_integer (Multiplicative.ofAdd z)).symm

end Langlands.Global
