import Langlands.GroupScheme.Rational.RelativeWeylCoxeterProof
import Langlands.Geometry.Building.RealTorusAction
import Langlands.BruhatTits.Cartan.CentralizerRealComparison

/-!
# The closed dominant chamber of the actual relative Weyl group

For a maximal split torus `i : T → G` of a connected reductive group over a field and a
generic cocharacter `ν`, the actual relative Weyl group `N(k)/Z(k)` acts on the real
cocharacter space `V(T)`. A vector is dominant if every positive relative root of `ν` is
nonnegative on it. Every orbit meets the dominant cone, and if `v` and `w • v` are both
dominant then `w • v = v`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Langlands.BruhatTits.Cartan

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.Aubert.General.RationalPointFamily

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}

section Eval

variable (T)

/-- Evaluation at a fixed real cocharacter, as an additive map on characters. -/
def evalAt (v : V T) : characterLattice T →+ ℝ where
  toFun χ := eval T χ v
  map_zero' := by simp only [eval_eq_pair, TensorProduct.tmul_zero, map_zero,
    LinearMap.zero_apply]
  map_add' χ ψ := by simp only [eval_eq_pair, TensorProduct.tmul_add, map_add,
    LinearMap.add_apply]

@[simp] theorem evalAt_apply (v : V T) (χ : characterLattice T) :
    evalAt T v χ = eval T χ v := rfl

theorem eval_add_left (χ ψ : characterLattice T) (v : V T) :
    eval T (χ + ψ) v = eval T χ v + eval T ψ v :=
  (evalAt T v).map_add χ ψ

theorem eval_neg_left (χ : characterLattice T) (v : V T) :
    eval T (-χ) v = -eval T χ v :=
  (evalAt T v).map_neg χ

theorem eval_sub_left (χ ψ : characterLattice T) (v : V T) :
    eval T (χ - ψ) v = eval T χ v - eval T ψ v :=
  (evalAt T v).map_sub χ ψ

theorem eval_zsmul_left (n : ℤ) (χ : characterLattice T) (v : V T) :
    eval T (n • χ) v = n * eval T χ v := by
  rw [← evalAt_apply, map_zsmul, evalAt_apply, zsmul_eq_mul]

theorem eval_nsmul_left (n : ℕ) (χ : characterLattice T) (v : V T) :
    eval T (n • χ) v = n * eval T χ v := by
  rw [← evalAt_apply, map_nsmul, evalAt_apply, nsmul_eq_mul]

end Eval

variable {G : GroupScheme (Spec (CommRingCat.of k))} (i : T.toGrp ⟶ G)

section Dominance

variable [IsAffineHom G.X.hom] (ν : cocharacterLattice T)

/-- A real cocharacter is dominant for `ν` when every positive relative root of `ν` is
nonnegative on it. -/
def IsDominantVector (v : V T) : Prop :=
  ∀ α ∈ positiveRelativeRoots i ν, 0 ≤ eval T α v

/-- Nonnegativity on the simple roots gives nonnegativity on all positive roots: a positive
root that is not simple is a sum of two positive roots of smaller pairing with `ν`. -/
theorem isDominantVector_of_simple {v : V T}
    (h : ∀ a ∈ simpleRelativeRoots i ν, 0 ≤ eval T a v) : IsDominantVector i ν v := by
  suffices H : ∀ n : ℕ, ∀ β ∈ positiveRelativeRoots i ν,
      latticePairing T β ν ≤ n → 0 ≤ eval T β v from
    fun β hβ => H (latticePairing T β ν).toNat β hβ (Int.self_le_toNat _)
  intro n
  induction n with
  | zero =>
    intro β hβ hn
    have := hβ.2
    push_cast at hn
    omega
  | succ n ih =>
    intro β hβ hn
    by_cases hs : β ∈ simpleRelativeRoots i ν
    · exact h β hs
    · have hdec : ∃ γ ∈ positiveRelativeRoots i ν, ∃ δ ∈ positiveRelativeRoots i ν,
          β = γ + δ := by
        by_contra hc
        exact hs ⟨hβ, hc⟩
      obtain ⟨γ, hγ, δ, hδ, rfl⟩ := hdec
      have hγp := hγ.2
      have hδp := hδ.2
      have hsum : latticePairing T (γ + δ) ν = latticePairing T γ ν + latticePairing T δ ν := by
        rw [map_add, LinearMap.add_apply]
      rw [eval_add_left]
      push_cast at hn
      exact add_nonneg (ih γ hγ (by omega)) (ih δ hδ (by omega))

end Dominance

variable [Mono i.hom.hom.left]

/-- The real cocharacter action of the relative Weyl group is contragredient to
`schemeWeylCharacterAction`. -/
theorem eval_relativeWeyl_smul (w : relativeWeylGroup i) (χ : characterLattice T)
    (v : V T) :
    eval T χ (w • v) = eval T (schemeWeylCharacterAction i w⁻¹ χ) v := by
  induction w using QuotientGroup.induction_on with
  | H n =>
    rw [relativeWeyl_mk_smul, eval_normalizer_smul, ← QuotientGroup.mk_inv,
      schemeWeylCharacterAction_mk]

theorem schemeWeylCharacterAction_inv_apply (w : relativeWeylGroup i)
    (χ : characterLattice T) :
    schemeWeylCharacterAction i w⁻¹ (schemeWeylCharacterAction i w χ) = χ := by
  rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one, LinearEquiv.coe_one, id]

variable [IsAffineHom G.X.hom] {ν : cocharacterLattice T}

variable {i}

section Realization

variable {M : CoxeterMatrix (SimpleRoot i ν)} {cs : CoxeterSystem M (relativeWeylGroup i)}
  (hcs : IsRelativeWeylCoxeterRealization i ν cs)
include hcs

/-- A simple reflection sends its root to the negative root. -/
theorem coxeterSimple_apply_self (a : SimpleRoot i ν) :
    schemeWeylCharacterAction i (cs.simple a) a.1 = -a.1 := by
  obtain ⟨f, hf, hact⟩ := hcs.1 a
  rw [hact, hf, two_smul, sub_add_cancel_left]

/-- A simple reflection fixes every real cocharacter on which its root vanishes. -/
theorem coxeterSimple_smul_eq (hT : IsSplitTorus T.toGrp)
    (a : SimpleRoot i ν) {v : V T} (hv : eval T a.1 v = 0) : cs.simple a • v = v := by
  obtain ⟨f, -, hact⟩ := hcs.1 a
  rw [← sub_eq_zero]
  apply eq_zero_of_eval_eq_zero hT
  intro χ
  rw [map_sub, eval_relativeWeyl_smul, cs.inv_simple, hact, eval_sub_left, eval_zsmul_left, hv,
    mul_zero, sub_zero, sub_self]

/-- If `w` has right descent `a`, then `w a` is a negative root. -/
theorem neg_mem_positive_of_isRightDescent
    (hν : IsGenericCocharacter i ν) {w : relativeWeylGroup i} {a : SimpleRoot i ν}
    (ha : cs.IsRightDescent w a) :
    -(schemeWeylCharacterAction i w a.1) ∈ positiveRelativeRoots i ν := by
  have haroot : a.1 ∈ relativeRoots i := (simpleRelativeRoots_subset_positive i ν a.2).1
  have hroot : ∀ u : relativeWeylGroup i, schemeWeylCharacterAction i u a.1 ∈ relativeRoots i :=
    fun u => (schemeWeylCharacterAction_image_relativeRoots i u).subset ⟨a.1, haroot, rfl⟩
  have hneg : -(schemeWeylCharacterAction i w a.1) =
      schemeWeylCharacterAction i (w * cs.simple a) a.1 := by
    rw [map_mul, LinearEquiv.mul_apply, coxeterSimple_apply_self hcs, map_neg]
  have hnotpos : schemeWeylCharacterAction i w a.1 ∉ positiveRelativeRoots i ν := by
    intro hpos
    have := (hcs.2.2.1 w a).mpr hpos
    exact (lt_asymm this) ha
  have hne := hν _ (hroot w)
  refine ⟨hneg ▸ hroot _, ?_⟩
  rw [map_neg, LinearMap.neg_apply]
  have hle : ¬ 0 < latticePairing T (schemeWeylCharacterAction i w a.1) ν :=
    fun hlt => hnotpos ⟨hroot w, hlt⟩
  omega

/-- **Uniqueness in the closed dominant chamber.** If `v` and `w • v` are dominant, then
`w • v = v`. The proof is by induction on the Coxeter length. -/
theorem relativeWeyl_smul_eq_of_isDominantVector
    (hT : IsSplitTorus T.toGrp) (hν : IsGenericCocharacter i ν)
    (w : relativeWeylGroup i) {v : V T} (hv : IsDominantVector i ν v)
    (hwv : IsDominantVector i ν (w • v)) : w • v = v := by
  suffices H : ∀ n : ℕ, ∀ w : relativeWeylGroup i, cs.length w = n →
      IsDominantVector i ν (w • v) → w • v = v from H _ w rfl hwv
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro w hn hwv
    by_cases hw : w = 1
    · rw [hw, one_smul]
    obtain ⟨a, ha⟩ := cs.exists_rightDescent_of_ne_one hw
    have hpos := neg_mem_positive_of_isRightDescent hcs hν ha
    have h1 := hwv _ hpos
    rw [eval_relativeWeyl_smul, map_neg, schemeWeylCharacterAction_inv_apply,
      eval_neg_left] at h1
    have h2 := hv a.1 (simpleRelativeRoots_subset_positive i ν a.2)
    have hzero : eval T a.1 v = 0 := le_antisymm (by linarith) h2
    have hfix := coxeterSimple_smul_eq hcs hT a hzero
    have hws : (w * cs.simple a) • v = w • v := by rw [mul_smul, hfix]
    rw [← hws]
    exact ih _ (hn ▸ ha) _ rfl (hws ▸ hwv)

/-- The positive roots negative on `v`. -/
private def negativeSet (v : V T) : Set (characterLattice T) :=
  {β | β ∈ positiveRelativeRoots i ν ∧ eval T β v < 0}

/-- A simple reflection at a simple root negative on `v` removes that root from the set of
positive roots negative on `v`, and permutes the others. -/
private theorem ncard_negativeSet_simple_lt (hfin : (relativeRoots i).Finite)
    (a : SimpleRoot i ν) {v : V T} (ha : eval T a.1 v < 0) :
    (negativeSet (i := i) (ν := ν) (cs.simple a • v)).ncard <
      (negativeSet (i := i) (ν := ν) v).ncard := by
  have hfinN : (negativeSet (i := i) (ν := ν) v).Finite :=
    hfin.subset fun β hβ => hβ.1.1
  have haN : a.1 ∈ negativeSet (i := i) (ν := ν) v :=
    ⟨simpleRelativeRoots_subset_positive i ν a.2, ha⟩
  have hapos := (simpleRelativeRoots_subset_positive i ν a.2).2
  let s := schemeWeylCharacterAction i (cs.simple a)
  have hs_eval : ∀ β, eval T β (cs.simple a • v) = eval T (s β) v := by
    intro β
    rw [eval_relativeWeyl_smul, cs.inv_simple]
  have hsa : s a.1 = -a.1 := coxeterSimple_apply_self hcs a
  have hss : ∀ β, s (s β) = β := by
    intro β
    change schemeWeylCharacterAction i (cs.simple a)
      (schemeWeylCharacterAction i (cs.simple a) β) = β
    rw [← LinearEquiv.mul_apply, ← map_mul, cs.simple_mul_simple_self, map_one,
      LinearEquiv.coe_one, id]
  calc (negativeSet (i := i) (ν := ν) (cs.simple a • v)).ncard
      ≤ (negativeSet (i := i) (ν := ν) v \ {a.1}).ncard := by
        apply Set.ncard_le_ncard_of_injOn s _ (s.injective.injOn) (hfinN.subset Set.sdiff_subset)
        rintro β ⟨hβ, hβv⟩
        rw [hs_eval] at hβv
        have hβa : β ≠ a.1 := by
          rintro rfl
          rw [hsa, eval_neg_left] at hβv
          linarith
        have hβ2a : β ≠ 2 • a.1 := by
          rintro rfl
          rw [map_nsmul, hsa, eval_nsmul_left, eval_neg_left] at hβv
          push_cast at hβv
          linarith
        have hsβ := hcs.2.1 a β hβ hβa hβ2a
        refine ⟨⟨hsβ, hβv⟩, ?_⟩
        intro heq
        have heq' : β = -a.1 := by
          rw [← hss β, Set.mem_singleton_iff.mp heq, hsa]
        have hβp := hβ.2
        rw [heq', map_neg, LinearMap.neg_apply] at hβp
        omega
    _ < (negativeSet (i := i) (ν := ν) v).ncard :=
        Set.ncard_lt_ncard (Set.sdiff_singleton_ssubset.mpr haN) hfinN

/-- **Existence in the closed dominant chamber.** Every orbit of the relative Weyl group on
`V(T)` meets the dominant cone. -/
theorem exists_relativeWeyl_smul_isDominantVector
    (hfin : (relativeRoots i).Finite) (v : V T) :
    ∃ w : relativeWeylGroup i, IsDominantVector i ν (w • v) := by
  suffices H : ∀ n : ℕ, ∀ v : V T, (negativeSet (i := i) (ν := ν) v).ncard = n →
      ∃ w : relativeWeylGroup i, IsDominantVector i ν (w • v) from H _ v rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hn
    by_cases hdom : ∀ a ∈ simpleRelativeRoots i ν, 0 ≤ eval T a v
    · exact ⟨1, by simpa only [one_smul] using isDominantVector_of_simple i ν hdom⟩
    simp only [not_forall, not_le] at hdom
    obtain ⟨a, ha, hav⟩ := hdom
    have hlt := ncard_negativeSet_simple_lt hcs hfin ⟨a, ha⟩ hav
    obtain ⟨w, hw⟩ := ih _ (hn ▸ hlt) (cs.simple ⟨a, ha⟩ • v) rfl
    exact ⟨w * cs.simple ⟨a, ha⟩, by rwa [mul_smul]⟩

end Realization

section Reductive

/-- For a maximal split torus of a connected reductive group and a generic cocharacter,
two dominant vectors in one orbit of the actual relative Weyl group are equal. -/
theorem relativeWeyl_smul_eq_of_isDominantVector_of_reductive (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν) (w : relativeWeylGroup i)
    {v : V T} (hv : IsDominantVector i ν v) (hwv : IsDominantVector i ν (w • v)) :
    w • v = v := by
  obtain ⟨-, -, M, cs, hcs⟩ := relativeWeylCoxeter k G hG T i hi ν hν
  exact relativeWeyl_smul_eq_of_isDominantVector hcs hi.isSplitSubtorus.1 hν w hv hwv

/-- For a maximal split torus of a connected reductive group and a generic cocharacter,
every orbit of the actual relative Weyl group on `V(T)` meets the dominant cone. -/
theorem exists_relativeWeyl_smul_isDominantVector_of_reductive (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν) (v : V T) :
    ∃ w : relativeWeylGroup i, IsDominantVector i ν (w • v) := by
  obtain ⟨-, -, M, cs, hcs⟩ := relativeWeylCoxeter k G hG T i hi ν hν
  have : LocallyOfFiniteType G.X.hom := by
    have := hG.smooth
    infer_instance
  exact exists_relativeWeyl_smul_isDominantVector hcs
    (hi.isSplitSubtorus.1.finite_relativeRoots i) v

end Reductive

end Langlands.BruhatTits.Cartan
