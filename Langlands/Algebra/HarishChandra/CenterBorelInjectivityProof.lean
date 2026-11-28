import Langlands.Algebra.EnvelopingFixedWeightDecomposition
import Langlands.Algebra.HarishChandra.CenterBorelWeightBasis

/-! # Injectivity of the center projection at a split Cartan -/

noncomputable section

universe v

set_option autoImplicit false

namespace Langlands.Algebra.HarishChandra

attribute [local instance 100] LieRing.ofAssociativeRing

open LieModule Finsupp UniversalEnveloping

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] {r : ℕ}
  (b : Module.Basis (Fin r) ℂ L)

local notation "U" => UniversalEnvelopingAlgebra ℂ L
local notation "ι" => UniversalEnvelopingAlgebra.ι ℂ

private def augmentation : U →ₐ[ℂ] ℂ :=
  UniversalEnvelopingAlgebra.lift ℂ (0 : L →ₗ⁅ℂ⁆ ℂ)

private theorem augmentation_generator (x : L) :
    augmentation (ι x) = 0 := by
  rw [augmentation, UniversalEnvelopingAlgebra.lift_ι_apply]
  rfl

private theorem augmentation_eq_zero_coordinate (u : U) :
    augmentation u = (orderedPBWBasisOf b).repr u 0 := by
  classical
  have h : (augmentation (L := L)).toLinearMap = (orderedPBWBasisOf b).coord 0 := by
    apply (orderedPBWBasisOf b).ext
    intro e
    rw [AlgHom.toLinearMap_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
      orderedPBWBasisOf_apply]
    by_cases he : e = 0
    · subst e
      rw [show (0 : Fin r → ℕ) = fun _ => 0 from rfl, orderedPBWMonomial_zero, map_one]
      simp
    · have hEval : augmentation (orderedPBWMonomial b e) = 0 := by
        rw [orderedPBWMonomial, map_list_prod, List.map_ofFn, List.prod_ofFn]
        have hNonzero : ∃ i, e i ≠ 0 := by
          by_contra! hz
          exact he (funext hz)
        obtain ⟨i, hi⟩ := hNonzero
        refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
        change augmentation (ι (b i) ^ e i) = 0
        rw [map_pow, augmentation_generator, zero_pow hi]
      simp [hEval, Ne.symm he]
  exact LinearMap.congr_fun h u

private theorem generatorRightIdeal_le_positivePBWSpan
    (p : Fin r → Prop) [DecidablePred p]
    (hOrder : ∀ i j, p i → ¬ p j → i < j)
    (hBracket : ∀ i j, p i → p j →
      ⁅b i, b j⁆ ∈ Submodule.span ℂ (b '' {i | p i})) :
    generatorRightIdeal (Submodule.span ℂ (b '' {i | p i})) ≤
      Submodule.span ℂ (orderedPBWBasisOf b '' {e | ∃ i, p i ∧ e i ≠ 0}) := by
  classical
  let S := Submodule.span ℂ (orderedPBWBasisOf b '' {e | ∃ i, p i ∧ e i ≠ 0})
  have hGenerator (i : Fin r) (hi : p i) (e : Fin r → ℕ) :
      ι (b i) * orderedPBWMonomial b e ∈ S := by
    let ePos (i : Fin r) := if p i then e i else 0
    let eRest (i : Fin r) := if p i then 0 else e i
    have hOnlyPos (i : Fin r) (hi : ePos i ≠ 0) : p i := by
      by_contra h
      exact hi (by simp [ePos, h])
    have hSplitOrder (f : Fin r → ℕ) (hf : ∀ i, f i ≠ 0 → p i) :
        ∀ i j, f i ≠ 0 → eRest j ≠ 0 → i < j :=
      fun i j hi hj => hOrder i j (hf i hi) (fun hj' => hj (by simp [eRest, hj']))
    have hSplit : orderedPBWMonomial b e =
        orderedPBWMonomial b ePos * orderedPBWMonomial b eRest := by
      rw [orderedPBWMonomial, orderedPBWMonomial, orderedPBWMonomial,
        ← ofFn_prod_pow_add _ ePos eRest (hSplitOrder ePos hOnlyPos)]
      congr 1
      apply congrArg List.ofFn
      funext j
      by_cases hj : p j <;> simp [ePos, eRest, hj]
    let x := ι (b i) * orderedPBWMonomial b ePos
    have hx : x ∈ Algebra.adjoin ℂ {u | ∃ a, p a ∧ u = ι (b a)} :=
      Subalgebra.mul_mem _ (Algebra.subset_adjoin ⟨i, hi, rfl⟩)
        (ofFn_prod_pow_mem_adjoin _ p ePos hOnlyPos)
    have hxSpan :=
      adjoin_le_span_orderedPBWBasisOf b p hBracket hx
    have hxConstant : (orderedPBWBasisOf b).repr x 0 = 0 := by
      rw [← augmentation_eq_zero_coordinate b, show x = ι (b i) * orderedPBWMonomial b ePos from
        rfl, map_mul, augmentation_generator, zero_mul]
    rw [hSplit, ← mul_assoc]
    change x * orderedPBWMonomial b eRest ∈ S
    rw [← (orderedPBWBasisOf b).linearCombination_repr x, Finsupp.linearCombination_apply,
      Finsupp.sum, Finset.sum_mul]
    refine Submodule.sum_mem _ fun f hf => ?_
    rw [smul_mul_assoc]
    refine S.smul_mem _ ?_
    have hfCoeff := Finsupp.mem_support_iff.mp hf
    have hPos (j : Fin r) (hj : f j ≠ 0) : p j := by
      by_contra hNot
      exact hfCoeff (repr_eq_zero_of_mem_span _ _ hxSpan (fun h => hNot (h j hj)))
    obtain ⟨j, hj⟩ : ∃ j, f j ≠ 0 := by
      by_contra! h
      have hfZero : f = 0 := funext h
      exact hfCoeff (by rwa [hfZero])
    apply Submodule.subset_span
    refine ⟨fun a => f a + eRest a, ⟨j, hPos j hj, ?_⟩, ?_⟩
    · change f j + eRest j ≠ 0
      omega
    · rw [orderedPBWBasisOf_apply, orderedPBWBasisOf_apply, orderedPBWMonomial,
        orderedPBWMonomial, orderedPBWMonomial, ofFn_prod_pow_add _ f eRest (hSplitOrder f hPos)]
  change generatorRightIdeal _ ≤ S
  rw [generatorRightIdeal, Submodule.span_le]
  rintro _ ⟨x, hx, u, rfl⟩
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, hi, rfl⟩ := hy
    rw [← (orderedPBWBasisOf b).linearCombination_repr u, Finsupp.linearCombination_apply,
      Finsupp.sum, Finset.mul_sum]
    refine Submodule.sum_mem _ fun e _ => ?_
    rw [mul_smul_comm, orderedPBWBasisOf_apply]
    exact S.smul_mem _ (hGenerator i hi e)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, add_mul]; exact S.add_mem hx hy
  | smul c y _ hy => rw [map_smul, smul_mul_assoc]; exact S.smul_mem _ hy

/-- The center has zero intersection with the right ideal of positive root directions. -/
theorem centerBorelInjectivity : CenterBorelInjectivityStatement.{v} := by
  classical
  intro L _ _ _ H hCartan X _hRegular z hCenter hIdeal
  obtain ⟨r, b, χ, hb, hLine, hSort⟩ := hCartan.exists_ordered_weight_basis X
  let p (i : Fin r) : Prop := 0 < (χ i X).re
  have hOrder (i j : Fin r) (hi : p i) (hj : ¬ p j) : i < j := by
    by_contra! h
    exact hj (lt_of_lt_of_le hi (hSort h))
  have hBracket (i j : Fin r) (hi : p i) (hj : p j) :
      ⁅b i, b j⁆ ∈ Submodule.span ℂ (b '' {i | p i}) := by
    rw [← positiveRootSubmodule_eq_span b χ hb X]
    have hpos : 0 < ((χ i + χ j) X).re := by
      change 0 < ((χ i X) + (χ j X)).re
      rw [Complex.add_re]
      exact add_pos hi hj
    exact Submodule.mem_iSup_of_mem (χ i + χ j)
      (Submodule.mem_iSup_of_mem hpos (bracket_mem_weightSpace_add (hb i) (hb j)))
  have hPosSpan : z ∈ Submodule.span ℂ (orderedPBWBasisOf b '' {e | ∃ i, p i ∧ e i ≠ 0}) :=
    generatorRightIdeal_le_positivePBWSpan b p hOrder hBracket
      (by rwa [← positiveRootSubmodule_eq_span b χ hb X])
  let w (i : Fin r) : ℕ := if χ i = 0 then 0 else 1
  refine cartanCenterProjectionInjectivity b w ?_ ?_ z hCenter ?_
  · intro i
    by_cases hi : χ i = 0 <;> simp [w, hi]
  · intro i hi
    have hi' : χ i ≠ 0 := by simpa [w] using hi
    obtain ⟨x, hx, hxOff⟩ := exists_transverse_weight_bracket b χ hb hCartan hLine i hi'
    exact ⟨x, hx, fun j hj hj' => hxOff j (by simpa [w] using hj) hj'⟩
  · intro a ha
    change (orderedPBWBasisOf b).repr z (fun i => a i) = 0
    refine repr_eq_zero_of_mem_span _ _ hPosSpan ?_
    rintro ⟨i, hi, hai⟩
    have hχ : χ i ≠ 0 := by
      intro h
      simp [p, h] at hi
    rw [weight_eq_sum, Finset.sum_eq_zero_iff] at ha
    exact hai (by simpa [w, hχ] using ha i (Finset.mem_univ i))

end Langlands.Algebra.HarishChandra
