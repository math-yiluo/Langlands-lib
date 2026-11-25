/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import WeilConjectures.AlgebraicGeometry.FunctionField
import WeilConjectures.Mathlib.Topology.KrullDimension
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import WeilConjectures.AlgebraicGeometry.Regular

/-!
# Local rings and normalized valuations of a smooth connected curve

Source: Stacks Project, Properties, Tags 033M and 02IZ; Algebra, Tag 00PD;
the standing setting of Divisors, Tag 0BE9
(blueprint: lem-sc-smooth-connected-curve-local-rings).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- The normalized valuation comes from the maximal-ideal adic valuation, so it is
independent of a chosen uniformizer. The unit-times-integer-power decomposition is
Mathlib's fraction-field form of Stacks Algebra, Tag 00PD. Applying the valuation
identifies the exponent, and cancellation identifies the unit. The valuation subring
characterization gives exactly the nonnegative values. -/
private theorem normalized_dvr_valuation
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] :
    ∃ v : Kˣ →* Multiplicative ℤ,
      Function.Surjective v ∧
      (∀ t : R, IsLocalRing.maximalIdeal R = Ideal.span {t} → ∀ g : Kˣ,
        (∃! q : Rˣ × ℤ,
          (g : K) = algebraMap R K (q.1 : R) * (algebraMap R K t) ^ q.2) ∧
        (∀ q : Rˣ × ℤ,
          (g : K) = algebraMap R K (q.1 : R) * (algebraMap R K t) ^ q.2 →
            Multiplicative.toAdd (v g) = q.2)) ∧
      (∀ g : Kˣ,
        (∃ r : R, r ≠ 0 ∧ algebraMap R K r = (g : K)) ↔
          0 ≤ Multiplicative.toAdd (v g)) := by
  classical
  let w := (IsDiscreteValuationRing.maximalIdeal R).valuation K
  have hw (g : Kˣ) : w (g : K) ≠ 0 :=
    (Valuation.ne_zero_iff w).mpr g.ne_zero
  let v : Kˣ →* Multiplicative ℤ :=
    { toFun := fun g ↦ Multiplicative.ofAdd (-WithZero.log (w (g : K)))
      map_one' := by simp
      map_mul' := by
        intro g h
        apply Multiplicative.toAdd.injective
        change -WithZero.log (w ((g * h : Kˣ) : K)) =
          -WithZero.log (w (g : K)) + -WithZero.log (w (h : K))
        simp only [Units.val_mul, map_mul, WithZero.log_mul (hw g) (hw h), neg_add] }
  have hv (g : Kˣ) : Multiplicative.toAdd (v g) = -WithZero.log (w (g : K)) := rfl
  have hu (a : Rˣ) : w (algebraMap R K (a : R)) = 1 := by
    apply ((IsDiscreteValuationRing.maximalIdeal R).valuation_eq_one_iff_notMem (K := K)).mpr
    simp [IsDiscreteValuationRing.maximalIdeal, IsLocalRing.mem_maximalIdeal]
  have htval (t : R) (ht : IsLocalRing.maximalIdeal R = Ideal.span {t}) :
      w (algebraMap R K t) = WithZero.exp (-1 : ℤ) := by
    have hirr := (IsDiscreteValuationRing.irreducible_iff_uniformizer t).mpr ht
    exact (IsDiscreteValuationRing.maximalIdeal R).valuation_of_algebraMap t |>.trans
      ((IsDiscreteValuationRing.maximalIdeal R).intValuation_singleton hirr.ne_zero ht)
  have hexponent (t : R) (ht : IsLocalRing.maximalIdeal R = Ideal.span {t})
      (g : Kˣ) (q : Rˣ × ℤ)
      (hq : (g : K) = algebraMap R K (q.1 : R) * (algebraMap R K t) ^ q.2) :
      Multiplicative.toAdd (v g) = q.2 := by
    rw [hv, hq, map_mul, hu, one_mul, map_zpow₀, htval t ht]
    simp
  refine ⟨v, ?_, ?_, ?_⟩
  · obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible R
    intro n
    have ht0 : algebraMap R K t ≠ 0 := by
      simpa using (IsFractionRing.injective R K).ne ht.ne_zero
    refine ⟨Units.mk0 (algebraMap R K t) ht0 ^ Multiplicative.toAdd n, ?_⟩
    apply Multiplicative.toAdd.injective
    exact hexponent t ht.maximalIdeal_eq _ (1, Multiplicative.toAdd n) (by simp)
  · intro t ht g
    have hirr := (IsDiscreteValuationRing.irreducible_iff_uniformizer t).mpr ht
    obtain ⟨n, a, ha⟩ :=
      IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hirr g.ne_zero
    have ha' : (g : K) = algebraMap R K (a : R) * (algebraMap R K t) ^ n := by
      simpa [Units.smul_def, Algebra.smul_def] using ha
    refine ⟨⟨(a, n), ha', ?_⟩, hexponent t ht g⟩
    intro q hq
    have hn : q.2 = n := (hexponent t ht g q hq).symm.trans
      (hexponent t ht g (a, n) ha')
    apply Prod.ext
    · apply Units.ext
      apply IsFractionRing.injective R K
      have heq := hq.symm.trans ha'
      rw [hn] at heq
      have ht0 : algebraMap R K t ≠ 0 := by
        simpa using (IsFractionRing.injective R K).ne hirr.ne_zero
      exact mul_right_cancel₀ (zpow_ne_zero _ ht0) heq
    · exact hn
  · intro g
    constructor
    · rintro ⟨a, ha, hmap⟩
      rw [hv, neg_nonneg, ← WithZero.log_one,
        WithZero.log_le_log (hw g) one_ne_zero, ← hmap]
      exact (IsDiscreteValuationRing.maximalIdeal R).valuation_le_one a
    · intro hg
      have hle : w (g : K) ≤ 1 := by
        rw [← WithZero.log_le_log (hw g) one_ne_zero, WithZero.log_one]
        exact neg_nonneg.mp hg
      obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hle
      exact ⟨a, fun hzero ↦ g.ne_zero (by simpa [hzero] using ha.symm), ha⟩

/-- A smooth connected curve over an algebraically closed field is Noetherian and integral,
its nongeneric points are exactly its closed points, and its closed stalks are DVRs with
fraction field the generic stalk. Their normalized valuations are independent of uniformizer.
Source: Stacks Project, Properties, Tags 033M and 02IZ; Algebra, Tag 00PD; the standing
hypotheses of Divisors, Tag 0BE9 (blueprint: lem-sc-smooth-connected-curve-local-rings).

Proof:
1. Finite type over the Noetherian field spectrum gives Noetherianity
   (`lem-weil-pbc-finite-type-over-noetherian`). Smoothness gives regular local rings
   (`lem-sc-smooth-regular`, `def-weil-regular-scheme`).
2. Nonempty connected regular schemes are integral (`lem-sc-regular-connected-integral`,
   the regular form of 033M). Integrality implies irreducibility
   (`lem-pc-integral-scheme-irreducible`); sobriety gives the unique generic point
   (`lem-sc-scheme-sober`). It belongs to every nonempty open. The generic stalk is a field
   (`lem-sc-integral-function-field-affine-fraction`). Germ maps and specialization maps
   to this field are injective, and each stalk has it as fraction field
   (`lem-sc-integral-scheme-stalks-in-function-field`).
3. Sobriety makes distinct points have distinct closures. Every nonempty closed subset of
   the quasi-compact underlying space contains a closed point
   (`lem-sc-quasi-compact-kolmogorov-closed-point`). In particular closed points exist.
4. A strict chain of two generalizations would give dimension at least two, excluded by
   dimension one (`lem-sc-scheme-stalk-dimension-generalization-chains`,
   `def-kun-topological-krull-dimension`, `def-pc-dimension`). A one-point scheme would
   have dimension zero, so the generic point is not closed.
5. If a nongeneric point were not closed, a closed point in its closure, that point, and
   the generic point would form a forbidden length-two chain. Thus it is closed.
6. At a closed point, the chain from it to the generic point has length one, and no longer
   chain exists. Thus its stalk has dimension one (02IZ and
   `lem-sc-scheme-stalk-dimension-generalization-chains`).
7. Its regular local ring of dimension one is a DVR (`lem-sc-regular-dim1-dvr`, 00PD).
   Its fraction field is the generic stalk by step 2.
8. Fix a uniformizer t. Each nonzero stalk element is a unit times a nonnegative power of t
   (`lem-weil-pbc-dvr-unit-times-uniformizer-power`). Express a nonzero fraction a/b using
   these forms to obtain u times an integer power of t. Two different exponents would put
   a unit in the maximal ideal, so the exponent and then the unit are unique. A different
   uniformizer is a unit times t, so the exponent is unchanged. Multiplication adds
   exponents; powers of t realize all integers; the nonzero stalk elements are exactly
   the fractions with nonnegative exponent.

The existential integral instance is a conclusion, not an additional hypothesis. For this
integral curve `C.functionField` is the generic stalk, as in `def-sc-function-field`.
The homomorphism uses `Multiplicative ℤ` to express an additive integer valuation on the
multiplicative group of nonzero field elements. -/
theorem Scheme.smooth_connected_curve_local_rings
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] :
    ∃ hC : IsIntegral C,
      letI := hC
      IsNoetherian C ∧
      IsGenericPoint (genericPoint C) (Set.univ : Set C) ∧
      IsField C.functionField ∧
      (∀ (V : C.Opens) (_ : Nonempty V) (x : V),
        Function.Injective (C.presheaf.germ V x x.property)) ∧
      (∀ x : C, Function.Injective (algebraMap (C.presheaf.stalk x) C.functionField)) ∧
      (∀ x : C, x ≠ genericPoint C → x ∈ closedPoints C) ∧
      genericPoint C ∉ closedPoints C ∧
      (∃ P : C, P ∈ closedPoints C) ∧
      (∀ P : C, P ∈ closedPoints C →
        IsDiscreteValuationRing (C.presheaf.stalk P) ∧
        IsFractionRing (C.presheaf.stalk P) C.functionField ∧
        ∃ v : C.functionFieldˣ →* Multiplicative ℤ,
          Function.Surjective v ∧
          (∀ (t : C.presheaf.stalk P),
            IsLocalRing.maximalIdeal (C.presheaf.stalk P) = Ideal.span {t} →
            ∀ g : C.functionFieldˣ,
              (∃! q : (C.presheaf.stalk P)ˣ × ℤ,
                (g : C.functionField) =
                  algebraMap (C.presheaf.stalk P) C.functionField (q.1 : C.presheaf.stalk P) *
                    (algebraMap (C.presheaf.stalk P) C.functionField t) ^ q.2) ∧
              (∀ q : (C.presheaf.stalk P)ˣ × ℤ,
                (g : C.functionField) =
                    algebraMap (C.presheaf.stalk P) C.functionField (q.1 : C.presheaf.stalk P) *
                      (algebraMap (C.presheaf.stalk P) C.functionField t) ^ q.2 →
                  Multiplicative.toAdd (v g) = q.2)) ∧
          (∀ g : C.functionFieldˣ,
            (∃ r : C.presheaf.stalk P, r ≠ 0 ∧
              algebraMap (C.presheaf.stalk P) C.functionField r = (g : C.functionField)) ↔
            0 ≤ Multiplicative.toAdd (v g))) := by
  classical
  let := IsConnectedCurve.connectedSpace (f := f)
  let := LocallyOfFiniteType.isLocallyNoetherian f
  let := QuasiCompact.compactSpace_of_compactSpace f
  let := IsRegular.of_smooth f
  let := IsRegular.isIntegral C
  have hηnot : genericPoint C ∉ closedPoints C := by
    intro hη
    have hsingleton : (Set.univ : Set C) = {genericPoint C} :=
      (genericPoint_spec C).symm.trans hη.closure_eq
    have : Subsingleton C := ⟨fun x y ↦ by
      have hx : x = genericPoint C := Set.mem_singleton_iff.mp (hsingleton ▸ Set.mem_univ x)
      have hy : y = genericPoint C := Set.mem_singleton_iff.mp (hsingleton ▸ Set.mem_univ y)
      exact hx.trans hy.symm⟩
    have hzero := topologicalKrullDim_zero_of_discreteTopology C
    rw [IsConnectedCurve.krullDim_eq_one (f := f)] at hzero
    exact (by decide : ¬ (1 : WithBot ℕ∞) ≤ 0) hzero
  refine ⟨inferInstance, ⟨⟩, genericPoint_spec C, Field.toIsField _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro V hV x
    exact germ_injective_of_isIntegral _ _ _
  · intro x
    exact IsFractionRing.injective _ _
  · intro x hx
    change IsClosed {x}
    by_contra hc
    have heq : closure {x} = (Set.univ : Set C) := by
      by_contra hne
      exact hc (IsOpen.isClosed_singleton_of_mem_compl
        (IsCurve.krullDim_le_one (f := f)) isClosed_closure.isOpen_compl
        (Set.nonempty_compl.mpr hne) fun hmem ↦ hmem (subset_closure rfl))
    exact hx ((show IsGenericPoint x Set.univ from heq).eq (genericPoint_spec C))
  · exact hηnot
  · obtain ⟨P, -, hP⟩ := isClosed_univ.exists_closed_singleton (X := C) Set.univ_nonempty
    exact ⟨P, hP⟩
  · intro P hP
    let := specializationOrder C
    have hdim : ringKrullDim (C.presheaf.stalk P) = 1 := by
      have hupper := (ringKrullDim_stalk_le_topologicalKrullDim P).trans
        (IsCurve.krullDim_le_one (f := f))
      rw [ringKrullDim_stalk_eq_coheight] at hupper ⊢
      have hlt : P < genericPoint C := lt_of_le_of_ne (a := P) (b := genericPoint C)
        (show genericPoint C ⤳ P from (genericPoint_spec C).specializes trivial)
        (fun heq ↦ hηnot (heq ▸ hP))
      have hlower := Order.coheight_add_one_le hlt
      have hone : (1 : ℕ∞) ≤ Order.coheight P :=
        le_trans (by simp) hlower
      exact le_antisymm hupper (by exact_mod_cast hone)
    let := IsRegularLocalRing.isDiscreteValuationRing (C.presheaf.stalk P) hdim
    refine ⟨inferInstance, inferInstance, ?_⟩
    exact normalized_dvr_valuation (C.presheaf.stalk P) C.functionField

end AlgebraicGeometry
