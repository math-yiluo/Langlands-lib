/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeights
public import WeilConjectures.Mathlib.Data.Multiset.UnionInter
public import WeilConjectures.RepresentationTheory.ExteriorPowerFiltration

/-!
# Determinant weights of exterior powers

Let `ρ` be a nonzero lisse Weil sheaf on a smooth geometrically connected curve `C₀ / 𝔽_q`, with
rank-counted list of determinant weights `L` (`AlgebraicGeometry.WeilGroup.rankDetWeightMultiset`:
the determinant weight `γ_a` of every composition factor `A_a` repeated `dim A_a` times). This file
proves that the determinant weights of the constituents of the exterior power `⋀^r ρ` are exactly
the sums of `r` entries of `L` (blueprint `proposition-determinant-weights-tensor-operations--2`).

The proof is by induction on the rank. For irreducible `ρ` it is the semisimple case
`Representation.exists_multiset_le_and_detWeight_eq_sum_of_exteriorPower`. Otherwise `ρ` has a
proper nonzero subrepresentation `A`, and `⋀^r ρ` has a filtration with steps
`⋀^j A ⊗ ⋀^{r - j} (ρ / A)` (`Subrepresentation.exteriorPowerGradedEquiv`); the
two-factor tensor rule (`Representation.exists_detWeight_eq_add_of_subquotient_tprod` and its
converse) and the additivity `L(ρ) = L(A) + L(ρ / A)`
(`AlgebraicGeometry.WeilGroup.rankDetWeightMultiset_eq_add`) reduce the claim to `A` and `ρ / A`.
The finite geometric determinant hypotheses of the tensor rule hold by rank-one purity
(`corollary-determinant-weights--1`).

## Main statements

- `AlgebraicGeometry.WeilGroup.detWeight_subquotient_exteriorPower`: the determinant weights of
  the constituents of `⋀^r ρ` (blueprint `proposition-determinant-weights-tensor-operations--2`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]

namespace WeilGroup

variable {W : WeilGroup p} {l : ℕ} [Fact l.Prime] {V : Type u} [AddCommGroup V]
  [Module (PadicAlgCl l) V] [FiniteDimensional (PadicAlgCl l) V]
  {ρ : Representation (PadicAlgCl l) W.carrier V} (ι : PadicAlgCl l →+* ℂ)

section Exterior

/-- A subrepresentation of a lisse Weil sheaf is lisse. -/
theorem IsLisse.subrepresentation (hρ : W.IsLisse l ρ) (A : Subrepresentation ρ) :
    W.IsLisse l A.toRepresentation :=
  IsLisse.of_continuous_apply fun φ v ↦ by
    obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend φ (p := A.toSubmodule)
    refine (hρ.continuous_apply ψ v).congr fun g ↦ ?_
    rw [← hψ]
    rfl

/-- A quotient of a lisse Weil sheaf is lisse. -/
theorem IsLisse.quotient (hρ : W.IsLisse l ρ) (A : Subrepresentation ρ) :
    W.IsLisse l A.quotient :=
  IsLisse.of_continuous_apply fun φ v ↦ by
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective _ v
    exact hρ.continuous_apply (φ ∘ₗ A.toSubmodule.mkQ) v

variable [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p] [Fact (ringChar K ≠ l)]
  [W.IsEtaleQuotient]

omit [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p] [Fact (ringChar K ≠ l)]
  [W.IsEtaleQuotient] in
/-- The rank-counted list of determinant weights of an irreducible `ρ` is `dw_ι(ρ)` repeated
`rank ρ` times. -/
theorem rankDetWeightMultiset_of_isIrreducible (hirr : ρ.IsIrreducible) :
    W.rankDetWeightMultiset l ρ ι =
      Multiset.replicate (Module.finrank (PadicAlgCl l) V) (W.detWeight l ρ ι) := by
  rw [rankDetWeightMultiset_eq_sum ι (Vs := fun _ : Unit ↦ ⊤)
    Subrepresentation.isInternal_const_top
    fun _ ↦ Subrepresentation.topEquiv.isIrreducible_iff.2 hirr, Fintype.sum_unique,
    ← detWeight_of_equiv ι Subrepresentation.topEquiv, ← Subrepresentation.topEquiv.finrank_eq]

/-- The constituents of an exterior power `⋀^r ρ` of an irreducible lisse Weil sheaf `ρ`: their
determinant weights are sums of `r` entries of the rank-counted list of `ρ`, which consists of
`dw_ι(ρ)` repeated `rank ρ` times. This is the semisimple case
`Representation.exists_multiset_le_and_detWeight_eq_sum_of_exteriorPower` for one summand. -/
theorem exists_le_rankDetWeightMultiset_of_isIrreducible (hρ : W.IsLisse l ρ)
    (hirr : ρ.IsIrreducible) (r : ℕ) {U S : Subrepresentation (ρ.exteriorPower r)}
    (hQ : (S.subquotient U).IsIrreducible) :
    ∃ T : Multiset ℝ, T ≤ W.rankDetWeightMultiset l ρ ι ∧ Multiset.card T = r ∧
      W.detWeight l (S.subquotient U) ι = T.sum := by
  have := hirr.nontrivial
  let Vs : Unit → Subrepresentation ρ := fun _ ↦ ⊤
  have hVs (a : Unit) : (Vs a).toRepresentation.IsIrreducible :=
    Subrepresentation.topEquiv.isIrreducible_iff.2 hirr
  let e₀ := Subrepresentation.subquotientInfEquiv U S
  obtain ⟨T, hT, hcard, hsum⟩ :=
    Representation.exists_multiset_le_and_detWeight_eq_sum_of_exteriorPower
      (weightCharacter ι (Nat.card K)) W.deg W.frobeniusLift ρ r Vs hVs
      (fun a ↦ (hasFiniteGeometricDet_and_detWeight_eq ι (hρ.subrepresentation (Vs a))).1)
      Subrepresentation.isInternal_const_top (Subrepresentation.inf_lt_of_isIrreducible hQ)
      (e₀.isIrreducible_iff.2 hQ)
      (hasFiniteGeometricDet_and_detWeight_eq ι ((hρ.exteriorPower r).subquotient S _)).1
  refine ⟨T, ?_, hcard, ?_⟩
  · rw [rankDetWeightMultiset_eq_sum ι Subrepresentation.isInternal_const_top hVs]
    convert hT using 1
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [detWeight_weightCharacter]
    rfl
  · rw [detWeight_of_equiv ι e₀, ← hsum, detWeight_weightCharacter]
    rfl

/-- The constituents of the steps `⋀^j A ⊗ ⋀^{r - j} (ρ / A)` of the filtration of `⋀^r ρ` along
a subrepresentation `A` of a lisse `ρ` have finite geometric determinant: these steps are
subquotients of the lisse `⋀^r ρ`. -/
theorem hasFiniteGeometricDet_subquotient_tprod (hρ : W.IsLisse l ρ) (A : Subrepresentation ρ)
    {r j : ℕ} (hjr : j ≤ r)
    (U S : Subrepresentation ((A.toRepresentation.exteriorPower j).tprod
      (A.quotient.exteriorPower (r - j)))) :
    (S.subquotient U).HasFiniteGeometricDet W.deg := by
  let e := A.exteriorPowerGradedEquiv r (Nat.add_sub_cancel' hjr)
  exact W.finite_range_of_continuous _ (IsLisse.continuous_det_apply
    ((IsLisse.of_equiv e.symm ((hρ.exteriorPower r).subquotient _ _)).subquotient S U))

/-- The forward induction step for
`AlgebraicGeometry.WeilGroup.detWeight_subquotient_exteriorPower`:
if the constituents of all exterior powers of a subrepresentation `A` and of the quotient `ρ / A`
have determinant weights which are sums of entries of their rank-counted lists, then so do those
of `⋀^r ρ`. A constituent of `⋀^r ρ` is a constituent of a step `⋀^j A ⊗ ⋀^{r - j} (ρ / A)` of
the filtration along `A`, so its weight is a sum `dw_ι(Q₁) + dw_ι(Q₂)` of weights of constituents
of `⋀^j A` and `⋀^{r - j} (ρ / A)` by the two-factor tensor rule. -/
theorem exists_le_rankDetWeightMultiset_of_subrepresentation (hρ : W.IsLisse l ρ)
    (A : Subrepresentation ρ)
    (hA : ∀ (j : ℕ) (U S : Subrepresentation (A.toRepresentation.exteriorPower j)),
      (S.subquotient U).IsIrreducible →
      ∃ T : Multiset ℝ, T ≤ W.rankDetWeightMultiset l A.toRepresentation ι ∧
        Multiset.card T = j ∧ W.detWeight l (S.subquotient U) ι = T.sum)
    (hQ : ∀ (j : ℕ) (U S : Subrepresentation (A.quotient.exteriorPower j)),
      (S.subquotient U).IsIrreducible →
      ∃ T : Multiset ℝ, T ≤ W.rankDetWeightMultiset l A.quotient ι ∧
        Multiset.card T = j ∧ W.detWeight l (S.subquotient U) ι = T.sum)
    {r : ℕ} {U S : Subrepresentation (ρ.exteriorPower r)} (hirr : (S.subquotient U).IsIrreducible) :
    ∃ T : Multiset ℝ, T ≤ W.rankDetWeightMultiset l ρ ι ∧ Multiset.card T = r ∧
      W.detWeight l (S.subquotient U) ι = T.sum := by
  obtain ⟨j, hj, U', S', ⟨e₁⟩⟩ :=
    Subrepresentation.exists_subquotient_equiv_of_antitone_chain
      (A.exteriorPowerFiltration_eq_bot r (Nat.lt_succ_self r))
      (fun j _ ↦ A.exteriorPowerFiltration_succ_le r j)
      ((A.exteriorPowerFiltration_zero r).symm ▸ le_top) hirr
  have hjr : j ≤ r := Nat.lt_succ_iff.1 hj
  obtain ⟨U'', S'', -, ⟨e₂⟩⟩ :=
    Representation.ConstituentsLE.of_equiv (A.exteriorPowerGradedEquiv r
      (Nat.add_sub_cancel' hjr)).symm U' S' (e₁.isIrreducible_iff.2 hirr)
  have f := e₂.symm.trans e₁
  obtain ⟨UV, SV, UE, SE, -, -, hV, hE, -, -, heq⟩ :=
    Representation.exists_detWeight_eq_add_of_subquotient_tprod
      (weightCharacter ι (Nat.card K)) W.deg W.frobeniusLift _ _
      (fun UV SV _ ↦ (hasFiniteGeometricDet_and_detWeight_eq ι
        (((hρ.subrepresentation A).exteriorPower j).subquotient SV UV)).1)
      (fun UE SE _ ↦ (hasFiniteGeometricDet_and_detWeight_eq ι
        (((hρ.quotient A).exteriorPower (r - j)).subquotient SE UE)).1)
      (f.isIrreducible_iff.2 hirr) (hasFiniteGeometricDet_subquotient_tprod hρ A hjr U'' S'')
  obtain ⟨T₁, hT₁, hc₁, hs₁⟩ := hA j UV SV hV
  obtain ⟨T₂, hT₂, hc₂, hs₂⟩ := hQ (r - j) UE SE hE
  refine ⟨T₁ + T₂, ?_, ?_, ?_⟩
  · rw [rankDetWeightMultiset_eq_add ι A]
    exact add_le_add hT₁ hT₂
  · rw [Multiset.card_add, hc₁, hc₂]; omega
  rw [Multiset.sum_add, ← hs₁, ← hs₂, detWeight_of_equiv ι f]
  exact (detWeight_eq_detWeight_weightCharacter ι _).trans (heq.trans (congrArg₂ (· + ·)
    (detWeight_eq_detWeight_weightCharacter ι _).symm
    (detWeight_eq_detWeight_weightCharacter ι _).symm))

/-- The converse induction step for
`AlgebraicGeometry.WeilGroup.detWeight_subquotient_exteriorPower`: if every sum of `j` entries of
the rank-counted list of a subrepresentation `A`, resp. of the quotient `ρ / A`, is the weight of
a constituent of `⋀^j A`, resp. `⋀^j (ρ / A)`, then every sum of `r` entries of the list of `ρ` is
the weight of a constituent of `⋀^r ρ`. Split the entries between `A` and `ρ / A`, and take a
constituent of `⋀^j A ⊗ ⋀^{r - j} (ρ / A)` given by the converse of the two-factor tensor rule. -/
theorem exists_detWeight_eq_sum_of_subrepresentation (hρ : W.IsLisse l ρ)
    (A : Subrepresentation ρ)
    (hA : ∀ (j : ℕ) (T : Multiset ℝ), T ≤ W.rankDetWeightMultiset l A.toRepresentation ι →
      Multiset.card T = j → ∃ U S : Subrepresentation (A.toRepresentation.exteriorPower j),
        (S.subquotient U).IsIrreducible ∧ W.detWeight l (S.subquotient U) ι = T.sum)
    (hQ : ∀ (j : ℕ) (T : Multiset ℝ), T ≤ W.rankDetWeightMultiset l A.quotient ι →
      Multiset.card T = j → ∃ U S : Subrepresentation (A.quotient.exteriorPower j),
        (S.subquotient U).IsIrreducible ∧ W.detWeight l (S.subquotient U) ι = T.sum)
    {r : ℕ} {T : Multiset ℝ} (hT : T ≤ W.rankDetWeightMultiset l ρ ι)
    (hcard : Multiset.card T = r) :
    ∃ U S : Subrepresentation (ρ.exteriorPower r), (S.subquotient U).IsIrreducible ∧
      W.detWeight l (S.subquotient U) ι = T.sum := by
  rw [rankDetWeightMultiset_eq_add ι A] at hT
  set L₁ := W.rankDetWeightMultiset l A.toRepresentation ι
  have hT₁T : T ∩ L₁ ≤ T := Multiset.inter_le_left
  have hT₂ : T - T ∩ L₁ ≤ W.rankDetWeightMultiset l A.quotient ι :=
    Multiset.sub_inter_le_of_le_add hT
  have hjr : Multiset.card (T ∩ L₁) ≤ r := hcard ▸ Multiset.card_le_card hT₁T
  have hc₂ : Multiset.card (T - T ∩ L₁) = r - Multiset.card (T ∩ L₁) := by
    rw [Multiset.card_sub hT₁T, hcard]
  obtain ⟨UV, SV, hV, hs₁⟩ := hA _ (T ∩ L₁) Multiset.inter_le_right rfl
  obtain ⟨UE, SE, hE, hs₂⟩ := hQ _ (T - T ∩ L₁) hT₂ hc₂
  obtain ⟨U'', S'', -, hQ'', heq⟩ :=
    Representation.exists_isIrreducible_subquotient_tprod_detWeight_eq_add
      (weightCharacter ι (Nat.card K)) W.deg W.frobeniusLift hV hE
      (hasFiniteGeometricDet_and_detWeight_eq ι
        (((hρ.subrepresentation A).exteriorPower _).subquotient SV UV)).1
      (hasFiniteGeometricDet_and_detWeight_eq ι
        (((hρ.quotient A).exteriorPower _).subquotient SE UE)).1
      fun U S _ ↦ hasFiniteGeometricDet_subquotient_tprod hρ A hjr U S
  obtain ⟨U, S, hirr, ⟨f⟩⟩ := Representation.ConstituentsLE.tprod_exteriorPower A
    (Nat.add_sub_cancel' hjr) U'' S'' hQ''
  refine ⟨U, S, hirr, ?_⟩
  have h := (detWeight_eq_detWeight_weightCharacter ι _).trans (heq.trans (congrArg₂ (· + ·)
    (detWeight_eq_detWeight_weightCharacter ι _).symm
    (detWeight_eq_detWeight_weightCharacter ι _).symm))
  exact (detWeight_of_equiv ι f.symm).symm.trans (h.trans ((congrArg₂ (· + ·) hs₁ hs₂).trans
    ((Multiset.sum_add _ _).symm.trans (congrArg Multiset.sum (add_tsub_cancel_of_le hT₁T)))))

/-- The constituents of an exterior power of a nonzero lisse Weil sheaf, by induction on the rank:
see `AlgebraicGeometry.WeilGroup.detWeight_subquotient_exteriorPower`. -/
theorem detWeight_subquotient_exteriorPower_aux (n : ℕ) {V : Type u} [AddCommGroup V]
    [Module (PadicAlgCl l) V] [FiniteDimensional (PadicAlgCl l) V] [Nontrivial V]
    {ρ : Representation (PadicAlgCl l) W.carrier V} (hρ : W.IsLisse l ρ)
    (hn : Module.finrank (PadicAlgCl l) V = n) (r : ℕ) :
    (∀ U S : Subrepresentation (ρ.exteriorPower r), (S.subquotient U).IsIrreducible →
      ∃ T : Multiset ℝ, T ≤ W.rankDetWeightMultiset l ρ ι ∧ Multiset.card T = r ∧
        W.detWeight l (S.subquotient U) ι = T.sum) ∧
    ∀ T : Multiset ℝ, T ≤ W.rankDetWeightMultiset l ρ ι → Multiset.card T = r →
      ∃ U S : Subrepresentation (ρ.exteriorPower r), (S.subquotient U).IsIrreducible ∧
        W.detWeight l (S.subquotient U) ι = T.sum := by
  induction n using Nat.strong_induction_on generalizing V r with
  | _ n ih =>
  by_cases hirr : ρ.IsIrreducible
  · -- the irreducible case: all constituents have weight `r dw_ι(ρ)`
    have hfwd := fun U S hQ ↦ exists_le_rankDetWeightMultiset_of_isIrreducible ι hρ hirr r
      (U := U) (S := S) hQ
    refine ⟨hfwd, fun T hT hcard ↦ ?_⟩
    have hrep {T' : Multiset ℝ} (hT' : T' ≤ W.rankDetWeightMultiset l ρ ι) :
        T' = Multiset.replicate (Multiset.card T') (W.detWeight l ρ ι) :=
      Multiset.eq_replicate_of_mem fun x hx ↦ by
        rw [rankDetWeightMultiset_of_isIrreducible ι hirr] at hT'
        exact Multiset.eq_of_mem_replicate (Multiset.subset_of_le hT' hx)
    have hr : r ≤ Module.finrank (PadicAlgCl l) V := by
      rw [← hcard, ← card_rankDetWeightMultiset (ρ := ρ) ι]
      exact Multiset.card_le_card hT
    have : Nontrivial (⋀[PadicAlgCl l]^r V) := by
      refine (Module.finrank_pos_iff (R := PadicAlgCl l)).1 ?_
      rw [exteriorPower.finrank_eq]
      exact Nat.choose_pos hr
    have : Nontrivial (Subrepresentation (ρ.exteriorPower r)) :=
      ⟨⊥, ⊤, fun e ↦ bot_ne_top (congrArg Subrepresentation.toSubmodule e)⟩
    obtain ⟨B, -, hB⟩ := Subrepresentation.exists_lt_isIrreducible_subquotient
      (ρ := ρ.exteriorPower r) (A := ⊤) top_ne_bot
    obtain ⟨T', hT', hcard', hsum'⟩ := hfwd B ⊤ hB
    refine ⟨B, ⊤, hB, ?_⟩
    rw [hsum', hrep hT', hrep hT, hcard, hcard']
  -- otherwise `ρ` has a proper nonzero subrepresentation `A`
  obtain ⟨A, hA0, hAtop⟩ : ∃ A : Subrepresentation ρ, A ≠ ⊥ ∧ A ≠ ⊤ := by
    by_contra! h
    have : Nontrivial (Subrepresentation ρ) :=
      ⟨⊥, ⊤, fun e ↦ bot_ne_top (congrArg Subrepresentation.toSubmodule e)⟩
    exact hirr ⟨fun A ↦ (eq_or_ne A ⊥).imp_right (h A)⟩
  have hA0' : A.toSubmodule ≠ ⊥ := fun h ↦
    hA0 (Subrepresentation.toSubmodule_injective (h.trans Subrepresentation.toSubmodule_bot.symm))
  have hAtop' : A.toSubmodule ≠ ⊤ := fun h ↦
    hAtop (Subrepresentation.toSubmodule_injective (h.trans Subrepresentation.toSubmodule_top.symm))
  have : Nontrivial A.toSubmodule := Submodule.nontrivial_iff_ne_bot.2 hA0'
  have : Nontrivial (V ⧸ A.toSubmodule) := Submodule.Quotient.nontrivial_iff.2 hAtop'
  have hdimA : Module.finrank (PadicAlgCl l) A.toSubmodule < n :=
    hn ▸ Submodule.finrank_lt hAtop'
  have hdimQ : Module.finrank (PadicAlgCl l) (V ⧸ A.toSubmodule) < n := by
    have h := Submodule.finrank_quotient_add_finrank A.toSubmodule
    have h' := Module.finrank_pos (R := PadicAlgCl l) (M := A.toSubmodule)
    omega
  have ihA := ih _ hdimA (hρ.subrepresentation A) rfl
  have ihQ := ih _ hdimQ (hρ.quotient A) rfl
  exact ⟨fun U S hQ ↦ exists_le_rankDetWeightMultiset_of_subrepresentation ι hρ A
      (fun j ↦ (ihA j).1) (fun j ↦ (ihQ j).1) hQ,
    fun T hT hcard ↦ exists_detWeight_eq_sum_of_subrepresentation ι hρ A
      (fun j ↦ (ihA j).2) (fun j ↦ (ihQ j).2) hT hcard⟩

/-- Blueprint `proposition-determinant-weights-tensor-operations--2`: Determinant weights of an
exterior power.

Let `ρ` be a nonzero lisse Weil sheaf, with composition factors `A_a` of rank `d_a` and
determinant weights `γ_a`, and let `L` be its rank-counted list of determinant weights
(`AlgebraicGeometry.WeilGroup.rankDetWeightMultiset`), in which `γ_a` occurs `d_a` times, so that
every value `γ` occurs `r(γ) = ∑_{γ_a = γ} d_a` times. A sub-multiset `T ≤ L` with `r` elements is
the same as a tuple `(n_γ)` with `0 ≤ n_γ ≤ r(γ)` and `∑ n_γ = r` (take `n_γ` the multiplicity
of `γ` in `T`), with `∑ T = ∑ n_γ γ`. In these terms:

* every constituent `S / U` of the exterior power `⋀^r ρ` has determinant weight `∑ T` for a
  sub-multiset `T ≤ L` with `r` elements;
* conversely, for every sub-multiset `T ≤ L` with `r` elements, some constituent of `⋀^r ρ` has
  determinant weight `∑ T`.

The finite geometric determinant hypotheses of
`proposition-determinant-weights-tensor-operations--2` hold by rank-one purity
(`corollary-determinant-weights--1`); the geometric semisimplicity assumed in the blueprint is not
needed. -/
theorem detWeight_subquotient_exteriorPower [Nontrivial V] (hρ : W.IsLisse l ρ) (r : ℕ) :
    (∀ U S : Subrepresentation (ρ.exteriorPower r), (S.subquotient U).IsIrreducible →
      ∃ T : Multiset ℝ, T ≤ W.rankDetWeightMultiset l ρ ι ∧ Multiset.card T = r ∧
        W.detWeight l (S.subquotient U) ι = T.sum) ∧
    ∀ T : Multiset ℝ, T ≤ W.rankDetWeightMultiset l ρ ι → Multiset.card T = r →
      ∃ U S : Subrepresentation (ρ.exteriorPower r), (S.subquotient U).IsIrreducible ∧
        W.detWeight l (S.subquotient U) ι = T.sum :=
  detWeight_subquotient_exteriorPower_aux ι _ hρ rfl r

end Exterior

end WeilGroup

end AlgebraicGeometry
