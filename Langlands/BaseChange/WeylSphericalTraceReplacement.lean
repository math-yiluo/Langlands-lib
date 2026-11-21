import Langlands.BaseChange.SphericalTraceReplacementReduction
import Langlands.Representation.Unramified.Eigenvalues
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finsupp.Multiset

/-! # Opposite Weyl characters in spherical trace replacement -/

noncomputable section

namespace Langlands.BaseChange

open Classical Multiplicative
open Langlands.Unramified
open scoped BigOperators

universe u v w t

variable {n : ℕ}

/-- The character of the integer weight lattice specified by its values on the coordinate basis. -/
def tupleWeightCharacter (z : Fin n → ℂˣ) : WeightCharacter n ℂ where
  toFun w := ((∏ i, z i ^ (toAdd w i) : ℂˣ) : ℂ)
  map_one' := by
    change ((∏ i, z i ^ (0 : ℤ) : ℂˣ) : ℂ) = 1
    simp
  map_mul' a b := by
    change ((∏ i, z i ^ (toAdd a i + toAdd b i) : ℂˣ) : ℂ) =
      ((∏ i, z i ^ (toAdd a i) : ℂˣ) : ℂ) * ((∏ i, z i ^ (toAdd b i) : ℂˣ) : ℂ)
    simp_rw [zpow_add]
    rw [Finset.prod_mul_distrib, Units.val_mul]

@[simp]
theorem tupleWeightCharacter_single (z : Fin n → ℂˣ) (i : Fin n) :
    tupleWeightCharacter z (ofAdd (Pi.single i 1)) = (z i : ℂ) := by
  change ((∏ j, z j ^ (Pi.single i 1 : Fin n → ℤ) j : ℂˣ) : ℂ) = _
  rw [Finset.prod_eq_single_of_mem i (Finset.mem_univ i)]
  · simp
  · intro j _ hij
    simp [Pi.single_eq_of_ne hij]

theorem tupleWeightCharacter_injective :
    Function.Injective (tupleWeightCharacter (n := n)) := by
  intro z z' h
  funext i
  apply Units.ext
  simpa using DFunLike.congr_fun h (ofAdd (Pi.single i 1))

/-- A coordinatewise power of the inducing values multiplies the weight by the degree. -/
theorem tupleWeightCharacter_pow_apply (l : ℕ) (z : Fin n → ℂˣ) (a : Fin n → ℤ) :
    tupleWeightCharacter (z ^ l) (ofAdd a) = tupleWeightCharacter z (ofAdd (l • a)) := by
  change ((∏ i, (z i ^ l) ^ (a i) : ℂˣ) : ℂ) = ((∏ i, z i ^ ((l • a) i) : ℂˣ) : ℂ)
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [← zpow_natCast, ← zpow_mul]
  simp only [Pi.smul_apply, nsmul_eq_mul]

private theorem ofTuple_eq_iff_reindex {z z' : Fin n → ℂˣ} :
    Eigenvalues.ofTuple z = Eigenvalues.ofTuple z' ↔ ∃ w : Equiv.Perm (Fin n), z' = z ∘ w := by
  constructor
  · intro h
    have hmap : Finset.univ.val.map z = Finset.univ.val.map z' := by
      rw [Fin.univ_val_map, Fin.univ_val_map]
      exact congrArg Subtype.val h
    have hcard (a : ℂˣ) :
        Fintype.card {i // z' i = a} = Fintype.card {i // z i = a} := by
      have hc := congrArg (Multiset.count a) hmap.symm
      rw [Multiset.count_map, Multiset.count_map] at hc
      rw [Fintype.card_subtype, Fintype.card_subtype]
      change (Multiset.filter (fun i ↦ z' i = a) Finset.univ.val).card =
        (Multiset.filter (fun i ↦ z i = a) Finset.univ.val).card
      simpa only [eq_comm (a := a)] using hc
    let fibre (a : ℂˣ) : {i // z' i = a} ≃ {i // z i = a} := Fintype.equivOfCardEq (hcard a)
    let w := (Equiv.sigmaFiberEquiv z').symm.trans
      ((Equiv.sigmaCongrRight fibre).trans (Equiv.sigmaFiberEquiv z))
    exact ⟨w, funext fun i ↦ (fibre (z' i) ⟨i, rfl⟩).2.symm⟩
  · rintro ⟨w, rfl⟩
    exact (Eigenvalues.ofTuple_reindex z w).symm

/-- The full Weyl multiset, indexed by all permutations so that repetitions retain their
multiplicities. -/
def weylTupleMultiset (z : Fin n → ℂˣ) : Multiset (Fin n → ℂˣ) :=
  Finset.univ.val.map fun w : Equiv.Perm (Fin n) ↦ z ∘ w

private theorem ofTuple_eq_of_mem_weylTupleMultiset {z a : Fin n → ℂˣ}
    (ha : a ∈ weylTupleMultiset z) : Eigenvalues.ofTuple a = Eigenvalues.ofTuple z := by
  obtain ⟨w, _, rfl⟩ := Multiset.mem_map.mp ha
  exact Eigenvalues.ofTuple_reindex z w

private theorem weylTupleMultiset_eq_of_ofTuple_eq {z a : Fin n → ℂˣ}
    (h : Eigenvalues.ofTuple z = Eigenvalues.ofTuple a) :
    weylTupleMultiset z = weylTupleMultiset a := by
  obtain ⟨w, rfl⟩ := ofTuple_eq_iff_reindex.mp h
  unfold weylTupleMultiset
  calc
    _ = ((Finset.univ.val : Multiset (Equiv.Perm (Fin n))).map (Equiv.mulLeft w)).map
      (fun g : Equiv.Perm (Fin n) ↦ z ∘ g) := by rw [Multiset.map_univ_val_equiv]
    _ = _ := by rw [Multiset.map_map]; rfl

private theorem map_pow_weylTupleMultiset (z : Fin n → ℂˣ) (l : ℕ) :
    (weylTupleMultiset z).map (· ^ l) = weylTupleMultiset (z ^ l) := by
  rw [weylTupleMultiset, weylTupleMultiset, Multiset.map_map]
  rfl

/-- The opposite ordering on uniformizer values uses weakly decreasing absolute values. -/
def IsOppositeWeightOrder (z : Fin n → ℂˣ) : Prop :=
  Antitone (fun i ↦ ‖(z i : ℂ)‖)

private theorem isOppositeWeightOrder_of_pow {z : Fin n → ℂˣ} {l : ℕ} (hl : l ≠ 0)
    (h : IsOppositeWeightOrder (z ^ l)) : IsOppositeWeightOrder z := by
  intro i j hij
  apply (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) hl).mp
  simpa only [Pi.pow_apply, Units.val_pow_eq_pow_val, Complex.norm_pow] using h hij

private theorem exists_oppositeTuple (s : Eigenvalues n) :
    ∃ z : Fin n → ℂˣ, Eigenvalues.ofTuple z = s ∧ IsOppositeWeightOrder z := by
  obtain ⟨z, rfl⟩ := Eigenvalues.ofTuple_surjective n s
  let a := fun i ↦ OrderDual.toDual ‖(z i : ℂ)‖
  exact ⟨z ∘ Tuple.sort a, Eigenvalues.ofTuple_reindex z _, Tuple.monotone_sort a⟩

private def oppositeTuple (s : Eigenvalues n) : Fin n → ℂˣ :=
  (exists_oppositeTuple s).choose

private theorem ofTuple_oppositeTuple (s : Eigenvalues n) :
    Eigenvalues.ofTuple (oppositeTuple s) = s :=
  (exists_oppositeTuple s).choose_spec.1

private theorem oppositeTuple_isOpposite (s : Eigenvalues n) :
    IsOppositeWeightOrder (oppositeTuple s) :=
  (exists_oppositeTuple s).choose_spec.2

/-- Convert an exponent multiset to weight characters and count after taking the indicated
coordinatewise power. Degree one gives the unpulled character multiset. -/
def jacquetWeightMultiplicities (l : ℕ) (m : Multiset (Fin n → ℂˣ)) :
    JacquetWeightMultiplicities n :=
  (m.map (fun z ↦ tupleWeightCharacter (z ^ l))).toFinsupp

/-- The character sum with multiplicities after pullback equals the original sum at the
degree-scaled weight. -/
theorem strictWeightCharacterEvaluation_jacquetWeightMultiplicities (l : ℕ)
    (m : Multiset (Fin n → ℂˣ)) (a : StrictWeight n) :
    strictWeightCharacterEvaluation n (jacquetWeightMultiplicities l m).coefficients a =
      (m.map (fun z ↦ tupleWeightCharacter z (ofAdd (l • a.1)))).sum := by
  induction m using Multiset.induction_on with
  | empty =>
      simp [jacquetWeightMultiplicities, JacquetWeightMultiplicities.coefficients]
  | cons z m ih =>
      have hcoeff : (jacquetWeightMultiplicities l (z ::ₘ m)).coefficients =
          Finsupp.single (tupleWeightCharacter (z ^ l)) 1 +
            (jacquetWeightMultiplicities l m).coefficients := by
        rw [jacquetWeightMultiplicities, Multiset.map_cons, ← Multiset.singleton_add,
          Multiset.toFinsupp_add, Multiset.toFinsupp_singleton]
        let castCoefficients := Finsupp.mapRange.addMonoidHom
          (ι := WeightCharacter n ℂ) (Nat.castAddMonoidHom ℂ)
        change castCoefficients (_ + _) = _ + castCoefficients _
        rw [map_add]
        simp [castCoefficients, Finsupp.mapRange_single, jacquetWeightMultiplicities]
      rw [hcoeff, map_add, Pi.add_apply, ih]
      simp [strictWeightCharacterEvaluation, tupleWeightCharacter_pow_apply]

private theorem jacquetWeightMultiplicities_weyl_pow (l : ℕ) (z : Fin n → ℂˣ) :
    jacquetWeightMultiplicities l (weylTupleMultiset z) =
      jacquetWeightMultiplicities 1 (weylTupleMultiset (z ^ l)) := by
  rw [← map_pow_weylTupleMultiset z l]
  simp only [jacquetWeightMultiplicities, pow_one, Multiset.map_map]
  rfl

/-- A chosen opposite Weyl character of the given unordered uniformizer values. -/
def oppositeWeightCharacter (s : Eigenvalues n) : WeightCharacter n ℂ :=
  tupleWeightCharacter (oppositeTuple s)

/-- The multiplicity of the chosen character in the full Weyl multiset. -/
def oppositeWeightMultiplicity (s : Eigenvalues n) : ℕ :=
  jacquetWeightMultiplicities 1 (weylTupleMultiset (oppositeTuple s)) (oppositeWeightCharacter s)

theorem oppositeWeightMultiplicity_ne_zero (s : Eigenvalues n) :
    oppositeWeightMultiplicity s ≠ 0 := by
  apply Multiset.count_ne_zero.mpr
  apply Multiset.mem_map.mpr
  refine ⟨oppositeTuple s, Multiset.mem_map.mpr ⟨1, Finset.mem_univ _, rfl⟩, ?_⟩
  simp [oppositeWeightCharacter]

variable {I S : Type*}

/-- The Jacquet multiset is supported on the Weyl orbit of the inducing data. Spherical
contributors have the full Weyl multiset, and each other contributor omits the opposite order. -/
def HasWeylJacquetSupport (inducing : I → Fin n → ℂˣ) (spherical : I → Prop)
    (exponents : I → Multiset (Fin n → ℂˣ)) : Prop :=
  ∀ i, exponents i ≤ weylTupleMultiset (inducing i) ∧
    (spherical i → exponents i = weylTupleMultiset (inducing i)) ∧
    (¬ spherical i → ∀ z ∈ exponents i, ¬ IsOppositeWeightOrder z)

/-- The elementary trace formula in terms of the original Jacquet multiset evaluated at the
degree-scaled diagonal weight. -/
def HasJacquetElementaryTraceExpansion (l : ℕ) (exponents : I → Multiset (Fin n → ℂˣ))
    (factor : StrictWeight n → ℂ) (trace : I → StrictWeight n → ℂ) : Prop :=
  ∀ i a, trace i a = factor a *
    ((exponents i).map (fun z ↦ tupleWeightCharacter z (ofAdd (l • a.1)))).sum

theorem HasJacquetElementaryTraceExpansion.toHasElementaryTraceExpansion
    {l : ℕ} {exponents : I → Multiset (Fin n → ℂˣ)} {factor : StrictWeight n → ℂ}
    {trace : I → StrictWeight n → ℂ}
    (h : HasJacquetElementaryTraceExpansion l exponents factor trace) :
    HasElementaryTraceExpansion (fun i ↦ jacquetWeightMultiplicities l (exponents i))
      factor trace := by
  intro i a
  rw [strictWeightCharacterEvaluation_jacquetWeightMultiplicities]
  exact h i a

/-- The opposite coefficient detects spherical contributors, including after the norm power
identifies different inducing characters. -/
theorem detectsSphericalContributors_of_weylJacquetSupport
    (l : ℕ) (hl : l ≠ 0) (inducing : I → Fin n → ℂˣ) (spherical : I → Prop)
    (exponents : I → Multiset (Fin n → ℂˣ))
    (hsupport : HasWeylJacquetSupport inducing spherical exponents)
    (label : I → S) (spectrum : S → Eigenvalues n) (hinj : Function.Injective spectrum)
    (hlabel : ∀ i, Eigenvalues.power (Eigenvalues.ofTuple (inducing i)) l = spectrum (label i)) :
    DetectsSphericalContributors (fun i ↦ jacquetWeightMultiplicities l (exponents i))
      label spherical (oppositeWeightCharacter ∘ spectrum) (oppositeWeightMultiplicity ∘ spectrum) := by
  intro i s
  change jacquetWeightMultiplicities l (exponents i) (oppositeWeightCharacter (spectrum s)) =
    if spherical i ∧ label i = s then oppositeWeightMultiplicity (spectrum s) else 0
  have hi := hsupport i
  by_cases h : spherical i ∧ label i = s
  · rw [ite_eq_left h, hi.2.1 h.1]
    have he : Eigenvalues.ofTuple (inducing i ^ l) =
        Eigenvalues.ofTuple (oppositeTuple (spectrum s)) := by
      rw [ofTuple_oppositeTuple, ← h.2, ← hlabel i, Eigenvalues.power_ofTuple]
      rfl
    rw [jacquetWeightMultiplicities_weyl_pow, weylTupleMultiset_eq_of_ofTuple_eq he]
    rfl
  · rw [ite_eq_right h]
    apply Multiset.count_eq_zero.mpr
    intro hm
    obtain ⟨z, hz, hchar⟩ := Multiset.mem_map.mp hm
    have hpow : z ^ l = oppositeTuple (spectrum s) :=
      tupleWeightCharacter_injective hchar
    have hs : label i = s := by
      apply hinj
      rw [← hlabel i, ← ofTuple_eq_of_mem_weylTupleMultiset (Multiset.mem_of_le hi.1 hz),
        Eigenvalues.power_ofTuple]
      change Eigenvalues.ofTuple (z ^ l) = spectrum s
      rw [hpow, ofTuple_oppositeTuple]
    exact hi.2.2 (fun hsi ↦ h ⟨hsi, hs⟩) z hz
      (isOppositeWeightOrder_of_pow hl (by rw [hpow]; exact oppositeTuple_isOpposite _))

/-- Spherical trace replacement from the Weyl multiset and opposite-order exclusion
properties of the Jacquet expansions. -/
def WeylSphericalTraceReplacementStatement : Prop :=
  ∀ (n l : ℕ), l ≠ 0 →
    ∀ (I : Type u) (J : Type v) (S : Type w) (Test : Type t)
      [Fintype I] [Fintype J] [Fintype S]
      (inducingE : I → Fin n → ℂˣ) (inducingF : J → Fin n → ℂˣ)
      (exponentsE : I → Multiset (Fin n → ℂˣ)) (exponentsF : J → Multiset (Fin n → ℂˣ))
      (labelE : I → S) (labelF : J → S) (spectrum : S → Eigenvalues n)
      (sphericalE : I → Prop) (sphericalF : J → Prop)
      (factor : StrictWeight n → ℂ) (value : S → Test → ℂ)
      (elementaryE : I → StrictWeight n → ℂ) (elementaryF : J → StrictWeight n → ℂ)
      (traceE : I → Test → ℂ) (traceF : J → Test → ℂ) (a : I → ℂ) (b : J → ℂ),
      Function.Injective spectrum →
      (∀ i, Eigenvalues.ofTuple (inducingE i) = spectrum (labelE i)) →
      (∀ j, Eigenvalues.power (Eigenvalues.ofTuple (inducingF j)) l = spectrum (labelF j)) →
      (∀ w, factor w ≠ 0) →
      HasWeylJacquetSupport inducingE sphericalE exponentsE →
      HasWeylJacquetSupport inducingF sphericalF exponentsF →
      HasJacquetElementaryTraceExpansion 1 exponentsE factor elementaryE →
      HasJacquetElementaryTraceExpansion l exponentsF factor elementaryF →
      HasSphericalTraceValues labelE sphericalE value traceE →
      HasSphericalTraceValues labelF sphericalF value traceF →
      (∀ w, ∑ i, a i * elementaryE i w = ∑ j, b j * elementaryF j w) →
      ∀ f, ∑ i, a i * traceE i f = ∑ j, b j * traceF j f

theorem weylSphericalTraceReplacement : WeylSphericalTraceReplacementStatement := by
  intro n l hl I J S Test _ _ _ inducingE inducingF exponentsE exponentsF labelE labelF spectrum
    sphericalE sphericalF factor value elementaryE elementaryF traceE traceF a b
    hinj hlabelE hlabelF hfactor hsupportE hsupportF hexpE hexpF htraceE htraceF heq
  have hdetectE :=
    detectsSphericalContributors_of_weylJacquetSupport 1 one_ne_zero inducingE sphericalE
      exponentsE hsupportE labelE spectrum hinj (fun i ↦ by simpa using hlabelE i)
  have hdetectF :=
    detectsSphericalContributors_of_weylJacquetSupport l hl inducingF sphericalF
      exponentsF hsupportF labelF spectrum hinj hlabelF
  exact sphericalTraceReplacementReduction n I J S Test
    (fun i ↦ jacquetWeightMultiplicities 1 (exponentsE i))
    (fun j ↦ jacquetWeightMultiplicities l (exponentsF j))
    labelE labelF sphericalE sphericalF (oppositeWeightCharacter ∘ spectrum)
    (oppositeWeightMultiplicity ∘ spectrum) factor value elementaryE elementaryF traceE traceF a b
    hfactor (fun s ↦ oppositeWeightMultiplicity_ne_zero (spectrum s))
    hexpE.toHasElementaryTraceExpansion hexpF.toHasElementaryTraceExpansion
    hdetectE hdetectF htraceE htraceF heq

end Langlands.BaseChange
