import Langlands.CommutativeAlgebra.ValuationSubringIntersection

/-!
# Finite intersections of discrete valuation subrings

The intersection maps to each valuation subring by a localization at the corresponding
contracted maximal ideal. For a finite family of distinct discrete valuation subrings, these
contractions are the distinct maximal ideals. The prime spectrum consists of their centers
and the generic point.
-/

namespace Langlands.CommutativeAlgebra.DiscreteValuationSubringIntersection

universe u v

variable {K : Type u} [Field K] {ι : Type v} (V : ι → ValuationSubring K)

/-- The intersection of the valuation subrings in the ambient field. -/
def intersection : Subring K := ⨅ i, (V i).toSubring

@[simp]
theorem mem_intersection (x : K) : x ∈ intersection V ↔ ∀ i, x ∈ V i :=
  Subring.mem_iInf

/-- The canonical inclusion of the intersection into a member of the family. -/
abbrev inclusion (i : ι) : intersection V →+* V i :=
  ValuationSubringIntersection.toValuationSubring V (mem_intersection V) i

@[simp]
theorem subtype_comp_inclusion (i : ι) :
    (V i).subtype.comp (inclusion V i) = (intersection V).subtype :=
  RingHom.ext fun _ => rfl

theorem inclusion_injective (i : ι) : Function.Injective (inclusion V i) :=
  fun _ _ h => Subtype.ext (congrArg (fun y : V i => (y : K)) h)

instance intersectionAlgebra (i : ι) : Algebra (intersection V) (V i) :=
  (inclusion V i).toAlgebra

@[simp]
theorem algebraMap_eq_inclusion (i : ι) :
    algebraMap (intersection V) (V i) = inclusion V i := rfl

/-- The contraction of the maximal ideal of `V i` to the intersection. -/
abbrev contraction (i : ι) : Ideal (intersection V) :=
  ValuationSubringIntersection.prime V (mem_intersection V) i

/-- Each valuation subring is a localization at its contracted maximal ideal. -/
instance localization [Finite ι] (i : ι) :
    IsLocalization.AtPrime (V i) (contraction V i) :=
  ValuationSubringIntersection.isLocalization_atPrime_valuationSubring V (mem_intersection V) i

/-- The localization equivalence over the intersection. -/
noncomputable def atPrimeAlgEquiv [Finite ι] (i : ι) :
    Localization.AtPrime (contraction V i) ≃ₐ[intersection V] V i :=
  IsLocalization.algEquiv (contraction V i).primeCompl _ _

@[simp]
theorem atPrimeAlgEquiv_algebraMap [Finite ι] (i : ι) (a : intersection V) :
    atPrimeAlgEquiv V i (algebraMap (intersection V) (Localization.AtPrime (contraction V i)) a) =
      inclusion V i a :=
  (atPrimeAlgEquiv V i).commutes a

/-- The image of the closed point of `Spec (V i)` in the spectrum of the intersection. -/
def center (i : ι) : PrimeSpectrum (intersection V) :=
  PrimeSpectrum.comap (inclusion V i) (IsLocalRing.closedPoint (V i))

@[simp]
theorem center_asIdeal (i : ι) : (center V i).asIdeal = contraction V i := rfl

@[simp]
theorem comap_inclusion_bot (i : ι) :
    PrimeSpectrum.comap (inclusion V i) ⊥ = ⊥ :=
  PrimeSpectrum.ext (Ideal.comap_bot_of_injective _ (inclusion_injective V i))

/-- An inclusion between two contracted primes induces the reverse inclusion of valuation
subrings. -/
theorem valuationSubring_le_of_contraction_le [Finite ι] {i j : ι}
    (hle : contraction V i ≤ contraction V j) : V j ≤ V i := by
  intro x hx
  obtain ⟨s, hs, hxs, hunit, -⟩ := ValuationSubringIntersection.exists_mem_mul_mem V x
  let a : intersection V := ⟨s, (mem_intersection V s).2 hs⟩
  have hj : a ∉ contraction V j :=
    (ValuationSubringIntersection.not_mem_prime V (mem_intersection V) j a).2 (hunit j hx)
  have hi : (V i).valuation s = 1 :=
    (ValuationSubringIntersection.not_mem_prime V (mem_intersection V) i a).1
      (fun ha => hj (hle ha))
  have hxs' := ((V i).valuation_le_one_iff (x * s)).2 (hxs i)
  rw [map_mul, hi, mul_one] at hxs'
  exact ((V i).valuation_le_one_iff x).1 hxs'

private theorem ne_top_of_dvr (W : ValuationSubring K) [IsDiscreteValuationRing W] : W ≠ ⊤ := by
  rintro rfl
  exact IsDiscreteValuationRing.not_isField (⊤ : ValuationSubring K) (Field.toIsField _)

variable [Finite ι] [∀ i, IsDiscreteValuationRing (V i)]

/-- For a distinct DVR family, comparable contractions come from the same index. -/
theorem eq_of_contraction_le (hV : Function.Injective V) {i j : ι}
    (hle : contraction V i ≤ contraction V j) : i = j := by
  have hji := valuationSubring_le_of_contraction_le V hle
  have heq := (ValuationSubring.eq_self_or_eq_top_of_le hji).resolve_right (ne_top_of_dvr (V i))
  exact (hV heq).symm

/-- A maximal ideal containing a contraction is that contraction itself. -/
theorem contraction_isMaximal (hV : Function.Injective V) (i : ι) :
    (contraction V i).IsMaximal := by
  let : Nonempty ι := ⟨i⟩
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (contraction V i)
    (ValuationSubringIntersection.prime_isPrime V (mem_intersection V) i).ne_top
  let : M.IsMaximal := hM
  obtain ⟨j, rfl⟩ :=
    ValuationSubringIntersection.exists_eq_prime_of_isMaximal V (mem_intersection V) M
  obtain rfl := eq_of_contraction_le V hV hle
  exact hM

theorem contraction_injective (hV : Function.Injective V) : Function.Injective (contraction V) :=
  fun _ _ h => eq_of_contraction_le V hV h.le

/-- The maximal ideals are exactly the contractions from the given discrete valuation rings. -/
theorem isMaximal_iff [Nonempty ι] (hV : Function.Injective V) (M : Ideal (intersection V)) :
    M.IsMaximal ↔ ∃ i, M = contraction V i := by
  constructor
  · intro hM
    let : M.IsMaximal := hM
    exact ValuationSubringIntersection.exists_eq_prime_of_isMaximal V (mem_intersection V) M
  · rintro ⟨i, rfl⟩
    exact contraction_isMaximal V hV i

/-- The contracted maximal ideal of a DVR is nonzero. -/
theorem contraction_ne_bot (i : ι) : contraction V i ≠ ⊥ := by
  intro h
  have hmap := IsLocalization.map_under (contraction V i).primeCompl (V i)
    (IsLocalRing.maximalIdeal (V i))
  change (contraction V i).map (inclusion V i) = IsLocalRing.maximalIdeal (V i) at hmap
  rw [h, Ideal.map_bot] at hmap
  exact IsDiscreteValuationRing.not_a_field (V i) hmap.symm

/-- Every prime is the zero ideal or the contraction of a DVR maximal ideal. -/
theorem prime_eq_bot_or_eq_contraction [Nonempty ι] (q : Ideal (intersection V)) (hq : q.IsPrime) :
    q = ⊥ ∨ ∃ i, q = contraction V i := by
  obtain ⟨M, hM, hqM⟩ := Ideal.exists_le_maximal q hq.ne_top
  let : M.IsMaximal := hM
  obtain ⟨i, rfl⟩ :=
    ValuationSubringIntersection.exists_eq_prime_of_isMaximal V (mem_intersection V) M
  have hd : Disjoint ((contraction V i).primeCompl : Set (intersection V))
      (q : Set (intersection V)) :=
    Set.disjoint_left.mpr fun _ hs hsq => (Ideal.mem_primeCompl_iff.mp hs) (hqM hsq)
  let P : Ideal (V i) := q.map (algebraMap (intersection V) (V i))
  have hP : P.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (contraction V i).primeCompl (V i) q hq hd
  have hcontract : P.comap (inclusion V i) = q :=
    IsLocalization.under_map_of_isPrime_disjoint (contraction V i).primeCompl (V i) hq hd
  rcases IsLocalRing.Ring.KrullDimLE.eq_bot_or_eq_top (⟨P, hP⟩ : PrimeSpectrum (V i)) with h | h
  · have hbot : P = ⊥ := congrArg PrimeSpectrum.asIdeal h
    left
    rw [← hcontract, hbot]
    exact Ideal.comap_bot_of_injective _ (inclusion_injective V i)
  · have hmax : P = IsLocalRing.maximalIdeal (V i) := congrArg PrimeSpectrum.asIdeal h
    exact Or.inr ⟨i, hcontract.symm.trans (congrArg (Ideal.comap (inclusion V i)) hmax)⟩

/-- The generic point and the listed centers exhaust the actual prime spectrum. -/
theorem eq_bot_or_eq_center [Nonempty ι] (p : PrimeSpectrum (intersection V)) :
    p = ⊥ ∨ ∃ i, p = center V i := by
  rcases prime_eq_bot_or_eq_contraction V p.asIdeal p.isPrime with h | ⟨i, hi⟩
  · exact Or.inl (PrimeSpectrum.ext h)
  · exact Or.inr ⟨i, PrimeSpectrum.ext hi⟩

end Langlands.CommutativeAlgebra.DiscreteValuationSubringIntersection
