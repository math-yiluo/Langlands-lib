import Langlands.Global.Adelic
import Langlands.Global.IntegralFiniteAdeles

/-!
# Prime-to-`p` finite adeles of the rationals

The restricted product of the actual completions of `ℚ` at the finite places
whose prime ideal does not contain `p`, its diagonal `ℚ`-algebra structure,
restriction from the full finite adeles, and its compact open integral subring.
See `PrimeToFiniteAdeles.md` for sources and conventions.
-/

noncomputable section

namespace Langlands.Global

open scoped RestrictedProduct
open NumberField IsDedekindDomain

/-- Finite places of `ℚ` whose prime ideal does not contain `p`. For prime `p`
these are the finite places other than the place of `p`
(`existsUnique_finitePlace_natCast_mem`). -/
abbrev PrimeToFinitePlace (p : ℕ) := {v : FinitePlace ℚ // (p : 𝓞 ℚ) ∉ v.asIdeal}

/-- The restricted product of the completions at the places in `PrimeToFinitePlace p`,
relative to their completed integers and the cofinite filter. -/
abbrev PrimeToFiniteAdeles (p : ℕ) :=
  Πʳ v : PrimeToFinitePlace p, [FiniteCompletion ℚ v.1, v.1.adicCompletionIntegers ℚ]

instance (p : ℕ) : IsTopologicalRing (PrimeToFiniteAdeles p) :=
  haveI : Fact (∀ v : PrimeToFinitePlace p,
      IsOpen (v.1.adicCompletionIntegers ℚ : Set (FiniteCompletion ℚ v.1))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  RestrictedProduct.isTopologicalRing (fun v : PrimeToFinitePlace p ↦ FiniteCompletion ℚ v.1)

/-- The diagonal map sending a rational number to its image in every retained completion. -/
def primeToDiagonal (p : ℕ) : ℚ →+* PrimeToFiniteAdeles p where
  toFun x := ⟨fun v ↦ algebraMap ℚ (FiniteCompletion ℚ v.1) x,
    Subtype.val_injective.tendsto_cofinite.eventually
      (FiniteAdeleRing.cofinite_mem_adicCompletionIntegers (algebraMap ℚ (FiniteAdeles ℚ) x))⟩
  map_one' := Subtype.ext <| funext fun v ↦ map_one (algebraMap ℚ (FiniteCompletion ℚ v.1))
  map_mul' x y := Subtype.ext <| funext fun v ↦
    map_mul (algebraMap ℚ (FiniteCompletion ℚ v.1)) x y
  map_zero' := Subtype.ext <| funext fun v ↦ map_zero (algebraMap ℚ (FiniteCompletion ℚ v.1))
  map_add' x y := Subtype.ext <| funext fun v ↦
    map_add (algebraMap ℚ (FiniteCompletion ℚ v.1)) x y

@[simp]
theorem primeToDiagonal_apply (p : ℕ) (x : ℚ) (v : PrimeToFinitePlace p) :
    primeToDiagonal p x v = algebraMap ℚ (FiniteCompletion ℚ v.1) x := rfl

/-- The `ℚ`-algebra structure given by the diagonal map. -/
instance (p : ℕ) : Algebra ℚ (PrimeToFiniteAdeles p) := (primeToDiagonal p).toAlgebra

theorem primeToFiniteAdeles_algebraMap_eq (p : ℕ) :
    algebraMap ℚ (PrimeToFiniteAdeles p) = primeToDiagonal p := rfl

@[simp]
theorem primeToFiniteAdeles_algebraMap_apply (p : ℕ) (x : ℚ) (v : PrimeToFinitePlace p) :
    algebraMap ℚ (PrimeToFiniteAdeles p) x v = algebraMap ℚ (FiniteCompletion ℚ v.1) x := rfl

/-- Restriction of a finite adele to the places in `PrimeToFinitePlace p`. -/
def primeToFiniteRestriction (p : ℕ) : FiniteAdeles ℚ →A[ℚ] PrimeToFiniteAdeles p where
  toFun a := ⟨fun v ↦ a v.1, Subtype.val_injective.tendsto_cofinite.eventually a.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  cont := RestrictedProduct.mapAlong_continuous (fun v : FinitePlace ℚ ↦ FiniteCompletion ℚ v)
    (fun v : PrimeToFinitePlace p ↦ FiniteCompletion ℚ v.1) Subtype.val
    Subtype.val_injective.tendsto_cofinite (fun _ ↦ id)
    (Filter.Eventually.of_forall fun _ ↦ Set.mapsTo_id _) fun _ ↦ continuous_id

@[simp]
theorem primeToFiniteRestriction_apply (p : ℕ) (a : FiniteAdeles ℚ) (v : PrimeToFinitePlace p) :
    primeToFiniteRestriction p a v = a v.1 := rfl

/-- Restriction is compatible with the two diagonal maps. -/
@[simp]
theorem primeToFiniteRestriction_algebraMap (p : ℕ) (x : ℚ) :
    primeToFiniteRestriction p (algebraMap ℚ (FiniteAdeles ℚ) x) =
      algebraMap ℚ (PrimeToFiniteAdeles p) x :=
  (primeToFiniteRestriction p).commutes x

/-- Prime-to-`p` finite adeles integral at every retained place. -/
def primeToIntegralFiniteAdeles (p : ℕ) : Subring (PrimeToFiniteAdeles p) where
  carrier := {a | ∀ v : PrimeToFinitePlace p, a v ∈ v.1.adicCompletionIntegers ℚ}
  zero_mem' v := (v.1.adicCompletionIntegers ℚ).zero_mem
  one_mem' v := (v.1.adicCompletionIntegers ℚ).one_mem
  add_mem' ha hb v := (v.1.adicCompletionIntegers ℚ).toSubring.add_mem (ha v) (hb v)
  mul_mem' ha hb v := (v.1.adicCompletionIntegers ℚ).toSubring.mul_mem (ha v) (hb v)
  neg_mem' ha v := (v.1.adicCompletionIntegers ℚ).toSubring.neg_mem (ha v)

@[simp]
theorem mem_primeToIntegralFiniteAdeles (p : ℕ) (a : PrimeToFiniteAdeles p) :
    a ∈ primeToIntegralFiniteAdeles p ↔
      ∀ v : PrimeToFinitePlace p, a v ∈ v.1.adicCompletionIntegers ℚ :=
  Iff.rfl

/-- The natural inclusion of the integral prime-to-`p` finite adeles. -/
def primeToIntegralInclusion (p : ℕ) :
    primeToIntegralFiniteAdeles p →+* PrimeToFiniteAdeles p :=
  (primeToIntegralFiniteAdeles p).subtype

@[simp]
theorem primeToIntegralInclusion_apply (p : ℕ) (a : primeToIntegralFiniteAdeles p) :
    primeToIntegralInclusion p a = (a : PrimeToFiniteAdeles p) := rfl

theorem continuous_primeToIntegralInclusion (p : ℕ) :
    Continuous (primeToIntegralInclusion p) :=
  continuous_subtype_val

/-- Restriction of the integral finite adeles of `ℚ` to the places in
`PrimeToFinitePlace p`. -/
def primeToIntegralRestriction (p : ℕ) :
    integralFiniteAdeles ℚ →+* primeToIntegralFiniteAdeles p :=
  (primeToFiniteRestriction p).toRingHom.restrict (integralFiniteAdeles ℚ)
    (primeToIntegralFiniteAdeles p) fun _ ha v ↦ ha v.1

@[simp]
theorem coe_primeToIntegralRestriction (p : ℕ) (a : integralFiniteAdeles ℚ) :
    (primeToIntegralRestriction p a : PrimeToFiniteAdeles p) =
      primeToFiniteRestriction p (a : FiniteAdeles ℚ) := rfl

theorem primeToIntegralRestriction_apply (p : ℕ) (a : integralFiniteAdeles ℚ)
    (v : PrimeToFinitePlace p) :
    (primeToIntegralRestriction p a : PrimeToFiniteAdeles p) v = (a : FiniteAdeles ℚ) v.1 := rfl

/-- Integral restriction followed by inclusion is restriction of the underlying adele. -/
theorem primeToIntegralInclusion_comp_restriction (p : ℕ) :
    (primeToIntegralInclusion p).comp (primeToIntegralRestriction p) =
      (primeToFiniteRestriction p).toRingHom.comp (integralFiniteAdeles ℚ).subtype := rfl

theorem continuous_primeToIntegralRestriction (p : ℕ) :
    Continuous (primeToIntegralRestriction p) :=
  ((primeToFiniteRestriction p).continuous.comp continuous_subtype_val).subtype_mk _

/-- Openness is in the actual restricted-product topology. -/
theorem isOpen_primeToIntegralFiniteAdeles (p : ℕ) :
    IsOpen (primeToIntegralFiniteAdeles p : Set (PrimeToFiniteAdeles p)) :=
  RestrictedProduct.isOpen_forall_mem
    (fun v : PrimeToFinitePlace p ↦ Valued.isOpen_valuationSubring (v.1.adicCompletion ℚ))

theorem isCompact_primeToIntegralFiniteAdeles (p : ℕ) :
    IsCompact (primeToIntegralFiniteAdeles p : Set (PrimeToFiniteAdeles p)) := by
  have : ∀ v : PrimeToFinitePlace p, CompactSpace (v.1.adicCompletionIntegers ℚ) :=
    fun v ↦ isCompact_iff_compactSpace.mp (isCompact_adicCompletionIntegers ℚ v.1)
  have h := isCompact_range
    (RestrictedProduct.isEmbedding_structureMap
      (R := fun v : PrimeToFinitePlace p ↦ FiniteCompletion ℚ v.1)
      (A := fun v : PrimeToFinitePlace p ↦
        (v.1.adicCompletionIntegers ℚ : Set (FiniteCompletion ℚ v.1)))
      (𝓕 := Filter.cofinite)).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

/-- A natural prime remains a prime element of the ring of integers of `ℚ`. -/
theorem prime_natCast_ringOfIntegers (p : ℕ) (hp : p.Prime) : Prime (p : 𝓞 ℚ) := by
  have h : Prime (Rat.ringOfIntegersEquiv.symm (p : ℤ)) :=
    (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr
      (Nat.prime_iff_prime_int.mp hp)
  simpa using h

/-- For a prime `p`, a finite place of `ℚ` contains `p` in its prime ideal exactly when that
ideal is generated by `p`. -/
theorem natCast_mem_asIdeal_iff (p : ℕ) (hp : p.Prime) (v : FinitePlace ℚ) :
    (p : 𝓞 ℚ) ∈ v.asIdeal ↔ v.asIdeal = Ideal.span {(p : 𝓞 ℚ)} := by
  have hprime := prime_natCast_ringOfIntegers p hp
  have hne : Ideal.span {(p : 𝓞 ℚ)} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hprime.ne_zero
  have hspan : (Ideal.span {(p : 𝓞 ℚ)}).IsPrime :=
    (Ideal.span_singleton_prime hprime.ne_zero).mpr hprime
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ Ideal.subset_span rfl⟩
  exact ((hspan.isMaximal hne).eq_of_le v.isPrime.ne_top
    ((Ideal.span_singleton_le_iff_mem _).mpr h)).symm

/-- For a prime `p`, exactly one finite place of `ℚ` contains `p` in its prime ideal, so
`PrimeToFinitePlace p` omits exactly one finite place. -/
theorem existsUnique_finitePlace_natCast_mem (p : ℕ) (hp : p.Prime) :
    ∃! v : FinitePlace ℚ, (p : 𝓞 ℚ) ∈ v.asIdeal := by
  have hprime := prime_natCast_ringOfIntegers p hp
  have hne : Ideal.span {(p : 𝓞 ℚ)} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hprime.ne_zero
  have hspan : (Ideal.span {(p : 𝓞 ℚ)}).IsPrime :=
    (Ideal.span_singleton_prime hprime.ne_zero).mpr hprime
  refine ⟨⟨Ideal.span {(p : 𝓞 ℚ)}, hspan, hne⟩, Ideal.subset_span rfl, fun w hw ↦ ?_⟩
  exact HeightOneSpectrum.ext ((natCast_mem_asIdeal_iff p hp w).mp hw)

end Langlands.Global
