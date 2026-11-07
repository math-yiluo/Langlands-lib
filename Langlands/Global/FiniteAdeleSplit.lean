import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.Topology.Algebra.Algebra.Equiv
import Langlands.Global.PrimeToFiniteAdeles
import Langlands.Topology.RestrictedProductSplit

/-!
# Splitting the finite adeles at finitely many places

For a decidable predicate `p` on the finite places of a number field `K` satisfied by only
finitely many places, the finite adeles of `K` are identified, as a topological ring, with the
full product of the completions at the places satisfying `p` times the finite adeles away from
those places. The integral finite adeles correspond to the product of the local integer rings
and the away integral subring. For `K = ℚ` and the places whose prime ideal contains a nonzero
natural number `n`, the second factor is the published `PrimeToFiniteAdeles n`, and the
splitting is an isomorphism of topological `ℚ`-algebras.
-/

noncomputable section

open Filter Set
open scoped RestrictedProduct

namespace RestrictedProduct

variable {ι : Type*} (R : ι → Type*) {S : ι → Type*} [Π i, SetLike (S i) (R i)] (B : Π i, S i)
variable [Π i, Ring (R i)] [∀ i, SubringClass (S i) (R i)]

/-- Over a finite index type the cofinite restricted product of rings is the full product. -/
def finiteRingEquiv [Finite ι] : Πʳ i, [R i, B i] ≃+* Π i, R i where
  toFun x i := x i
  invFun x := ⟨x, by rw [cofinite_eq_bot]; exact eventually_bot⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem finiteRingEquiv_apply [Finite ι] (x : Πʳ i, [R i, B i]) (i : ι) :
    finiteRingEquiv R B x i = x i :=
  rfl

@[simp]
theorem finiteRingEquiv_symm_apply [Finite ι] (x : Π i, R i) (i : ι) :
    (finiteRingEquiv R B).symm x i = x i :=
  rfl

variable (p : ι → Prop) [DecidablePred p]

/-- Splitting a cofinite restricted product of rings along `p`, as a ring isomorphism. -/
def splitRingEquiv :
    Πʳ i, [R i, B i] ≃+* Πʳ (i : {i // p i}), [R i, B i] × Πʳ (i : {i // ¬ p i}), [R i, B i] where
  toEquiv := splitEquiv R (fun i => (B i : Set (R i))) p
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem splitRingEquiv_apply_fst (x : Πʳ i, [R i, B i]) (i : {i // p i}) :
    (splitRingEquiv R B p x).1 i = x i :=
  rfl

@[simp]
theorem splitRingEquiv_apply_snd (x : Πʳ i, [R i, B i]) (i : {i // ¬ p i}) :
    (splitRingEquiv R B p x).2 i = x i :=
  rfl

theorem splitRingEquiv_symm_apply
    (z : Πʳ (i : {i // p i}), [R i, B i] × Πʳ (i : {i // ¬ p i}), [R i, B i]) :
    (splitRingEquiv R B p).symm z = glueSubtype R (fun i => (B i : Set (R i))) p z.1 z.2 :=
  rfl

/-- If only finitely many indices satisfy `p`, the cofinite restricted product of rings is the
full product over `{i // p i}` times the cofinite restricted product over `{i // ¬ p i}`. -/
def splitFiniteRingEquiv [Finite {i // p i}] :
    Πʳ i, [R i, B i] ≃+* (Π i : {i // p i}, R i) × Πʳ (i : {i // ¬ p i}), [R i, B i] :=
  (splitRingEquiv R B p).trans
    ((finiteRingEquiv (fun i : {i // p i} => R i) fun i => B i).prodCongr (RingEquiv.refl _))

@[simp]
theorem splitFiniteRingEquiv_apply_fst [Finite {i // p i}] (x : Πʳ i, [R i, B i])
    (i : {i // p i}) : (splitFiniteRingEquiv R B p x).1 i = x i :=
  rfl

@[simp]
theorem splitFiniteRingEquiv_apply_snd [Finite {i // p i}] (x : Πʳ i, [R i, B i])
    (i : {i // ¬ p i}) : (splitFiniteRingEquiv R B p x).2 i = x i :=
  rfl

theorem splitFiniteRingEquiv_symm_apply_of_pos [Finite {i // p i}]
    (z : (Π i : {i // p i}, R i) × Πʳ (i : {i // ¬ p i}), [R i, B i]) {i : ι} (h : p i) :
    (splitFiniteRingEquiv R B p).symm z i = z.1 ⟨i, h⟩ :=
  glueSubtype_apply_of_pos R (fun i => (B i : Set (R i))) p
    ((finiteRingEquiv (fun i : {i // p i} => R i) fun i => B i).symm z.1) z.2 h

theorem splitFiniteRingEquiv_symm_apply_of_neg [Finite {i // p i}]
    (z : (Π i : {i // p i}, R i) × Πʳ (i : {i // ¬ p i}), [R i, B i]) {i : ι} (h : ¬ p i) :
    (splitFiniteRingEquiv R B p).symm z i = z.2 ⟨i, h⟩ :=
  glueSubtype_apply_of_neg R (fun i => (B i : Set (R i))) p
    ((finiteRingEquiv (fun i : {i // p i} => R i) fun i => B i).symm z.1) z.2 h

variable [∀ i, TopologicalSpace (R i)]

/-- The ring splitting has the same underlying map as the homeomorphism
`splitFiniteHomeomorph`. -/
theorem coe_splitFiniteRingEquiv [Finite {i // p i}] (hB : ∀ i, IsOpen (B i : Set (R i))) :
    ⇑(splitFiniteRingEquiv R B p) = splitFiniteHomeomorph R p hB :=
  rfl

theorem coe_splitFiniteRingEquiv_symm [Finite {i // p i}] (hB : ∀ i, IsOpen (B i : Set (R i))) :
    ⇑(splitFiniteRingEquiv R B p).symm = (splitFiniteHomeomorph R p hB).symm :=
  rfl

end RestrictedProduct

namespace Langlands.Global

open NumberField IsDedekindDomain

universe u

variable (K : Type u) [Field K] [NumberField K] (p : FinitePlace K → Prop)

/-- The finite adeles of `K` away from the places satisfying `p`: the restricted product of the
completions at the places not satisfying `p`, relative to their completed integers and the
cofinite filter. -/
abbrev AwayFiniteAdeles :=
  Πʳ v : {v : FinitePlace K // ¬ p v}, [FiniteCompletion K v.1, v.1.adicCompletionIntegers K]

instance : IsTopologicalRing (AwayFiniteAdeles K p) :=
  haveI : Fact (∀ v : {v : FinitePlace K // ¬ p v},
      IsOpen (v.1.adicCompletionIntegers K : Set (FiniteCompletion K v.1))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  RestrictedProduct.isTopologicalRing
    (fun v : {v : FinitePlace K // ¬ p v} ↦ FiniteCompletion K v.1)

/-- Restriction of a finite adele to the places not satisfying `p`. -/
def awayRestriction : FiniteAdeles K →+* AwayFiniteAdeles K p where
  toFun a := ⟨fun v ↦ a v.1, Subtype.val_injective.tendsto_cofinite.eventually a.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem awayRestriction_apply (a : FiniteAdeles K) (v : {v : FinitePlace K // ¬ p v}) :
    awayRestriction K p a v = a v.1 :=
  rfl

theorem continuous_awayRestriction : Continuous (awayRestriction K p) :=
  RestrictedProduct.mapAlong_continuous (fun v : FinitePlace K ↦ FiniteCompletion K v)
    (fun v : {v : FinitePlace K // ¬ p v} ↦ FiniteCompletion K v.1) Subtype.val
    Subtype.val_injective.tendsto_cofinite (fun _ ↦ id)
    (Eventually.of_forall fun _ ↦ Set.mapsTo_id _) fun _ ↦ continuous_id

/-- The diagonal map sending an element of `K` to its image in every completion at a place not
satisfying `p`. -/
def awayDiagonal : K →+* AwayFiniteAdeles K p :=
  (awayRestriction K p).comp (algebraMap K (FiniteAdeles K))

@[simp]
theorem awayDiagonal_apply (x : K) (v : {v : FinitePlace K // ¬ p v}) :
    awayDiagonal K p x v = algebraMap K (FiniteCompletion K v.1) x :=
  rfl

/-- Away finite adeles integral at every place not satisfying `p`. -/
def awayIntegralFiniteAdeles : Subring (AwayFiniteAdeles K p) where
  carrier := {a | ∀ v : {v : FinitePlace K // ¬ p v}, a v ∈ v.1.adicCompletionIntegers K}
  zero_mem' v := (v.1.adicCompletionIntegers K).zero_mem
  one_mem' v := (v.1.adicCompletionIntegers K).one_mem
  add_mem' ha hb v := (v.1.adicCompletionIntegers K).toSubring.add_mem (ha v) (hb v)
  mul_mem' ha hb v := (v.1.adicCompletionIntegers K).toSubring.mul_mem (ha v) (hb v)
  neg_mem' ha v := (v.1.adicCompletionIntegers K).toSubring.neg_mem (ha v)

@[simp]
theorem mem_awayIntegralFiniteAdeles (a : AwayFiniteAdeles K p) :
    a ∈ awayIntegralFiniteAdeles K p ↔
      ∀ v : {v : FinitePlace K // ¬ p v}, a v ∈ v.1.adicCompletionIntegers K :=
  Iff.rfl

/-- Openness is in the actual restricted-product topology. -/
theorem isOpen_awayIntegralFiniteAdeles :
    IsOpen (awayIntegralFiniteAdeles K p : Set (AwayFiniteAdeles K p)) :=
  RestrictedProduct.isOpen_forall_mem
    (fun v : {v : FinitePlace K // ¬ p v} ↦ Valued.isOpen_valuationSubring (v.1.adicCompletion K))

theorem isCompact_awayIntegralFiniteAdeles :
    IsCompact (awayIntegralFiniteAdeles K p : Set (AwayFiniteAdeles K p)) := by
  have : ∀ v : {v : FinitePlace K // ¬ p v}, CompactSpace (v.1.adicCompletionIntegers K) :=
    fun v ↦ isCompact_iff_compactSpace.mp (isCompact_adicCompletionIntegers K v.1)
  have h := isCompact_range
    (RestrictedProduct.isEmbedding_structureMap
      (R := fun v : {v : FinitePlace K // ¬ p v} ↦ FiniteCompletion K v.1)
      (A := fun v : {v : FinitePlace K // ¬ p v} ↦
        (v.1.adicCompletionIntegers K : Set (FiniteCompletion K v.1)))
      (𝓕 := Filter.cofinite)).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

/-- Families of local elements at the places satisfying `p` that are integral at each of them. -/
def localIntegralProduct : Subring (Π v : {v : FinitePlace K // p v}, FiniteCompletion K v.1) where
  carrier := {x | ∀ v : {v : FinitePlace K // p v}, x v ∈ v.1.adicCompletionIntegers K}
  zero_mem' v := (v.1.adicCompletionIntegers K).zero_mem
  one_mem' v := (v.1.adicCompletionIntegers K).one_mem
  add_mem' ha hb v := (v.1.adicCompletionIntegers K).toSubring.add_mem (ha v) (hb v)
  mul_mem' ha hb v := (v.1.adicCompletionIntegers K).toSubring.mul_mem (ha v) (hb v)
  neg_mem' ha v := (v.1.adicCompletionIntegers K).toSubring.neg_mem (ha v)

@[simp]
theorem mem_localIntegralProduct (x : Π v : {v : FinitePlace K // p v}, FiniteCompletion K v.1) :
    x ∈ localIntegralProduct K p ↔
      ∀ v : {v : FinitePlace K // p v}, x v ∈ v.1.adicCompletionIntegers K :=
  Iff.rfl

theorem isCompact_localIntegralProduct :
    IsCompact (localIntegralProduct K p : Set (Π v : {v : FinitePlace K // p v},
      FiniteCompletion K v.1)) := by
  have h := isCompact_univ_pi fun v : {v : FinitePlace K // p v} ↦
    isCompact_adicCompletionIntegers K v.1
  convert h using 1
  ext x
  simp [Set.mem_pi]

theorem isOpen_localIntegralProduct [Finite {v : FinitePlace K // p v}] :
    IsOpen (localIntegralProduct K p : Set (Π v : {v : FinitePlace K // p v},
      FiniteCompletion K v.1)) := by
  have hv : ∀ v : {v : FinitePlace K // p v},
      IsOpen (v.1.adicCompletionIntegers K : Set (FiniteCompletion K v.1)) :=
    fun v ↦ Valued.isOpen_valuationSubring (v.1.adicCompletion K)
  have h := isOpen_set_pi (Set.finite_univ (α := {v : FinitePlace K // p v})) fun v _ ↦ hv v
  convert h using 1
  ext x
  simp [Set.mem_pi]

/-- Only finitely many finite places have a prime ideal containing a given nonzero integer. -/
theorem finite_mem_asIdeal (a : 𝓞 K) (ha : a ≠ 0) :
    Finite {v : FinitePlace K // a ∈ v.asIdeal} := by
  have hspan : Ideal.span {a} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact ha
  refine Set.Finite.to_subtype (s := {v : FinitePlace K | a ∈ v.asIdeal})
    ((Ideal.finite_factors hspan).subset fun v hv ↦ ?_)
  exact Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hv)

theorem finite_natCast_mem_asIdeal (n : ℕ) (hn : n ≠ 0) :
    Finite {v : FinitePlace K // (n : 𝓞 K) ∈ v.asIdeal} :=
  finite_mem_asIdeal K (n : 𝓞 K) (Nat.cast_ne_zero.mpr hn)

variable [DecidablePred p] [Finite {v : FinitePlace K // p v}]

/-- The finite adeles are the full product of the completions at the finitely many places
satisfying `p` times the finite adeles away from those places. -/
def finiteAdelesSplit :
    FiniteAdeles K ≃+* (Π v : {v : FinitePlace K // p v}, FiniteCompletion K v.1) ×
      AwayFiniteAdeles K p :=
  RestrictedProduct.splitFiniteRingEquiv (fun v : FinitePlace K ↦ FiniteCompletion K v)
    (fun v ↦ v.adicCompletionIntegers K) p

@[simp]
theorem finiteAdelesSplit_apply_fst (a : FiniteAdeles K) (v : {v : FinitePlace K // p v}) :
    (finiteAdelesSplit K p a).1 v = a v.1 :=
  rfl

@[simp]
theorem finiteAdelesSplit_apply_snd (a : FiniteAdeles K) :
    (finiteAdelesSplit K p a).2 = awayRestriction K p a :=
  rfl

theorem finiteAdelesSplit_symm_apply_of_pos
    (z : (Π v : {v : FinitePlace K // p v}, FiniteCompletion K v.1) × AwayFiniteAdeles K p)
    {v : FinitePlace K} (h : p v) :
    (finiteAdelesSplit K p).symm z v = z.1 ⟨v, h⟩ :=
  RestrictedProduct.splitFiniteRingEquiv_symm_apply_of_pos _ _ p z h

theorem finiteAdelesSplit_symm_apply_of_neg
    (z : (Π v : {v : FinitePlace K // p v}, FiniteCompletion K v.1) × AwayFiniteAdeles K p)
    {v : FinitePlace K} (h : ¬ p v) :
    (finiteAdelesSplit K p).symm z v = z.2 ⟨v, h⟩ :=
  RestrictedProduct.splitFiniteRingEquiv_symm_apply_of_neg _ _ p z h

/-- The splitting is a homeomorphism for the restricted-product topologies. -/
def finiteAdelesSplitHomeomorph :
    FiniteAdeles K ≃ₜ (Π v : {v : FinitePlace K // p v}, FiniteCompletion K v.1) ×
      AwayFiniteAdeles K p :=
  RestrictedProduct.splitFiniteHomeomorph (fun v : FinitePlace K ↦ FiniteCompletion K v) p
    fun v ↦ Valued.isOpen_valuationSubring (v.adicCompletion K)

@[simp]
theorem coe_finiteAdelesSplitHomeomorph :
    ⇑(finiteAdelesSplitHomeomorph K p) = finiteAdelesSplit K p :=
  rfl

@[simp]
theorem coe_finiteAdelesSplitHomeomorph_symm :
    ⇑(finiteAdelesSplitHomeomorph K p).symm = (finiteAdelesSplit K p).symm :=
  rfl

theorem continuous_finiteAdelesSplit : Continuous (finiteAdelesSplit K p) :=
  (finiteAdelesSplitHomeomorph K p).continuous

theorem continuous_finiteAdelesSplit_symm : Continuous (finiteAdelesSplit K p).symm :=
  (finiteAdelesSplitHomeomorph K p).symm.continuous

/-- The splitting sends the diagonal image of `x : K` to its local images at the places
satisfying `p` and its away diagonal image. -/
theorem finiteAdelesSplit_algebraMap (x : K) :
    finiteAdelesSplit K p (algebraMap K (FiniteAdeles K) x) =
      (fun v : {v : FinitePlace K // p v} ↦ algebraMap K (FiniteCompletion K v.1) x,
        awayDiagonal K p x) :=
  rfl

/-- A finite adele is integral exactly when its components at the places satisfying `p` are
integral and its away part is integral at every remaining place. -/
theorem mem_integralFiniteAdeles_iff_finiteAdelesSplit (a : FiniteAdeles K) :
    a ∈ integralFiniteAdeles K ↔
      (finiteAdelesSplit K p a).1 ∈ localIntegralProduct K p ∧
        (finiteAdelesSplit K p a).2 ∈ awayIntegralFiniteAdeles K p := by
  rw [mem_integralFiniteAdeles]
  refine ⟨fun h ↦ ⟨fun v ↦ h v.1, fun v ↦ h v.1⟩, fun h v ↦ ?_⟩
  by_cases hv : p v
  · exact h.1 ⟨v, hv⟩
  · exact h.2 ⟨v, hv⟩

/-- The splitting carries the integral finite adeles onto the product of the local integral
product and the away integral subring. -/
theorem map_integralFiniteAdeles_finiteAdelesSplit :
    (integralFiniteAdeles K).map (finiteAdelesSplit K p).toRingHom =
      (localIntegralProduct K p).prod (awayIntegralFiniteAdeles K p) := by
  ext z
  rw [Subring.mem_map, Subring.mem_prod]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (mem_integralFiniteAdeles_iff_finiteAdelesSplit K p a).mp ha
  · intro h
    refine ⟨(finiteAdelesSplit K p).symm z, ?_, (finiteAdelesSplit K p).apply_symm_apply z⟩
    refine (mem_integralFiniteAdeles_iff_finiteAdelesSplit K p _).mpr ?_
    rw [RingEquiv.apply_symm_apply]
    exact h

/-- The splitting restricted to the integral finite adeles. -/
def integralFiniteAdelesSplit :
    integralFiniteAdeles K ≃+* localIntegralProduct K p × awayIntegralFiniteAdeles K p :=
  ((finiteAdelesSplit K p).subringMap (s := integralFiniteAdeles K)).trans
    ((RingEquiv.subringCongr (map_integralFiniteAdeles_finiteAdelesSplit K p)).trans
      (Subring.prodEquiv _ _))

@[simp]
theorem coe_integralFiniteAdelesSplit_fst (a : integralFiniteAdeles K) :
    ((integralFiniteAdelesSplit K p a).1 :
      Π v : {v : FinitePlace K // p v}, FiniteCompletion K v.1) =
        (finiteAdelesSplit K p a).1 :=
  rfl

@[simp]
theorem coe_integralFiniteAdelesSplit_snd (a : integralFiniteAdeles K) :
    ((integralFiniteAdelesSplit K p a).2 : AwayFiniteAdeles K p) =
      (finiteAdelesSplit K p a).2 :=
  rfl

section Rat

variable (n : ℕ)

/-- For `K = ℚ` and the places whose prime ideal contains `n`, the away finite adeles are the
published prime-to-`n` finite adeles. -/
theorem awayFiniteAdeles_natCast :
    AwayFiniteAdeles ℚ (fun v ↦ (n : 𝓞 ℚ) ∈ v.asIdeal) = PrimeToFiniteAdeles n :=
  rfl

theorem awayRestriction_natCast :
    awayRestriction ℚ (fun v ↦ (n : 𝓞 ℚ) ∈ v.asIdeal) =
      (primeToFiniteRestriction n).toRingHom :=
  rfl

theorem awayDiagonal_natCast :
    awayDiagonal ℚ (fun v ↦ (n : 𝓞 ℚ) ∈ v.asIdeal) = primeToDiagonal n :=
  rfl

theorem awayIntegralFiniteAdeles_natCast :
    awayIntegralFiniteAdeles ℚ (fun v ↦ (n : 𝓞 ℚ) ∈ v.asIdeal) = primeToIntegralFiniteAdeles n :=
  rfl

open scoped Classical in
/-- For a nonzero natural number `n`, the finite adeles of `ℚ` are, as a topological
`ℚ`-algebra, the product of the completions at the places whose prime ideal contains `n` and
the prime-to-`n` finite adeles. -/
def ratFiniteAdelesSplit (hn : n ≠ 0) :
    FiniteAdeles ℚ ≃A[ℚ]
      (Π v : {v : FinitePlace ℚ // (n : 𝓞 ℚ) ∈ v.asIdeal}, FiniteCompletion ℚ v.1) ×
        PrimeToFiniteAdeles n :=
  haveI := finite_natCast_mem_asIdeal ℚ n hn
  { toRingEquiv := finiteAdelesSplit ℚ fun v ↦ (n : 𝓞 ℚ) ∈ v.asIdeal
    commutes' _ := rfl
    continuous_toFun := continuous_finiteAdelesSplit ℚ fun v ↦ (n : 𝓞 ℚ) ∈ v.asIdeal
    continuous_invFun := continuous_finiteAdelesSplit_symm ℚ fun v ↦ (n : 𝓞 ℚ) ∈ v.asIdeal }

@[simp]
theorem ratFiniteAdelesSplit_apply_fst (hn : n ≠ 0) (a : FiniteAdeles ℚ)
    (v : {v : FinitePlace ℚ // (n : 𝓞 ℚ) ∈ v.asIdeal}) :
    (ratFiniteAdelesSplit n hn a).1 v = a v.1 :=
  rfl

@[simp]
theorem ratFiniteAdelesSplit_apply_snd (hn : n ≠ 0) (a : FiniteAdeles ℚ) :
    (ratFiniteAdelesSplit n hn a).2 = primeToFiniteRestriction n a :=
  rfl

/-- The second projection of the rational splitting is the published restriction map. -/
theorem snd_comp_ratFiniteAdelesSplit (hn : n ≠ 0) :
    (ContinuousAlgHom.snd ℚ _ _).comp (ratFiniteAdelesSplit n hn).toContinuousAlgHom =
      primeToFiniteRestriction n :=
  rfl

open scoped Classical in
theorem ratFiniteAdelesSplit_symm_apply_of_mem (hn : n ≠ 0)
    (z : (Π v : {v : FinitePlace ℚ // (n : 𝓞 ℚ) ∈ v.asIdeal}, FiniteCompletion ℚ v.1) ×
      PrimeToFiniteAdeles n) {v : FinitePlace ℚ} (h : (n : 𝓞 ℚ) ∈ v.asIdeal) :
    (ratFiniteAdelesSplit n hn).symm z v = z.1 ⟨v, h⟩ := by
  have := finite_natCast_mem_asIdeal ℚ n hn
  exact finiteAdelesSplit_symm_apply_of_pos ℚ (fun v ↦ (n : 𝓞 ℚ) ∈ v.asIdeal) z h

open scoped Classical in
theorem ratFiniteAdelesSplit_symm_apply_of_not_mem (hn : n ≠ 0)
    (z : (Π v : {v : FinitePlace ℚ // (n : 𝓞 ℚ) ∈ v.asIdeal}, FiniteCompletion ℚ v.1) ×
      PrimeToFiniteAdeles n) {v : FinitePlace ℚ} (h : (n : 𝓞 ℚ) ∉ v.asIdeal) :
    (ratFiniteAdelesSplit n hn).symm z v = z.2 ⟨v, h⟩ := by
  have := finite_natCast_mem_asIdeal ℚ n hn
  exact finiteAdelesSplit_symm_apply_of_neg ℚ (fun v ↦ (n : 𝓞 ℚ) ∈ v.asIdeal) z h

/-- A rational finite adele is integral exactly when its components at the places whose prime
ideal contains `n` are integral and its prime-to-`n` part is integral. -/
theorem mem_integralFiniteAdeles_iff_ratFiniteAdelesSplit (hn : n ≠ 0) (a : FiniteAdeles ℚ) :
    a ∈ integralFiniteAdeles ℚ ↔
      (ratFiniteAdelesSplit n hn a).1 ∈ localIntegralProduct ℚ (fun v ↦ (n : 𝓞 ℚ) ∈ v.asIdeal) ∧
        (ratFiniteAdelesSplit n hn a).2 ∈ primeToIntegralFiniteAdeles n := by
  classical
  have := finite_natCast_mem_asIdeal ℚ n hn
  exact mem_integralFiniteAdeles_iff_finiteAdelesSplit ℚ (fun v ↦ (n : 𝓞 ℚ) ∈ v.asIdeal) a

end Rat

end Langlands.Global
