import Langlands.Representation.Smooth.IrreducibleGrothendieckProof

/-!
# Euler classes of actual finite exact sequences

Actual image inclusions, range projections and cokernel projections give the
short exact sequences used to telescope the exact finite-length K0 class.
Exactness is assumed only before the terminal degree, whose homology is kept.
-/

noncomputable section

open CategoryTheory
open Langlands.VirtualRepresentation
open scoped BigOperators

universe uR uG uV

namespace Langlands.SmoothRep.FiniteExactEuler

open IrreducibleGrothendieckProof
open FiniteLengthGrothendieckGroup

variable {k : Type uR} [Field k] {G : Type uG} [Group G] [TopologicalSpace G]

/-- The actual projection onto the invariant image of an equivariant map. -/
def toImage {A B : SmoothRep.{uR, uG, uV} k G} (f : A ⟶ B) : A ⟶ image f :=
  ofHom {
    toLinearMap := (hom f).toLinearMap.rangeRestrict
    isIntertwining' g := by
      ext v
      exact Subtype.ext (Representation.IntertwiningMap.isIntertwining _ _ (hom f) g v) }

/-- The actual range projection is surjective. -/
theorem toImage_surjective {A B : SmoothRep.{uR, uG, uV} k G} (f : A ⟶ B) :
    Function.Surjective (hom (toImage f)) := by
  rintro ⟨v, x, rfl⟩
  exact ⟨x, rfl⟩

/-- The actual quotient by an invariant submodule inherits finite length. -/
theorem quotient_hasFiniteLength {A : SmoothRep.{uR, uG, uV} k G}
    (hA : A.HasFiniteLength) (S : Subrepresentation A.representation) :
    (quotient A S).HasFiniteLength :=
  hA.of_surjective
    (f := Representation.IntertwiningMap.equivLinearMapAsModule _ _ (hom (mkQ A S)))
    (mkQ_surjective A S)

/-- The incoming image at degree zero is the actual zero subrepresentation;
at successor degree it is the actual image of the preceding differential. -/
def boundary (C : ℕ → FiniteLengthObject.{uR, uG, uV} k G)
    (d : ∀ i, (C i).val ⟶ (C (i + 1)).val) : ℕ → FiniteLengthObject.{uR, uG, uV} k G
  | 0 => ⟨subrepresentation (C 0).val ⊥, subrepresentation_hasFiniteLength (C 0).property ⊥⟩
  | i + 1 => ⟨image (d i), subrepresentation_hasFiniteLength (C (i + 1)).property _⟩

/-- The actual terminal homology: with one term it is that term, and otherwise
it is the actual target module modulo the preceding differential's range. -/
def terminal (C : ℕ → FiniteLengthObject.{uR, uG, uV} k G)
    (d : ∀ i, (C i).val ⟶ (C (i + 1)).val) : ℕ → FiniteLengthObject.{uR, uG, uV} k G
  | 0 => C 0
  | i + 1 => ⟨cokernel (d i), quotient_hasFiniteLength (C (i + 1)).property _⟩

/-- The canonical inclusion of the incoming image into a term. -/
def boundaryι (C : ℕ → FiniteLengthObject.{uR, uG, uV} k G)
    (d : ∀ i, (C i).val ⟶ (C (i + 1)).val) : ∀ i, (boundary C d i).val ⟶ (C i).val
  | 0 => subtype (C 0).val ⊥
  | i + 1 => imageι (d i)

/-- The incoming image at degree zero has zero exact class. -/
theorem boundary_zero_class (C : ℕ → FiniteLengthObject.{uR, uG, uV} k G)
    (d : ∀ i, (C i).val ⟶ (C (i + 1)).val) :
    ofObject (boundary C d 0) = 0 := by
  have : Subsingleton (subrepresentation (C 0).val ⊥).obj := by
    change Subsingleton (⊥ : Submodule k (C 0).val.obj)
    exact Submodule.subsingleton_iff_eq_bot.mpr rfl
  exact ofRepresentation_eq_zero_of_subsingleton _ _

/-- Injectivity at the start gives an actual short exact sequence with the
zero incoming image and the first actual outgoing image. -/
theorem start_shortExact (C : ℕ → FiniteLengthObject.{uR, uG, uV} k G)
    (d : ∀ i, (C i).val ⟶ (C (i + 1)).val)
    (h : Function.Injective (hom (d 0))) :
    IsShortExact (hom (boundaryι C d 0)) (hom (toImage (d 0))) := by
  refine ⟨subtype_injective _ _, toImage_surjective _, ?_⟩
  change LinearMap.range (⊥ : Submodule k (C 0).val.obj).subtype =
    LinearMap.ker (hom (d 0)).toLinearMap.rangeRestrict
  rw [Submodule.range_subtype, LinearMap.ker_rangeRestrict, LinearMap.ker_eq_bot.mpr h]

/-- Internal range-kernel exactness gives an actual short exact sequence
between the incoming image, the term, and the outgoing image. -/
theorem internal_shortExact (C : ℕ → FiniteLengthObject.{uR, uG, uV} k G)
    (d : ∀ i, (C i).val ⟶ (C (i + 1)).val) (i : ℕ)
    (h : LinearMap.range (hom (d i)).toLinearMap =
      LinearMap.ker (hom (d (i + 1))).toLinearMap) :
    IsShortExact (hom (boundaryι C d (i + 1))) (hom (toImage (d (i + 1)))) := by
  refine ⟨subtype_injective _ _, toImage_surjective _, ?_⟩
  change LinearMap.range (hom (d i)).range.toSubmodule.subtype =
    LinearMap.ker (hom (d (i + 1))).toLinearMap.rangeRestrict
  rw [Submodule.range_subtype, LinearMap.ker_rangeRestrict]
  exact h

/-- The incoming image and the terminal actual cokernel always form an
actual short exact sequence, without exactness or a splitting hypothesis. -/
theorem terminal_shortExact (C : ℕ → FiniteLengthObject.{uR, uG, uV} k G)
    (d : ∀ i, (C i).val ⟶ (C (i + 1)).val) (i : ℕ) :
    IsShortExact (hom (boundaryι C d (i + 1))) (hom (cokernelπ (d i))) := by
  refine ⟨subtype_injective _ _, mkQ_surjective _ _, ?_⟩
  change LinearMap.range (hom (d i)).range.toSubmodule.subtype =
    LinearMap.ker (hom (d i)).range.toSubmodule.mkQ
  rw [Submodule.range_subtype, Submodule.ker_mkQ]

private theorem alternating_partial_sum {M : Type*} [AddCommGroup M]
    (c b : ℕ → M) (m : ℕ) (hb : b 0 = 0)
    (hc : ∀ i, i < m → c i = b i + b (i + 1)) :
    ∑ i ∈ Finset.range m, (-1 : ℤ) ^ i • c i = -((-1 : ℤ) ^ m • b m) := by
  induction m with
  | zero => simp [hb]
  | succ m ih =>
      rw [Finset.sum_range_succ, ih (fun i hi => hc i (Nat.lt_trans hi (Nat.lt_succ_self m))),
        hc m (Nat.lt_succ_self m), smul_add, pow_succ]
      simp only [mul_neg, mul_one, neg_smul, neg_neg]
      abel

/-- The Euler class of an actual finite sequence exact before degree `m` is
the signed class of its actual terminal homology. The case `m = 0` assumes no
injectivity and retains `C 0` as homology. -/
theorem alternating_class (C : ℕ → FiniteLengthObject.{uR, uG, uV} k G)
    (d : ∀ i, (C i).val ⟶ (C (i + 1)).val) (m : ℕ)
    (hstart : 0 < m → Function.Injective (hom (d 0)))
    (hexact : ∀ i, i + 1 < m → LinearMap.range (hom (d i)).toLinearMap =
      LinearMap.ker (hom (d (i + 1))).toLinearMap) :
    ∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i • ofObject (C i) =
      (-1 : ℤ) ^ m • ofObject (terminal C d m) := by
  cases m with
  | zero => simp [terminal]
  | succ m =>
      have hclass (i : ℕ) (hi : i < m + 1) :
          ofObject (C i) = ofObject (boundary C d i) + ofObject (boundary C d (i + 1)) := by
        cases i with
        | zero => exact ofObject_shortExact (start_shortExact C d (hstart (Nat.zero_lt_succ m)))
        | succ i => exact ofObject_shortExact (internal_shortExact C d i (hexact i hi))
      have ht : ofObject (C (m + 1)) =
          ofObject (boundary C d (m + 1)) + ofObject (terminal C d (m + 1)) :=
        ofObject_shortExact (terminal_shortExact C d m)
      rw [Finset.sum_range_succ,
        alternating_partial_sum (fun i => ofObject (C i))
          (fun i => ofObject (boundary C d i)) (m + 1) (boundary_zero_class C d) hclass,
        ht, smul_add]
      abel

/-- Multiplying by the terminal parity sign gives the class of an actual
finite-length representation, including the single-term case. -/
theorem signed_alternating_class (C : ℕ → FiniteLengthObject.{uR, uG, uV} k G)
    (d : ∀ i, (C i).val ⟶ (C (i + 1)).val) (m : ℕ)
    (hstart : 0 < m → Function.Injective (hom (d 0)))
    (hexact : ∀ i, i + 1 < m → LinearMap.range (hom (d i)).toLinearMap =
      LinearMap.ker (hom (d (i + 1))).toLinearMap) :
    (-1 : ℤ) ^ m • (∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i • ofObject (C i)) =
      ofObject (terminal C d m) := by
  rw [alternating_class C d m hstart hexact, smul_smul, ← mul_pow]
  simp

/-- Every actual finite-length class has effective composition factors. -/
theorem factorMap_ofObject_effective (A : FiniteLengthObject.{uR, uG, uV} k G) :
    factorMap (ofObject A) ∈ effective := by
  change factorMap (ofRepresentation A.val A.property) ∈ effective
  rw [factorMap_ofRepresentation]
  intro c
  obtain ⟨B, hB, rfl⟩ := IrreducibleIsoClass.exists_eq c
  rw [compositionFactors_apply A B hB]
  exact Nat.cast_nonneg _

/-- Terminal exactness implies coefficientwise effectivity of the signed
Euler class in the lattice of genuine irreducible isomorphism classes. -/
theorem signed_alternating_effective (C : ℕ → FiniteLengthObject.{uR, uG, uV} k G)
    (d : ∀ i, (C i).val ⟶ (C (i + 1)).val) (m : ℕ)
    (hstart : 0 < m → Function.Injective (hom (d 0)))
    (hexact : ∀ i, i + 1 < m → LinearMap.range (hom (d i)).toLinearMap =
      LinearMap.ker (hom (d (i + 1))).toLinearMap) :
    factorMap ((-1 : ℤ) ^ m •
      (∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i • ofObject (C i))) ∈ effective := by
  rw [signed_alternating_class C d m hstart hexact]
  exact factorMap_ofObject_effective _

/-- The support sign converts descending rank signs into the usual degree
signs when degree `i` corresponds to block length `i+1`. -/
theorem descending_sign (n m i : ℕ) (hm : m + 1 ≤ n) (hi : i ≤ m) :
    (-1 : ℤ) ^ (n - (m + 1)) * (-1 : ℤ) ^ (n - (i + 1)) =
      (-1 : ℤ) ^ m * (-1 : ℤ) ^ i := by
  rw [← pow_add, ← pow_add,
    neg_one_pow_eq_pow_mod_two (n - (m + 1) + (n - (i + 1))),
    neg_one_pow_eq_pow_mod_two (m + i)]
  congr 1
  omega

/-- In descending rank-sign indexing, the common support sign converts the
Euler sum to the actual terminal homology class. -/
theorem signed_descending_class (C : ℕ → FiniteLengthObject.{uR, uG, uV} k G)
    (d : ∀ i, (C i).val ⟶ (C (i + 1)).val) (m n : ℕ) (hm : m + 1 ≤ n)
    (hstart : 0 < m → Function.Injective (hom (d 0)))
    (hexact : ∀ i, i + 1 < m → LinearMap.range (hom (d i)).toLinearMap =
      LinearMap.ker (hom (d (i + 1))).toLinearMap) :
    (-1 : ℤ) ^ (n - (m + 1)) •
      (∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ (n - (i + 1)) • ofObject (C i)) =
      ofObject (terminal C d m) := by
  calc
    _ = (-1 : ℤ) ^ m •
        (∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i • ofObject (C i)) := by
      rw [Finset.smul_sum, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [smul_smul, smul_smul, descending_sign n m i hm
        (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
    _ = _ := signed_alternating_class C d m hstart hexact

/-- An exact descending-sign expansion of any exact-K0 class implies
effectivity after multiplication by the common terminal support sign. -/
theorem effective_of_descending_expansion
    (C : ℕ → FiniteLengthObject.{uR, uG, uV} k G)
    (d : ∀ i, (C i).val ⟶ (C (i + 1)).val) (m n : ℕ) (hm : m + 1 ≤ n)
    (hstart : 0 < m → Function.Injective (hom (d 0)))
    (hexact : ∀ i, i + 1 < m → LinearMap.range (hom (d i)).toLinearMap =
      LinearMap.ker (hom (d (i + 1))).toLinearMap)
    (x : FiniteLengthGrothendieckGroup.{uR, uG, uV} k G)
    (hx : x = ∑ i ∈ Finset.range (m + 1),
      (-1 : ℤ) ^ (n - (i + 1)) • ofObject (C i)) :
    factorMap ((-1 : ℤ) ^ (n - (m + 1)) • x) ∈ effective := by
  rw [hx, signed_descending_class C d m n hm hstart hexact]
  exact factorMap_ofObject_effective _

end Langlands.SmoothRep.FiniteExactEuler
