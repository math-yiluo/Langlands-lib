import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.RingTheory.DedekindDomain.SInteger

/-!
# Actual finite-adelic rings at a finite set of places

The level ring is an open subring of Mathlib's actual finite adele ring.
It has the diagonal action of the actual ring of `S`-integers.
-/

noncomputable section

universe u

open IsDedekindDomain

namespace Langlands.Global

variable (R K : Type u) [CommRing R] [IsDedekindDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

/-- Actual finite adeles integral at every finite place outside `S`. -/
def finiteAdeleLevel (S : Finset (HeightOneSpectrum R)) :
    Subring (FiniteAdeleRing R K) where
  carrier := {a | ∀ v, v ∉ S → a v ∈ v.adicCompletionIntegers K}
  zero_mem' v _ := (v.adicCompletionIntegers K).zero_mem
  one_mem' v _ := (v.adicCompletionIntegers K).one_mem
  add_mem' ha hb v hv := (v.adicCompletionIntegers K).toSubring.add_mem (ha v hv) (hb v hv)
  mul_mem' ha hb v hv := (v.adicCompletionIntegers K).toSubring.mul_mem (ha v hv) (hb v hv)
  neg_mem' ha v hv := (v.adicCompletionIntegers K).toSubring.neg_mem (ha v hv)

@[simp]
theorem mem_finiteAdeleLevel (S : Finset (HeightOneSpectrum R)) (a : FiniteAdeleRing R K) :
    a ∈ finiteAdeleLevel R K S ↔
      ∀ v, v ∉ S → a v ∈ v.adicCompletionIntegers K := Iff.rfl

/-- The level ring is open in the actual finite-adelic topology. -/
theorem isOpen_finiteAdeleLevel (S : Finset (HeightOneSpectrum R)) :
    IsOpen (finiteAdeleLevel R K S : Set (FiniteAdeleRing R K)) :=
  RestrictedProduct.isOpen_forall_imp_mem
    (fun v : HeightOneSpectrum R => Valued.isOpen_valuationSubring (v.adicCompletion K))

/-- Increasing `S` gives an inclusion of the actual level subrings. -/
theorem finiteAdeleLevel_mono {S T : Finset (HeightOneSpectrum R)} (hST : S ⊆ T) :
    finiteAdeleLevel R K S ≤ finiteAdeleLevel R K T :=
  fun _ ha v hv => ha v (fun h => hv (hST h))

/-- The transition map between actual finite-adelic level rings. -/
def finiteAdeleLevelMap {S T : Finset (HeightOneSpectrum R)} (hST : S ⊆ T) :
    finiteAdeleLevel R K S →+* finiteAdeleLevel R K T :=
  Subring.inclusion (finiteAdeleLevel_mono R K hST)

@[simp]
theorem finiteAdeleLevelMap_coe {S T : Finset (HeightOneSpectrum R)} (hST : S ⊆ T)
    (a : finiteAdeleLevel R K S) :
    (finiteAdeleLevelMap R K hST a : FiniteAdeleRing R K) = a := rfl

/-- The diagonal map from the actual ring of `S`-integers into the level ring. -/
def finiteAdeleLevelDiagonal (S : Finset (HeightOneSpectrum R)) :
    (S : Set (HeightOneSpectrum R)).integer K →+* finiteAdeleLevel R K S :=
  (((algebraMap K (FiniteAdeleRing R K)).comp
    ((S : Set (HeightOneSpectrum R)).integer K).toSubring.subtype).codRestrict
      (finiteAdeleLevel R K S) (by
        intro c v hv
        change Valued.v (algebraMap K (v.adicCompletion K) c.val) ≤ 1
        simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
          Algebra.algebraMap_self, RingHom.id_apply,
          HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
        exact c.property v hv))

instance (S : Finset (HeightOneSpectrum R)) :
    Algebra ((S : Set (HeightOneSpectrum R)).integer K) (finiteAdeleLevel R K S) :=
  (finiteAdeleLevelDiagonal R K S).toAlgebra

@[simp]
theorem finiteAdeleLevelDiagonal_apply (S : Finset (HeightOneSpectrum R))
    (c : (S : Set (HeightOneSpectrum R)).integer K) (v : HeightOneSpectrum R) :
    (finiteAdeleLevelDiagonal R K S c : FiniteAdeleRing R K) v =
      algebraMap K (v.adicCompletion K) c.val := rfl

/-- Assemble unrestricted components at `S` and integral components away from `S`. -/
def finiteAdeleLevelAssemble (S : Finset (HeightOneSpectrum R))
    (p : (∀ v : {v : HeightOneSpectrum R // v ∈ S}, v.1.adicCompletion K) ×
      (∀ v : {v : HeightOneSpectrum R // v ∉ S}, v.1.adicCompletionIntegers K)) :
    finiteAdeleLevel R K S := by
  classical
  let a : ∀ v : HeightOneSpectrum R, v.adicCompletion K :=
    fun v => if h : v ∈ S then p.1 ⟨v, h⟩ else (p.2 ⟨v, h⟩ : v.adicCompletion K)
  have ha (v : HeightOneSpectrum R) (hv : v ∉ S) :
      a v ∈ v.adicCompletionIntegers K := by
    simp only [a, dite_eq_right hv]
    exact (p.2 ⟨v, hv⟩).property
  refine ⟨⟨a, ?_⟩, ha⟩
  apply Filter.eventually_cofinite.mpr
  exact S.finite_toSet.subset (fun v hv => by
    by_contra h
    exact hv (ha v h))

/-- The actual finite-adelic level ring is the product of its local value rings. -/
def finiteAdeleLevelProductEquiv (S : Finset (HeightOneSpectrum R)) :
    finiteAdeleLevel R K S ≃+*
      (∀ v : {v : HeightOneSpectrum R // v ∈ S}, v.1.adicCompletion K) ×
        (∀ v : {v : HeightOneSpectrum R // v ∉ S}, v.1.adicCompletionIntegers K) where
  toFun a :=
    (fun v => (a : FiniteAdeleRing R K) v.1,
      fun v => ⟨(a : FiniteAdeleRing R K) v.1, a.property v.1 v.property⟩)
  invFun := finiteAdeleLevelAssemble R K S
  left_inv a := by
    classical
    apply Subtype.ext
    apply FiniteAdeleRing.ext
    intro v
    change (if h : v ∈ S then _ else _) = _
    split <;> rfl
  right_inv p := by
    classical
    apply Prod.ext
    · funext v
      change (if h : v.1 ∈ S then _ else _) = _
      simp only [dite_eq_left v.property]
    · funext v
      apply Subtype.ext
      change (if h : v.1 ∈ S then _ else _) = _
      simp only [dite_eq_right v.property]
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem finiteAdeleLevelProductEquiv_fst (S : Finset (HeightOneSpectrum R))
    (a : finiteAdeleLevel R K S) (v : {v : HeightOneSpectrum R // v ∈ S}) :
    (finiteAdeleLevelProductEquiv R K S a).1 v = (a : FiniteAdeleRing R K) v.1 := rfl

@[simp]
theorem finiteAdeleLevelProductEquiv_snd (S : Finset (HeightOneSpectrum R))
    (a : finiteAdeleLevel R K S) (v : {v : HeightOneSpectrum R // v ∉ S}) :
    ((finiteAdeleLevelProductEquiv R K S a).2 v : v.1.adicCompletion K) =
      (a : FiniteAdeleRing R K) v.1 := rfl

end Langlands.Global
