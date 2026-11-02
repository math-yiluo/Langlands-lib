import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTupleCrossEmbedding

/-! # Relation laws for symmetric cross-correspondences -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

variable (E : EtaleEquivalenceRelation.{u}) [IsSeparated E.s]

/-- An ordered tuple is related to itself. -/
def tupleCrossUnit (n : ℕ) : E.tupleDistinctScheme n ⟶ E.tupleCrossScheme n n :=
  E.tupleCrossLift n n (𝟙 _) (𝟙 _) (E.tupleDistinctProjection n 0 ≫ E.unit)
    (by simp) (by simp)

@[reassoc (attr := simp)]
theorem tupleCrossUnit_left (n : ℕ) :
    E.tupleCrossUnit n ≫ E.tupleCrossLeft n n = 𝟙 _ := by
  simp [tupleCrossUnit]

@[reassoc (attr := simp)]
theorem tupleCrossUnit_right (n : ℕ) :
    E.tupleCrossUnit n ≫ E.tupleCrossRight n n = 𝟙 _ := by
  simp [tupleCrossUnit]

/-- Swap the two ordered tuples and reverse their relation arrow. -/
def tupleCrossSwap (m n : ℕ) : E.tupleCrossScheme m n ⟶ E.tupleCrossScheme n m :=
  E.tupleCrossLift n m (E.tupleCrossRight m n) (E.tupleCrossLeft m n)
    (E.tupleCrossMap m n ≫ E.inverse)
    (by simpa using E.tupleCrossMap_s m n)
    (by simpa using E.tupleCrossMap_t m n)

@[reassoc (attr := simp)]
theorem tupleCrossSwap_left (m n : ℕ) :
    E.tupleCrossSwap m n ≫ E.tupleCrossLeft n m = E.tupleCrossRight m n := by
  simp [tupleCrossSwap]

@[reassoc (attr := simp)]
theorem tupleCrossSwap_right (m n : ℕ) :
    E.tupleCrossSwap m n ≫ E.tupleCrossRight n m = E.tupleCrossLeft m n := by
  simp [tupleCrossSwap]

section Affine

variable [IsAffine E.U] [IsAffine E.R]

/-- Ordered representatives of the endpoints lift a symmetric cross arrow. -/
theorem tupleCross_exists_of_symmetric (m n : ℕ) {T : Scheme.{u}}
    (a : T ⟶ E.tupleDistinctScheme m) (b : T ⟶ E.tupleDistinctScheme n)
    (r : T ⟶ E.tupleSymmetricCrossScheme m n)
    (ha : a ≫ E.tupleSymmetricMap m = r ≫ E.tupleSymmetricCrossLeft m n)
    (hb : b ≫ E.tupleSymmetricMap n = r ≫ E.tupleSymmetricCrossRight m n) :
    ∃ l : T ⟶ E.tupleCrossScheme m n,
      l ≫ E.tupleCrossLeft m n = a ∧ l ≫ E.tupleCrossRight m n = b := by
  have hp := E.tupleSymmetricCross_isPullback m n
  have h : prod.lift a b ≫ prod.map (E.tupleSymmetricMap m) (E.tupleSymmetricMap n) =
      r ≫ prod.lift (E.tupleSymmetricCrossLeft m n) (E.tupleSymmetricCrossRight m n) := by
    apply prod.hom_ext
    · simpa using ha
    · simpa using hb
  refine ⟨hp.lift (prod.lift a b) r h, ?_, ?_⟩
  · simpa using congrArg (· ≫ prod.fst) (hp.lift_fst (prod.lift a b) r h)
  · simpa using congrArg (· ≫ prod.snd) (hp.lift_fst (prod.lift a b) r h)

variable [IsClosedImmersion (prod.lift E.t E.s)]

/-- A symmetric cross arrow is determined by its two endpoints. -/
theorem tupleSymmetricCross_hom_ext (m n : ℕ) {T : Scheme.{u}}
    {a b : T ⟶ E.tupleSymmetricCrossScheme m n}
    (hl : a ≫ E.tupleSymmetricCrossLeft m n = b ≫ E.tupleSymmetricCrossLeft m n)
    (hr : a ≫ E.tupleSymmetricCrossRight m n = b ≫ E.tupleSymmetricCrossRight m n) :
    a = b := by
  apply (cancel_mono
    (prod.lift (E.tupleSymmetricCrossLeft m n) (E.tupleSymmetricCrossRight m n))).mp
  apply prod.hom_ext
  · simpa using hl
  · simpa using hr

/-- Existence of a symmetric cross arrow descends along a strong epimorphism.
Finite étale surjections are examples of the permitted covers. -/
theorem tupleSymmetricCross_exists_of_cover (m n : ℕ) {T V : Scheme.{u}}
    (q : V ⟶ T) [StrongEpi q]
    (a : T ⟶ E.tupleSymmetricScheme m) (b : T ⟶ E.tupleSymmetricScheme n)
    (r : V ⟶ E.tupleSymmetricCrossScheme m n)
    (hl : r ≫ E.tupleSymmetricCrossLeft m n = q ≫ a)
    (hr : r ≫ E.tupleSymmetricCrossRight m n = q ≫ b) :
    ∃ l : T ⟶ E.tupleSymmetricCrossScheme m n,
      l ≫ E.tupleSymmetricCrossLeft m n = a ∧
      l ≫ E.tupleSymmetricCrossRight m n = b := by
  let sq : CommSq r q
      (prod.lift (E.tupleSymmetricCrossLeft m n) (E.tupleSymmetricCrossRight m n))
      (prod.lift a b) := ⟨by
        apply prod.hom_ext
        · simpa using hl
        · simpa using hr⟩
  refine ⟨sq.lift, ?_, ?_⟩
  · simpa using congrArg (· ≫ prod.fst) sq.fac_right
  · simpa using congrArg (· ≫ prod.snd) sq.fac_right

/-- The identity arrow on an unordered distinct tuple. -/
def tupleSymmetricCrossUnit (n : ℕ) :
    E.tupleSymmetricScheme n ⟶ E.tupleSymmetricCrossScheme n n :=
  (E.tupleSymmetricCross_exists_of_cover n n (E.tupleSymmetricMap n) (𝟙 _) (𝟙 _)
    (E.tupleCrossUnit n ≫ E.tupleSymmetricCrossMap n n)
    (by simp) (by simp)).choose

@[reassoc (attr := simp)]
theorem tupleSymmetricCrossUnit_left (n : ℕ) :
    E.tupleSymmetricCrossUnit n ≫ E.tupleSymmetricCrossLeft n n = 𝟙 _ :=
  (E.tupleSymmetricCross_exists_of_cover n n (E.tupleSymmetricMap n) (𝟙 _) (𝟙 _)
    (E.tupleCrossUnit n ≫ E.tupleSymmetricCrossMap n n)
    (by simp) (by simp)).choose_spec.1

@[reassoc (attr := simp)]
theorem tupleSymmetricCrossUnit_right (n : ℕ) :
    E.tupleSymmetricCrossUnit n ≫ E.tupleSymmetricCrossRight n n = 𝟙 _ :=
  (E.tupleSymmetricCross_exists_of_cover n n (E.tupleSymmetricMap n) (𝟙 _) (𝟙 _)
    (E.tupleCrossUnit n ≫ E.tupleSymmetricCrossMap n n)
    (by simp) (by simp)).choose_spec.2

/-- Swap the endpoints of a symmetric cross arrow. -/
def tupleSymmetricCrossSwap (m n : ℕ) :
    E.tupleSymmetricCrossScheme m n ⟶ E.tupleSymmetricCrossScheme n m :=
  (E.tupleSymmetricCross_exists_of_cover n m (E.tupleSymmetricCrossMap m n)
    (E.tupleSymmetricCrossRight m n) (E.tupleSymmetricCrossLeft m n)
    (E.tupleCrossSwap m n ≫ E.tupleSymmetricCrossMap n m)
    (by simp) (by simp)).choose

@[reassoc (attr := simp)]
theorem tupleSymmetricCrossSwap_left (m n : ℕ) :
    E.tupleSymmetricCrossSwap m n ≫ E.tupleSymmetricCrossLeft n m =
      E.tupleSymmetricCrossRight m n :=
  (E.tupleSymmetricCross_exists_of_cover n m (E.tupleSymmetricCrossMap m n)
    (E.tupleSymmetricCrossRight m n) (E.tupleSymmetricCrossLeft m n)
    (E.tupleCrossSwap m n ≫ E.tupleSymmetricCrossMap n m)
    (by simp) (by simp)).choose_spec.1

@[reassoc (attr := simp)]
theorem tupleSymmetricCrossSwap_right (m n : ℕ) :
    E.tupleSymmetricCrossSwap m n ≫ E.tupleSymmetricCrossRight n m =
      E.tupleSymmetricCrossLeft m n :=
  (E.tupleSymmetricCross_exists_of_cover n m (E.tupleSymmetricCrossMap m n)
    (E.tupleSymmetricCrossRight m n) (E.tupleSymmetricCrossLeft m n)
    (E.tupleCrossSwap m n ≫ E.tupleSymmetricCrossMap n m)
    (by simp) (by simp)).choose_spec.2

@[reassoc (attr := simp)]
theorem tupleSymmetricCrossSwap_swap (m n : ℕ) :
    E.tupleSymmetricCrossSwap m n ≫ E.tupleSymmetricCrossSwap n m = 𝟙 _ := by
  apply E.tupleSymmetricCross_hom_ext m n <;> simp

/-- Transitivity between symmetric tuple schemes of three possibly different
lengths, on points valued in every test scheme. -/
theorem tupleSymmetricCross_transitive (m n k : ℕ) {T : Scheme.{u}}
    (r : T ⟶ E.tupleSymmetricCrossScheme m n)
    (s : T ⟶ E.tupleSymmetricCrossScheme n k)
    (hrs : r ≫ E.tupleSymmetricCrossRight m n = s ≫ E.tupleSymmetricCrossLeft n k) :
    ∃ l : T ⟶ E.tupleSymmetricCrossScheme m k,
      l ≫ E.tupleSymmetricCrossLeft m k = r ≫ E.tupleSymmetricCrossLeft m n ∧
      l ≫ E.tupleSymmetricCrossRight m k = s ≫ E.tupleSymmetricCrossRight n k := by
  let q0 := prod.map (prod.map (E.tupleSymmetricMap m) (E.tupleSymmetricMap n))
    (E.tupleSymmetricMap k)
  have : Etale q0 := schemeMorphismProperty_prod_map (@Etale) _ _
    (schemeMorphismProperty_prod_map (@Etale) _ _ inferInstance inferInstance) inferInstance
  have : Surjective q0 := schemeMorphismProperty_prod_map (@Surjective) _ _
    (schemeMorphismProperty_prod_map (@Surjective) _ _ inferInstance inferInstance) inferInstance
  let z := prod.lift
    (prod.lift (r ≫ E.tupleSymmetricCrossLeft m n) (r ≫ E.tupleSymmetricCrossRight m n))
    (s ≫ E.tupleSymmetricCrossRight n k)
  let q := pullback.fst z q0
  let x := pullback.snd z q0
  let a := x ≫ prod.fst ≫ prod.fst
  let b := x ≫ prod.fst ≫ prod.snd
  let c := x ≫ prod.snd
  have ha : a ≫ E.tupleSymmetricMap m = q ≫ r ≫ E.tupleSymmetricCrossLeft m n := by
    simpa [a, x, q, q0, z] using
      congrArg (fun f => f ≫ prod.fst ≫ prod.fst) (pullback.condition (f := z) (g := q0)).symm
  have hb : b ≫ E.tupleSymmetricMap n = q ≫ r ≫ E.tupleSymmetricCrossRight m n := by
    simpa [b, x, q, q0, z] using
      congrArg (fun f => f ≫ prod.fst ≫ prod.snd) (pullback.condition (f := z) (g := q0)).symm
  have hc : c ≫ E.tupleSymmetricMap k = q ≫ s ≫ E.tupleSymmetricCrossRight n k := by
    simpa [c, x, q, q0, z] using
      congrArg (fun f => f ≫ prod.snd) (pullback.condition (f := z) (g := q0)).symm
  obtain ⟨r', hr'l, hr'r⟩ := E.tupleCross_exists_of_symmetric m n a b (q ≫ r)
    (by simpa using ha) (by simpa using hb)
  obtain ⟨s', hs'l, hs'r⟩ := E.tupleCross_exists_of_symmetric n k b c (q ≫ s)
    (by simpa only [Category.assoc, hrs] using hb) (by simpa using hc)
  have hmid : (r' ≫ E.tupleCrossMap m n) ≫ E.s =
      (s' ≫ E.tupleCrossMap n k) ≫ E.t := by
    calc
      (r' ≫ E.tupleCrossMap m n) ≫ E.s =
          (r' ≫ E.tupleCrossRight m n) ≫ E.tupleDistinctProjection n 0 := by
            simp only [Category.assoc, E.tupleCrossMap_s]
      _ = b ≫ E.tupleDistinctProjection n 0 := by rw [hr'r]
      _ = (s' ≫ E.tupleCrossLeft n k) ≫ E.tupleDistinctProjection n 0 := by
            rw [hs'l]
      _ = (s' ≫ E.tupleCrossMap n k) ≫ E.t := by
            simp only [Category.assoc, E.tupleCrossMap_t]
  let w := E.compose (r' ≫ E.tupleCrossMap m n) (s' ≫ E.tupleCrossMap n k) hmid
  have hwt : w ≫ E.t = a ≫ E.tupleDistinctProjection m 0 := by
    simp only [w, E.compose_t, Category.assoc, E.tupleCrossMap_t]
    rw [← Category.assoc, hr'l]
  have hws : w ≫ E.s = c ≫ E.tupleDistinctProjection k 0 := by
    simp only [w, E.compose_s, Category.assoc, E.tupleCrossMap_s]
    rw [← Category.assoc, hs'r]
  exact E.tupleSymmetricCross_exists_of_cover m k q
    (r ≫ E.tupleSymmetricCrossLeft m n) (s ≫ E.tupleSymmetricCrossRight n k)
    (E.tupleCrossLift m k a c w hwt hws ≫ E.tupleSymmetricCrossMap m k)
    (by simpa using ha) (by simpa using hc)

end Affine

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
