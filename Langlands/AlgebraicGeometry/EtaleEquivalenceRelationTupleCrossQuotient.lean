import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTupleQuotient

/-! # Affine correspondences between symmetric tuple quotients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

variable (E : EtaleEquivalenceRelation.{u}) [IsSeparated E.s] (m n : ℕ)

/-- Ordered tuples in the same relation class, with separate distinctness in
each tuple. The two tuples may have coordinates in common. -/
abbrev tupleCrossScheme : Scheme.{u} :=
  pullback (pullback.snd (E.tupleDistinctProjection m 0) E.t ≫ E.s)
    (E.tupleDistinctProjection n 0)

def tupleCrossLeft : E.tupleCrossScheme m n ⟶ E.tupleDistinctScheme m :=
  pullback.fst _ _ ≫ pullback.fst _ _

def tupleCrossRight : E.tupleCrossScheme m n ⟶ E.tupleDistinctScheme n :=
  pullback.snd _ _

def tupleCrossMap : E.tupleCrossScheme m n ⟶ E.R :=
  pullback.fst _ _ ≫ pullback.snd _ _

@[reassoc]
theorem tupleCrossMap_t :
    E.tupleCrossMap m n ≫ E.t =
      E.tupleCrossLeft m n ≫ E.tupleDistinctProjection m 0 := by
  simp only [tupleCrossMap, tupleCrossLeft, Category.assoc]
  rw [← pullback.condition]

@[reassoc]
theorem tupleCrossMap_s :
    E.tupleCrossMap m n ≫ E.s =
      E.tupleCrossRight m n ≫ E.tupleDistinctProjection n 0 := by
  simpa only [tupleCrossMap, tupleCrossRight, Category.assoc] using
    (pullback.condition
      (f := pullback.snd (E.tupleDistinctProjection m 0) E.t ≫ E.s)
      (g := E.tupleDistinctProjection n 0))

/-- The universal lift of two ordered tuples with related zeroth coordinates. -/
def tupleCrossLift {T : Scheme.{u}} (a : T ⟶ E.tupleDistinctScheme m)
    (b : T ⟶ E.tupleDistinctScheme n) (r : T ⟶ E.R)
    (ht : r ≫ E.t = a ≫ E.tupleDistinctProjection m 0)
    (hs : r ≫ E.s = b ≫ E.tupleDistinctProjection n 0) :
    T ⟶ E.tupleCrossScheme m n :=
  pullback.lift (pullback.lift a r ht.symm) b
    (by rw [← Category.assoc, pullback.lift_snd, hs])

@[reassoc (attr := simp)]
theorem tupleCrossLift_left {T : Scheme.{u}} (a : T ⟶ E.tupleDistinctScheme m)
    (b : T ⟶ E.tupleDistinctScheme n) (r : T ⟶ E.R)
    (ht : r ≫ E.t = a ≫ E.tupleDistinctProjection m 0)
    (hs : r ≫ E.s = b ≫ E.tupleDistinctProjection n 0) :
    E.tupleCrossLift m n a b r ht hs ≫ E.tupleCrossLeft m n = a := by
  simp [tupleCrossLift, tupleCrossLeft]

@[reassoc (attr := simp)]
theorem tupleCrossLift_right {T : Scheme.{u}} (a : T ⟶ E.tupleDistinctScheme m)
    (b : T ⟶ E.tupleDistinctScheme n) (r : T ⟶ E.R)
    (ht : r ≫ E.t = a ≫ E.tupleDistinctProjection m 0)
    (hs : r ≫ E.s = b ≫ E.tupleDistinctProjection n 0) :
    E.tupleCrossLift m n a b r ht hs ≫ E.tupleCrossRight m n = b :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem tupleCrossLift_map {T : Scheme.{u}} (a : T ⟶ E.tupleDistinctScheme m)
    (b : T ⟶ E.tupleDistinctScheme n) (r : T ⟶ E.R)
    (ht : r ≫ E.t = a ≫ E.tupleDistinctProjection m 0)
    (hs : r ≫ E.s = b ≫ E.tupleDistinctProjection n 0) :
    E.tupleCrossLift m n a b r ht hs ≫ E.tupleCrossMap m n = r := by
  simp [tupleCrossLift, tupleCrossMap]

theorem tupleCross_hom_ext {T : Scheme.{u}} {a b : T ⟶ E.tupleCrossScheme m n}
    (hl : a ≫ E.tupleCrossLeft m n = b ≫ E.tupleCrossLeft m n)
    (hr : a ≫ E.tupleCrossRight m n = b ≫ E.tupleCrossRight m n) : a = b := by
  have hm : a ≫ E.tupleCrossMap m n = b ≫ E.tupleCrossMap m n := by
    apply E.hom_ext
    · rw [Category.assoc, Category.assoc, E.tupleCrossMap_t,
        ← Category.assoc, hl, Category.assoc]
    · rw [Category.assoc, Category.assoc, E.tupleCrossMap_s,
        ← Category.assoc, hr, Category.assoc]
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simpa only [tupleCrossLeft, Category.assoc] using hl
    · simpa only [tupleCrossMap, Category.assoc] using hm
  · exact hr

instance tupleCrossLeft_etale : Etale (E.tupleCrossLeft m n) := by
  let := E.etale_t
  let := E.etale_s
  dsimp only [tupleCrossLeft]
  infer_instance

instance tupleCrossRight_etale : Etale (E.tupleCrossRight m n) := by
  let := E.etale_t
  let := E.etale_s
  dsimp only [tupleCrossRight]
  infer_instance

instance tupleCrossScheme_isAffine [IsAffine E.U] [IsAffine E.R] :
    IsAffine (E.tupleCrossScheme m n) := by
  dsimp only [tupleCrossScheme]
  infer_instance

/-- Every coordinate on one tuple is related to every coordinate on the other. -/
theorem tupleCrossCoordinates_related (i : Fin (m + 1)) (j : Fin (n + 1)) :
    ∃ r : E.tupleCrossScheme m n ⟶ E.R,
      r ≫ E.t = E.tupleCrossLeft m n ≫ E.tupleDistinctProjection m i ∧
      r ≫ E.s = E.tupleCrossRight m n ≫ E.tupleDistinctProjection n j := by
  let l := E.tupleCrossLeft m n ≫ (E.tupleDistinctOpen m).ι ≫ E.tupleRelation m i 0
  let r := E.tupleCrossRight m n ≫ (E.tupleDistinctOpen n).ι ≫ E.tupleRelation n 0 j
  have hl : l ≫ E.s = E.tupleCrossMap m n ≫ E.t := by
    simp only [l, Category.assoc, E.tupleRelation_s]
    exact (E.tupleCrossMap_t m n).symm
  have hr : E.compose l (E.tupleCrossMap m n) hl ≫ E.s = r ≫ E.t := by
    rw [E.compose_s, E.tupleCrossMap_s]
    simp [r, tupleDistinctProjection]
  refine ⟨E.compose (E.compose l (E.tupleCrossMap m n) hl) r hr, ?_, ?_⟩
  · simp [l, tupleDistinctProjection]
  · simp [r, tupleDistinctProjection]

/-- Independent coordinate permutations on the two ordered tuples. -/
def tupleCrossReindex (a : Equiv.Perm (Fin (m + 1)))
    (b : Equiv.Perm (Fin (n + 1))) :
    E.tupleCrossScheme m n ⟶ E.tupleCrossScheme m n :=
  E.tupleCrossLift m n
    (E.tupleCrossLeft m n ≫ (E.tupleDistinctReindexIso a).hom)
    (E.tupleCrossRight m n ≫ (E.tupleDistinctReindexIso b).hom)
    (E.tupleCrossCoordinates_related m n (a 0) (b 0)).choose
    (by simpa using (E.tupleCrossCoordinates_related m n (a 0) (b 0)).choose_spec.1)
    (by simpa using (E.tupleCrossCoordinates_related m n (a 0) (b 0)).choose_spec.2)

@[reassoc (attr := simp)]
theorem tupleCrossReindex_left (a : Equiv.Perm (Fin (m + 1)))
    (b : Equiv.Perm (Fin (n + 1))) :
    E.tupleCrossReindex m n a b ≫ E.tupleCrossLeft m n =
      E.tupleCrossLeft m n ≫ (E.tupleDistinctReindexIso a).hom :=
  E.tupleCrossLift_left _ _ _ _ _ _ _

@[reassoc (attr := simp)]
theorem tupleCrossReindex_right (a : Equiv.Perm (Fin (m + 1)))
    (b : Equiv.Perm (Fin (n + 1))) :
    E.tupleCrossReindex m n a b ≫ E.tupleCrossRight m n =
      E.tupleCrossRight m n ≫ (E.tupleDistinctReindexIso b).hom :=
  E.tupleCrossLift_right _ _ _ _ _ _ _

/-- The isomorphism given by independent coordinate permutations. -/
def tupleCrossReindexIso (a : Equiv.Perm (Fin (m + 1)))
    (b : Equiv.Perm (Fin (n + 1))) :
    E.tupleCrossScheme m n ≅ E.tupleCrossScheme m n where
  hom := E.tupleCrossReindex m n a b
  inv := E.tupleCrossReindex m n a.symm b.symm
  hom_inv_id := by
    apply E.tupleCross_hom_ext m n
    · apply E.tupleDistinct_hom_ext m
      intro i
      simp
    · apply E.tupleDistinct_hom_ext n
      intro i
      simp
  inv_hom_id := by
    apply E.tupleCross_hom_ext m n
    · apply E.tupleDistinct_hom_ext m
      intro i
      simp
    · apply E.tupleDistinct_hom_ext n
      intro i
      simp

/-- The free product symmetric-group action on the ordered correspondence. -/
def tupleCrossPermutationAction :
    FiniteFreeSchemeAction
      (TuplePermutationGroup.{u} m × TuplePermutationGroup.{u} n)
      (E.tupleCrossScheme m n) where
  act g := E.tupleCrossReindexIso m n g.1.down g.2.down
  one := by
    apply E.tupleCross_hom_ext m n
    · apply E.tupleDistinct_hom_ext m
      intro i
      simp [tupleCrossReindexIso]
    · apply E.tupleDistinct_hom_ext n
      intro i
      simp [tupleCrossReindexIso]
  mul g h := by
    apply E.tupleCross_hom_ext m n
    · apply E.tupleDistinct_hom_ext m
      intro i
      simp [tupleCrossReindexIso]
    · apply E.tupleDistinct_hom_ext n
      intro i
      simp [tupleCrossReindexIso]
  free f := by
    intro g h hgh
    apply Prod.ext
    · apply (E.tuplePermutationAction m).free (f ≫ E.tupleCrossLeft m n)
      simpa [tuplePermutationAction, tupleCrossReindexIso] using
        congrArg (· ≫ E.tupleCrossLeft m n) hgh
    · apply (E.tuplePermutationAction n).free (f ≫ E.tupleCrossRight m n)
      simpa [tuplePermutationAction, tupleCrossReindexIso] using
        congrArg (· ≫ E.tupleCrossRight m n) hgh

section Affine

variable [IsAffine E.U] [IsAffine E.R]

/-- The affine quotient of the ordered correspondence by both symmetric groups. -/
def tupleCrossQuotient : (E.tupleCrossPermutationAction m n).AffineQuotient :=
  (E.tupleCrossPermutationAction m n).quotient

abbrev tupleSymmetricCrossScheme : Scheme.{u} := (E.tupleCrossQuotient m n).scheme

abbrev tupleSymmetricCrossMap :
    E.tupleCrossScheme m n ⟶ E.tupleSymmetricCrossScheme m n :=
  (E.tupleCrossQuotient m n).map

instance tupleSymmetricCrossScheme_isAffine :
    IsAffine (E.tupleSymmetricCrossScheme m n) :=
  (E.tupleCrossQuotient m n).isAffine

instance tupleSymmetricCrossMap_isFinite : IsFinite (E.tupleSymmetricCrossMap m n) :=
  (E.tupleCrossQuotient m n).finite

instance tupleSymmetricCrossMap_etale : Etale (E.tupleSymmetricCrossMap m n) :=
  (E.tupleCrossQuotient m n).etale

instance tupleSymmetricCrossMap_surjective : Surjective (E.tupleSymmetricCrossMap m n) :=
  (E.tupleCrossQuotient m n).surjective

/-- The descended first endpoint, valued in unordered tuples. -/
def tupleSymmetricCrossLeft :
    E.tupleSymmetricCrossScheme m n ⟶ E.tupleSymmetricScheme m :=
  (E.tupleCrossQuotient m n).desc
    (E.tupleCrossLeft m n ≫ E.tupleSymmetricMap m) (by
      intro g
      simp [tupleCrossPermutationAction, tupleCrossReindexIso])

/-- The descended second endpoint, valued in unordered tuples. -/
def tupleSymmetricCrossRight :
    E.tupleSymmetricCrossScheme m n ⟶ E.tupleSymmetricScheme n :=
  (E.tupleCrossQuotient m n).desc
    (E.tupleCrossRight m n ≫ E.tupleSymmetricMap n) (by
      intro g
      simp [tupleCrossPermutationAction, tupleCrossReindexIso])

@[reassoc (attr := simp)]
theorem tupleSymmetricCrossMap_left :
    E.tupleSymmetricCrossMap m n ≫ E.tupleSymmetricCrossLeft m n =
      E.tupleCrossLeft m n ≫ E.tupleSymmetricMap m :=
  (E.tupleCrossQuotient m n).map_desc _ _

@[reassoc (attr := simp)]
theorem tupleSymmetricCrossMap_right :
    E.tupleSymmetricCrossMap m n ≫ E.tupleSymmetricCrossRight m n =
      E.tupleCrossRight m n ≫ E.tupleSymmetricMap n :=
  (E.tupleCrossQuotient m n).map_desc _ _

end Affine

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
