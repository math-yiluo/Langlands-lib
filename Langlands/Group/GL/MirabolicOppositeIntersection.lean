import Langlands.Group.GL.Mirabolic
import Langlands.Group.GL.OppositeBlocks

/-! # The binary opposite-parabolic intersection inside the mirabolic group -/

namespace Langlands.GeneralLinear

universe u

namespace BlockShape

/-- Two positive consecutive blocks, with no coordinate choices supplied by the caller. -/
def binary (a c : ℕ) (ha : 0 < a) (hc : 0 < c) : BlockShape (a + c) where
  length := 2
  size := Fin.cases a (fun _ => c)
  positive := Fin.cases ha (fun _ => hc)
  sum_eq := by simp [Fin.sum_univ_succ]

@[simp] theorem binary_length (a c : ℕ) (ha : 0 < a) (hc : 0 < c) :
    (binary a c ha hc).length = 2 := rfl

@[simp] theorem binary_size_zero (a c : ℕ) (ha : 0 < a) (hc : 0 < c) :
    (binary a c ha hc).size (0 : Fin 2) = a := rfl

@[simp] theorem binary_size_one (a c : ℕ) (ha : 0 < a) (hc : 0 < c) :
    (binary a c ha hc).size (1 : Fin 2) = c := rfl

@[simp] theorem binary_index_zero (a c : ℕ) (ha : 0 < a) (hc : 0 < c)
    (i : Fin a) :
    (binary a c ha hc).index (0 : Fin 2) i = Fin.castAdd c i := by
  apply Fin.ext
  simp only [index, indexEquiv, Function.Embedding.coeFn_mk, Equiv.trans_apply,
    finCongr_apply, Fin.val_cast, finSigmaFinEquiv_apply]
  simp [binary]

@[simp] theorem binary_index_one (a c : ℕ) (ha : 0 < a) (hc : 0 < c)
    (j : Fin c) :
    (binary a c ha hc).index (1 : Fin 2) j = Fin.natAdd a j := by
  apply Fin.ext
  simp only [index, indexEquiv, Function.Embedding.coeFn_mk, Equiv.trans_apply,
    finCongr_apply, Fin.val_cast, finSigmaFinEquiv_apply]
  simp [binary]

end BlockShape

namespace MirabolicOppositeIntersection

variable (a b : ℕ) (ha : 0 < a)

/-- The binary shape of ranks `a` and `b+1`. -/
abbrev shape : BlockShape (a + b + 1) :=
  BlockShape.binary a (b + 1) ha (Nat.succ_pos b)

/-- The last coordinate of the tail is the last ambient coordinate. -/
@[simp] theorem tail_last :
    Fin.natAdd a (Fin.last b) = Fin.last (a + b) := by
  apply Fin.ext
  rfl

variable (R : Type u) [CommRing R]

/-- The actual opposite-parabolic intersection, inside the actual mirabolic group. -/
def intersection : Subgroup (mirabolic (a + b) R) :=
  ((shape a b ha).oppositeParabolic R).comap (mirabolic (a + b) R).subtype

/-- Only the head-to-tail rectangle is constrained beyond the mirabolic row. -/
theorem mem_intersection_iff (g : mirabolic (a + b) R) :
    g ∈ intersection a b ha R ↔
      ∀ (i : Fin a) (j : Fin (b + 1)),
        g.val (Fin.castAdd (b + 1) i) (Fin.natAdd a j) = 0 := by
  change g.val ∈ (shape a b ha).oppositeParabolic R ↔ _
  rw [BlockShape.mem_oppositeParabolic_iff]
  constructor
  · intro h i j
    simpa only [shape, BlockShape.binary_index_zero, BlockShape.binary_index_one] using
      h (0 : Fin 2) (1 : Fin 2) i j (show (0 : Fin 2) < 1 from by decide)
  · intro h i j x y hij
    fin_cases i <;> fin_cases j
    · exact False.elim (lt_irrefl _ hij)
    · change g.val ((shape a b ha).index (0 : Fin 2) x)
        ((shape a b ha).index (1 : Fin 2) y) = 0
      exact (congrArg₂ g.val
        (BlockShape.binary_index_zero a (b + 1) ha _ x)
        (BlockShape.binary_index_one a (b + 1) ha _ y)).trans (h x y)
    · simp at hij
    · exact False.elim (lt_irrefl _ hij)

/-- The original last-row certificate is retained. -/
theorem last_row (g : intersection a b ha R) (j : Fin (a + b + 1)) :
    g.val.val (Fin.last (a + b)) j = if j = Fin.last (a + b) then 1 else 0 :=
  g.val.property j

/-- All entries from the head rows to the tail columns vanish. -/
theorem head_tail_zero (g : intersection a b ha R) (i : Fin a) (j : Fin (b + 1)) :
    g.val.val (Fin.castAdd (b + 1) i) (Fin.natAdd a j) = 0 :=
  (mem_intersection_iff a b ha R g.val).mp g.property i j

/-- Forget only the mirabolic certificate, retaining the same opposite-parabolic matrix. -/
def toOpposite : intersection a b ha R →* (shape a b ha).oppositeParabolic R where
  toFun g := ⟨g.val.val, g.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem toOpposite_val (g : intersection a b ha R) :
    (toOpposite a b ha R g).val = g.val.val := rfl

/-- The published actual invertible-block projection restricted to this intersection. -/
def diagonalProjection : intersection a b ha R →* (shape a b ha).Levi R :=
  ((shape a b ha).oppositeLeviProjection R).comp (toOpposite a b ha R)

@[simp] theorem diagonalProjection_head_entry (g : intersection a b ha R) (i j : Fin a) :
    diagonalProjection a b ha R g (0 : Fin 2) i j =
      g.val.val (Fin.castAdd (b + 1) i) (Fin.castAdd (b + 1) j) := by
  exact congrArg₂ g.val.val
    (BlockShape.binary_index_zero a (b + 1) ha _ i)
    (BlockShape.binary_index_zero a (b + 1) ha _ j)

@[simp] theorem diagonalProjection_tail_entry (g : intersection a b ha R)
    (i j : Fin (b + 1)) :
    diagonalProjection a b ha R g (1 : Fin 2) i j =
      g.val.val (Fin.natAdd a i) (Fin.natAdd a j) := by
  exact congrArg₂ g.val.val
    (BlockShape.binary_index_one a (b + 1) ha _ i)
    (BlockShape.binary_index_one a (b + 1) ha _ j)

/-- The extracted invertible tail block satisfies the actual mirabolic row equation. -/
theorem diagonalProjection_tail_mem (g : intersection a b ha R) :
    diagonalProjection a b ha R g (1 : Fin 2) ∈ mirabolic b R := by
  intro j
  rw [diagonalProjection_tail_entry]
  simpa only [← tail_last a b, Fin.natAdd_inj] using
    last_row a b ha R g (Fin.natAdd a j)

/-- The split diagonal projection, with its tail valued in the actual mirabolic subgroup. -/
def projection :
    intersection a b ha R →* (Langlands.GeneralLinear a R × mirabolic b R) where
  toFun g := (diagonalProjection a b ha R g (0 : Fin 2),
    ⟨diagonalProjection a b ha R g (1 : Fin 2), diagonalProjection_tail_mem a b ha R g⟩)
  map_one' := by
    apply Prod.ext
    · exact congrFun (diagonalProjection a b ha R).map_one (0 : Fin 2)
    · exact Subtype.ext (congrFun (diagonalProjection a b ha R).map_one (1 : Fin 2))
  map_mul' g h := by
    apply Prod.ext
    · exact congrFun ((diagonalProjection a b ha R).map_mul g h) (0 : Fin 2)
    · exact Subtype.ext (congrFun ((diagonalProjection a b ha R).map_mul g h) (1 : Fin 2))

@[simp] theorem projection_head_entry (g : intersection a b ha R) (i j : Fin a) :
    (projection a b ha R g).1 i j =
      g.val.val (Fin.castAdd (b + 1) i) (Fin.castAdd (b + 1) j) :=
  diagonalProjection_head_entry a b ha R g i j

@[simp] theorem projection_tail_entry (g : intersection a b ha R) (i j : Fin (b + 1)) :
    (projection a b ha R g).2.val i j = g.val.val (Fin.natAdd a i) (Fin.natAdd a j) :=
  diagonalProjection_tail_entry a b ha R g i j

/-- The two supplied matrices as the actual dependent Levi product. -/
def leviLift : (Langlands.GeneralLinear a R × mirabolic b R) →* (shape a b ha).Levi R where
  toFun m := Fin.cases m.1 (fun _ => m.2.val)
  map_one' := by funext i; fin_cases i <;> rfl
  map_mul' _ _ := by funext i; fin_cases i <;> rfl

/-- The common ambient block diagonal embedding. -/
def blockDiagonal :
    (Langlands.GeneralLinear a R × mirabolic b R) →* Langlands.GeneralLinear (a + b + 1) R :=
  ((shape a b ha).leviEmbedding R).comp (leviLift a b ha R)

@[simp] theorem blockDiagonal_head_head
    (m : Langlands.GeneralLinear a R × mirabolic b R) (i j : Fin a) :
    blockDiagonal a b ha R m (Fin.castAdd (b + 1) i) (Fin.castAdd (b + 1) j) = m.1 i j := by
  rw [← BlockShape.binary_index_zero a (b + 1) ha (Nat.succ_pos b) i,
    ← BlockShape.binary_index_zero a (b + 1) ha (Nat.succ_pos b) j]
  exact (shape a b ha).leviEmbedding_apply_same R (leviLift a b ha R m) (0 : Fin 2) i j

@[simp] theorem blockDiagonal_tail_tail
    (m : Langlands.GeneralLinear a R × mirabolic b R) (i j : Fin (b + 1)) :
    blockDiagonal a b ha R m (Fin.natAdd a i) (Fin.natAdd a j) = m.2.val i j := by
  rw [← BlockShape.binary_index_one a (b + 1) ha (Nat.succ_pos b) i,
    ← BlockShape.binary_index_one a (b + 1) ha (Nat.succ_pos b) j]
  exact (shape a b ha).leviEmbedding_apply_same R (leviLift a b ha R m) (1 : Fin 2) i j

@[simp] theorem blockDiagonal_head_tail
    (m : Langlands.GeneralLinear a R × mirabolic b R) (i : Fin a) (j : Fin (b + 1)) :
    blockDiagonal a b ha R m (Fin.castAdd (b + 1) i) (Fin.natAdd a j) = 0 := by
  rw [← BlockShape.binary_index_zero a (b + 1) ha (Nat.succ_pos b) i,
    ← BlockShape.binary_index_one a (b + 1) ha (Nat.succ_pos b) j]
  exact (shape a b ha).leviEmbedding_apply_ne R (leviLift a b ha R m)
    (i := (0 : Fin 2)) (j := (1 : Fin 2)) i j (show (0 : Fin 2) ≠ 1 from by decide)

@[simp] theorem blockDiagonal_tail_head
    (m : Langlands.GeneralLinear a R × mirabolic b R) (i : Fin (b + 1)) (j : Fin a) :
    blockDiagonal a b ha R m (Fin.natAdd a i) (Fin.castAdd (b + 1) j) = 0 := by
  rw [← BlockShape.binary_index_one a (b + 1) ha (Nat.succ_pos b) i,
    ← BlockShape.binary_index_zero a (b + 1) ha (Nat.succ_pos b) j]
  exact (shape a b ha).leviEmbedding_apply_ne R (leviLift a b ha R m)
    (i := (1 : Fin 2)) (j := (0 : Fin 2)) i j (show (1 : Fin 2) ≠ 0 from by decide)

theorem blockDiagonal_mem_mirabolic (m : Langlands.GeneralLinear a R × mirabolic b R) :
    blockDiagonal a b ha R m ∈ mirabolic (a + b) R := by
  intro j
  refine Fin.addCases (m := a) (n := b + 1) (fun i => ?_) (fun k => ?_) j
  · rw [← tail_last a b, blockDiagonal_tail_head]
    have hne : Fin.castAdd (b + 1) i ≠ Fin.natAdd a (Fin.last b) := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.val_last] at hv
      have := i.isLt
      omega
    simp only [hne, ↓reduceIte]
  · rw [← tail_last a b, blockDiagonal_tail_tail]
    simpa only [Fin.natAdd_inj] using m.2.property k

/-- The common diagonal embedding, retaining its proved mirabolic membership. -/
def mirabolicEmbedding :
    (Langlands.GeneralLinear a R × mirabolic b R) →* mirabolic (a + b) R :=
  (blockDiagonal a b ha R).codRestrict _ (blockDiagonal_mem_mirabolic a b ha R)

/-- The homomorphic diagonal section inside the actual intersection. -/
def diagonalSection :
    (Langlands.GeneralLinear a R × mirabolic b R) →* intersection a b ha R :=
  (mirabolicEmbedding a b ha R).codRestrict _ fun m =>
    ((shape a b ha).oppositeLeviInParabolic R (leviLift a b ha R m)).property

/-- The section preserves exactly the common block diagonal ambient matrix. -/
@[simp] theorem diagonalSection_val (m : Langlands.GeneralLinear a R × mirabolic b R) :
    (diagonalSection a b ha R m).val.val = blockDiagonal a b ha R m := rfl

/-- The common diagonal section is a right inverse of the restricted projection. -/
@[simp] theorem projection_diagonalSection
    (m : Langlands.GeneralLinear a R × mirabolic b R) :
    projection a b ha R (diagonalSection a b ha R m) = m := by
  have h : diagonalProjection a b ha R (diagonalSection a b ha R m) =
      leviLift a b ha R m :=
    (shape a b ha).oppositeLeviProjection_section R (leviLift a b ha R m)
  apply Prod.ext
  · exact congrFun h (0 : Fin 2)
  · exact Subtype.ext (congrFun h (1 : Fin 2))

theorem projection_surjective : Function.Surjective (projection a b ha R) :=
  fun m => ⟨diagonalSection a b ha R m, projection_diagonalSection a b ha R m⟩

section Topology

variable [TopologicalSpace R] [IsTopologicalRing R]

omit [IsTopologicalRing R] in
theorem continuous_toOpposite : Continuous (toOpposite a b ha R) :=
  (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

theorem continuous_diagonalProjection : Continuous (diagonalProjection a b ha R) :=
  ((shape a b ha).oppositeLeviProjectionContinuous R).continuous.comp
    (continuous_toOpposite a b ha R)

theorem continuous_projection : Continuous (projection a b ha R) :=
  ((continuous_apply (0 : Fin 2)).comp (continuous_diagonalProjection a b ha R)).prodMk
    (((continuous_apply (1 : Fin 2)).comp (continuous_diagonalProjection a b ha R)).subtype_mk _)

/-- The same projection as a continuous monoid homomorphism. -/
def projectionContinuous :
    ContinuousMonoidHom (intersection a b ha R) (Langlands.GeneralLinear a R × mirabolic b R) where
  toMonoidHom := projection a b ha R
  continuous_toFun := continuous_projection a b ha R

omit [IsTopologicalRing R] in
theorem continuous_leviLift : Continuous (leviLift a b ha R) := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_fst
  · change Continuous (fun m : Langlands.GeneralLinear a R × mirabolic b R => m.2.val)
    exact continuous_subtype_val.comp continuous_snd

omit [IsTopologicalRing R] in
theorem continuous_blockDiagonal : Continuous (blockDiagonal a b ha R) :=
  ((shape a b ha).leviEmbeddingContinuous R).continuous.comp (continuous_leviLift a b ha R)

theorem continuous_diagonalSection : Continuous (diagonalSection a b ha R) :=
  ((continuous_blockDiagonal a b ha R).subtype_mk _).subtype_mk _

/-- The same common diagonal section as a continuous monoid homomorphism. -/
def diagonalSectionContinuous :
    ContinuousMonoidHom (Langlands.GeneralLinear a R × mirabolic b R) (intersection a b ha R) where
  toMonoidHom := diagonalSection a b ha R
  continuous_toFun := continuous_diagonalSection a b ha R

variable [T2Space R]

omit [IsTopologicalRing R] in
/-- The intersection is closed in the mirabolic group with its inherited topology. -/
theorem isClosed : IsClosed (intersection a b ha R : Set (mirabolic (a + b) R)) :=
  ((shape a b ha).isClosed_oppositeParabolic R).preimage continuous_subtype_val

omit [IsTopologicalRing R] in
/-- Closed subgroup inclusions transfer local compactness from the ambient matrix group. -/
theorem locallyCompactSpace [LocallyCompactSpace (Langlands.GeneralLinear (a + b + 1) R)] :
    LocallyCompactSpace (intersection a b ha R) := by
  have := Mirabolic.locallyCompactSpace (F := R) (n := a + b)
  exact (isClosed a b ha R).locallyCompactSpace

end Topology
end MirabolicOppositeIntersection
end Langlands.GeneralLinear
