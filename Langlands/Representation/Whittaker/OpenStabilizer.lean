import Langlands.Group.GL.ReverseBlocks
import Langlands.Group.GL.SingletonBlocks
import Langlands.Group.GL.TriangularParabolic
import Langlands.Representation.Geometric.WeylMinimalRepresentativeProof
import Langlands.Representation.Geometric.ClosedSubgroupDefinitions
import Langlands.Representation.Whittaker.EntrywiseCharacter

noncomputable section

namespace Langlands.Whittaker

open GeneralLinear Geometric
open scoped BigOperators

universe u
variable {n : ℕ} (B : BlockShape n) (K : Type u) [Field K]

/-- The actual stabilizer at the block-reversal representative. -/
abbrev openStabilizer :=
  orbitStabilizer (B.parabolic K) (upperUnipotent n K) (B.reverseMatrix K)⁻¹

private abbrev inducingMap :=
  stabilizerToInducing (B.parabolic K) (upperUnipotent n K) (B.reverseMatrix K)⁻¹

private theorem inducingMap_entry (q : openStabilizer B K)
    (i j : Fin B.length) (a : Fin (B.size i.rev)) (b : Fin (B.size j.rev)) :
    (inducingMap B K q).val (B.index i.rev a) (B.index j.rev b) =
      q.val.val (B.reverse.index i a) (B.reverse.index j b) := by
  change MulAut.conj ((B.reverseMatrix K)⁻¹)⁻¹ q.val.val _ _ = _
  rw [inv_inv, B.reverseMatrix_conjugate_entry]

private theorem inverseConjugate_entry (g : Langlands.GeneralLinear n K)
    (i j : Fin B.length) (a : Fin (B.size i.rev)) (b : Fin (B.size j.rev)) :
    MulAut.conj (B.reverseMatrix K)⁻¹ g
      (B.reverse.index i a) (B.reverse.index j b) =
      g (B.index i.rev a) (B.index j.rev b) := by
  have h := B.reverseMatrix_conjugate_entry K
    (MulAut.conj (B.reverseMatrix K)⁻¹ g) i j a b
  simpa [MulAut.conj_apply, mul_assoc] using h.symm

private theorem inducingMap_offBlock (q : openStabilizer B K)
    {i j : Fin B.length} (a : Fin (B.size i)) (b : Fin (B.size j)) (hij : i ≠ j) :
    (inducingMap B K q).val (B.index i a) (B.index j b) = 0 := by
  rcases lt_or_gt_of_ne hij with hij | hji
  · obtain ⟨i, rfl⟩ := Fin.rev_surjective i
    obtain ⟨j, rfl⟩ := Fin.rev_surjective j
    rw [inducingMap_entry]
    exact q.val.property.1 (B.reverse.index_lt_index_of_block_lt
      (Fin.rev_lt_rev.mp hij) b a)
  · exact (B.mem_parabolic_iff K _).mp (inducingMap B K q).property i j a b hji

private theorem projection_mem (q : openStabilizer B K) (i : Fin B.length) :
    B.leviProjection K (inducingMap B K q) i ∈ upperUnipotent (B.size i) K := by
  obtain ⟨i, rfl⟩ := Fin.rev_surjective i
  constructor
  · intro a b hba
    change (inducingMap B K q).val (B.index i.rev a) (B.index i.rev b) = 0
    rw [inducingMap_entry]
    exact q.val.property.1 (index_strictMono B.reverse i hba)
  · intro a
    change (inducingMap B K q).val (B.index i.rev a) (B.index i.rev a) = 1
    rw [inducingMap_entry]
    exact q.val.property.2 _

private def forward : openStabilizer B K →* (∀ i, upperUnipotent (B.size i) K) where
  toFun q i := ⟨B.leviProjection K (inducingMap B K q) i, projection_mem B K q i⟩
  map_one' := by
    funext i
    apply Subtype.ext
    exact congrFun (map_one ((B.leviProjection K).comp (inducingMap B K))) i
  map_mul' q r := by
    funext i
    apply Subtype.ext
    exact congrFun (map_mul ((B.leviProjection K).comp (inducingMap B K)) q r) i

private theorem embedding_projection (q : openStabilizer B K) :
    B.leviEmbedding K (B.leviProjection K (inducingMap B K q)) =
      (inducingMap B K q).val := by
  apply Matrix.GeneralLinearGroup.ext
  intro x y
  obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective x
  obtain ⟨⟨j, b⟩, rfl⟩ := B.indexEquiv.surjective y
  change B.leviEmbedding K _ (B.index i a) (B.index j b) =
    (inducingMap B K q).val (B.index i a) (B.index j b)
  by_cases hij : i = j
  · subst j
    rw [B.leviEmbedding_apply_same, B.leviProjection_apply]
  · rw [B.leviEmbedding_apply_ne K _ a b hij, inducingMap_offBlock B K q a b hij]

private def inverseMatrix (m : ∀ i, upperUnipotent (B.size i) K) :
    Langlands.GeneralLinear n K :=
  MulAut.conj (B.reverseMatrix K)⁻¹ (B.leviEmbedding K (fun i => (m i).val))

private theorem inverseMatrix_mem (m : ∀ i, upperUnipotent (B.size i) K) :
    inverseMatrix B K m ∈ upperUnipotent n K := by
  constructor
  · intro x y hyx
    obtain ⟨⟨i, a⟩, rfl⟩ := B.reverse.indexEquiv.surjective x
    obtain ⟨⟨j, b⟩, rfl⟩ := B.reverse.indexEquiv.surjective y
    change Fin B.length at i j
    change Fin (B.size i.rev) at a
    change Fin (B.size j.rev) at b
    change inverseMatrix B K m (B.reverse.index i a) (B.reverse.index j b) = 0
    rw [inverseMatrix, inverseConjugate_entry B K _ i j a b]
    by_cases hij : i = j
    · subst j
      rw [B.leviEmbedding_apply_same K (fun k => (m k).val) i.rev a b]
      exact (m i.rev).property.1 ((index_strictMono B.reverse i).lt_iff_lt.mp hyx)
    · exact B.leviEmbedding_apply_ne K _ a b (fun h => hij (Fin.rev_injective h))
  · intro x
    obtain ⟨⟨i, a⟩, rfl⟩ := B.reverse.indexEquiv.surjective x
    change Fin B.length at i
    change Fin (B.size i.rev) at a
    change inverseMatrix B K m (B.reverse.index i a) (B.reverse.index i a) = 1
    rw [inverseMatrix, inverseConjugate_entry B K _ i i a a,
      B.leviEmbedding_apply_same K (fun k => (m k).val) i.rev a a]
    exact (m i.rev).property.2 a

private def backward (m : ∀ i, upperUnipotent (B.size i) K) : openStabilizer B K :=
  ⟨⟨inverseMatrix B K m, inverseMatrix_mem B K m⟩, by
    change MulAut.conj ((B.reverseMatrix K)⁻¹)⁻¹ (inverseMatrix B K m) ∈ B.parabolic K
    simpa [inverseMatrix, MulAut.conj_apply, mul_assoc] using
      (B.leviInParabolic K (fun i => (m i).val)).property⟩

private theorem inducingMap_backward (m : ∀ i, upperUnipotent (B.size i) K) :
    inducingMap B K (backward B K m) = B.leviInParabolic K (fun i => (m i).val) := by
  apply Subtype.ext
  change MulAut.conj ((B.reverseMatrix K)⁻¹)⁻¹ (inverseMatrix B K m) = _
  simp [inverseMatrix, MulAut.conj_apply, mul_assoc]

/-- Diagonal blocks of the conjugated matrix identify the actual stabilizer with
its ordered product of upper unipotent block groups. -/
def openStabilizerEquiv : openStabilizer B K ≃* (∀ i, upperUnipotent (B.size i) K) where
  toFun := forward B K
  invFun := backward B K
  left_inv q := by
    apply Subtype.ext
    apply Subtype.ext
    change MulAut.conj (B.reverseMatrix K)⁻¹
      (B.leviEmbedding K (B.leviProjection K (inducingMap B K q))) = q.val.val
    rw [embedding_projection]
    simp [inducingMap, stabilizerToInducing, MulAut.conj_apply, mul_assoc]
  right_inv m := by
    funext i
    apply Subtype.ext
    change B.leviProjection K (inducingMap B K (backward B K m)) i = (m i).val
    rw [inducingMap_backward, B.leviProjection_section]
  map_mul' := (forward B K).map_mul

/-- The forward map is exactly the Levi projection of the conjugated element. -/
@[simp] theorem openStabilizerEquiv_apply_val (q : openStabilizer B K)
    (i : Fin B.length) :
    (openStabilizerEquiv B K q i).val =
      B.leviProjection K
        (stabilizerToInducing (B.parabolic K) (upperUnipotent n K)
          (B.reverseMatrix K)⁻¹ q) i := rfl

/-- The inverse is the conjugated block diagonal matrix, with no internal reversal. -/
@[simp] theorem openStabilizerEquiv_symm_apply_val
    (m : ∀ i, upperUnipotent (B.size i) K) :
    ((openStabilizerEquiv B K).symm m).val.val =
      (B.reverseMatrix K)⁻¹ * B.leviEmbedding K (fun i => (m i).val) *
        B.reverseMatrix K := by
  change MulAut.conj (B.reverseMatrix K)⁻¹ _ = _
  simp only [MulAut.conj_apply, inv_inv]

/-- Equality of the whole Levi family, in the original order of the blocks. -/
theorem openStabilizerEquiv_leviProjection (q : openStabilizer B K) :
    B.leviProjection K
      (stabilizerToInducing (B.parabolic K) (upperUnipotent n K)
        (B.reverseMatrix K)⁻¹ q) =
      fun i => (openStabilizerEquiv B K q i).val := rfl

private theorem index_adjacent_iff (i : Fin B.length) (a b : Fin (B.size i)) :
    (B.index i b).val = (B.index i a).val + 1 ↔ b.val = a.val + 1 := by
  simp only [BlockShape.index, Function.Embedding.coeFn_mk, BlockShape.indexEquiv,
    Equiv.trans_apply, finCongr_apply, Fin.val_cast, finSigmaFinEquiv_apply]
  omega

private theorem block_entrywiseProduct (ψ : AddChar K ℂ)
    (g : Langlands.GeneralLinear n K)
    (hg : ∀ (i j : Fin B.length) (a : Fin (B.size i)) (b : Fin (B.size j)),
      i ≠ j → g (B.index i a) (B.index j b) = 0) :
    (∏ x : Fin n, ∏ y : Fin n, if y.val = x.val + 1 then ψ (g x y) else 1) =
      ∏ i : Fin B.length, ∏ a : Fin (B.size i), ∏ b : Fin (B.size i),
        if b.val = a.val + 1 then ψ (g (B.index i a) (B.index i b)) else 1 := by
  classical
  let f : Fin n → Fin n → ℂ :=
    fun x y => if y.val = x.val + 1 then ψ (g x y) else 1
  change (∏ x, ∏ y, f x y) = _
  calc
    (∏ x, ∏ y, f x y) =
        ∏ s : B.Index, ∏ y : Fin n, f (B.indexEquiv s) y :=
      (Equiv.prod_comp B.indexEquiv (fun x => ∏ y, f x y)).symm
    _ = ∏ s : B.Index, ∏ t : B.Index, f (B.indexEquiv s) (B.indexEquiv t) := by
      apply Finset.prod_congr rfl
      intro s _
      exact (Equiv.prod_comp B.indexEquiv (f (B.indexEquiv s))).symm
    _ = ∏ i : Fin B.length, ∏ a : Fin (B.size i),
        ∏ j : Fin B.length, ∏ b : Fin (B.size j), f (B.index i a) (B.index j b) := by
      simp only [Fintype.prod_sigma]
      rfl
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      apply Finset.prod_congr rfl
      intro a _
      rw [Finset.prod_eq_single i]
      · apply Finset.prod_congr rfl
        intro b _
        simp only [f, index_adjacent_iff]
      · intro j _ hji
        apply Finset.prod_eq_one
        intro b _
        simp [f, hg i j a b (Ne.symm hji)]
      · simp

/-- The raw additive character restricts to exactly the product of the characters
of the original ordered blocks, without character inversion or internal reversal. -/
theorem openStabilizerEquiv_character (ψ : AddChar K ℂ) (q : openStabilizer B K) :
    entrywiseCharacter ψ n q.val =
      ∏ i, entrywiseCharacter ψ (B.size i) (openStabilizerEquiv B K q i) := by
  classical
  have hoff (i j : Fin B.reverse.length) (a : Fin (B.reverse.size i))
      (b : Fin (B.reverse.size j)) (hij : i ≠ j) :
      q.val.val (B.reverse.index i a) (B.reverse.index j b) = 0 := by
    rw [← inducingMap_entry B K q i j a b]
    exact inducingMap_offBlock B K q a b (fun h => hij (Fin.rev_injective h))
  apply Units.ext
  rw [Units.coe_prod, entrywiseCharacter_apply, block_entrywiseProduct B.reverse K ψ _ hoff]
  calc
    (∏ i : Fin B.reverse.length, ∏ a : Fin (B.reverse.size i),
        ∏ b : Fin (B.reverse.size i),
        if b.val = a.val + 1 then
          ψ (q.val.val (B.reverse.index i a) (B.reverse.index i b)) else 1) =
        ∏ i : Fin B.length,
          (entrywiseCharacter ψ (B.size i.rev) (openStabilizerEquiv B K q i.rev) : ℂ) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [entrywiseCharacter_apply]
      apply Finset.prod_congr rfl
      intro a _
      apply Finset.prod_congr rfl
      intro b _
      congr 1
      congr 1
      change q.val.val (B.reverse.index i a) (B.reverse.index i b) =
        (inducingMap B K q).val (B.index i.rev a) (B.index i.rev b)
      exact (inducingMap_entry B K q i i a b).symm
    _ = _ := Equiv.prod_comp Fin.revPerm
      (fun i => (entrywiseCharacter ψ (B.size i) (openStabilizerEquiv B K q i) : ℂ))

/-- The block-reversal representative is intrinsically minimal for the singleton
target shape. This assertion does not assert openness of the orbit. -/
theorem reversePermutation_isMinimalRepresentative :
    IsMinimalRepresentative B (BlockShape.singletons n) B.reversePermutation.symm := by
  constructor
  · intro i
    obtain ⟨i, rfl⟩ := Fin.rev_surjective i
    intro a b hab
    simp only [B.reversePermutation_symm_index]
    exact index_strictMono B.reverse i hab
  · intro j a b hab
    have he : a = b := Subsingleton.elim _ _
    exact False.elim ((ne_of_lt hab) he)

section Topology

variable [TopologicalSpace K] [IsTopologicalRing K]

private theorem continuous_inducingMap : Continuous (inducingMap B K) := by
  change Continuous (fun q : openStabilizer B K =>
    (⟨MulAut.conj ((B.reverseMatrix K)⁻¹)⁻¹ q.val.val, q.property⟩ :
      B.parabolic K))
  apply Continuous.subtype_mk
  simp only [MulAut.conj_apply]
  exact (continuous_const.mul (continuous_subtype_val.comp continuous_subtype_val)).mul
    continuous_const

/-- The actual stabilizer/product equivalence is continuous in both directions
for the inherited subgroup and product topologies. -/
def openStabilizerContinuousEquiv :
    openStabilizer B K ≃ₜ* (∀ i, upperUnipotent (B.size i) K) where
  toMulEquiv := openStabilizerEquiv B K
  continuous_toFun := by
    apply continuous_pi
    intro i
    apply Continuous.subtype_mk
    exact (continuous_apply i).comp
      ((B.leviProjectionContinuous K).continuous.comp (continuous_inducingMap B K))
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    change Continuous (fun m : ∀ i, upperUnipotent (B.size i) K =>
      MulAut.conj (B.reverseMatrix K)⁻¹ (B.leviEmbedding K (fun i => (m i).val)))
    simp only [MulAut.conj_apply]
    exact (continuous_const.mul ((B.leviEmbeddingContinuous K).continuous.comp
      (continuous_pi (fun i => continuous_subtype_val.comp (continuous_apply i))))).mul
        continuous_const

@[simp] theorem openStabilizerContinuousEquiv_toMulEquiv :
    (openStabilizerContinuousEquiv B K).toMulEquiv = openStabilizerEquiv B K := rfl

end Topology

end Langlands.Whittaker
