import Langlands.Representation.Geometric.WeylDefinitions

/-! The actual single-block Levi and its standard refinements. -/

namespace Langlands.GeneralLinear.BlockShape

universe u

/-- Transport a block shape along equality of its total rank, preserving its blocks. -/
def rankCast {m n : ℕ} (C : BlockShape m) (h : m = n) : BlockShape n where
  length := C.length
  size := C.size
  positive := C.positive
  sum_eq := C.sum_eq.trans h

variable {n : ℕ} (B : BlockShape n) (hB : B.length = 1)

include hB

/-- The unique block index of a one-block shape. -/
def singleBlockIndex : Fin B.length := ⟨0, by omega⟩

theorem eq_singleBlockIndex (i : Fin B.length) : i = B.singleBlockIndex hB := by
  apply Fin.ext
  have := i.isLt
  simp only [singleBlockIndex]
  omega

/-- The sole block has the full ambient rank. -/
theorem singleBlock_size (i : Fin B.length) : B.size i = n := by
  calc
    B.size i = ∑ j, B.size j := by
      symm
      apply Finset.sum_eq_single i
      · intro j _ hji
        exact False.elim (hji ((B.eq_singleBlockIndex hB j).trans
          (B.eq_singleBlockIndex hB i).symm))
      · simp
    _ = n := B.sum_eq

/-- Consecutive numbering in the sole block preserves coordinate values. -/
theorem singleBlock_index_val (i : Fin B.length) (a : Fin (B.size i)) :
    (B.index i a).val = a.val := by
  rcases B with ⟨l, s, hp, hs⟩
  dsimp at hB
  subst l
  exact finSigmaFinEquiv_one ⟨i, a⟩

variable (R : Type u) [CommRing R]

/-- A one-block standard parabolic is the whole actual general linear group. -/
theorem singleBlock_parabolic_eq_top : B.parabolic R = ⊤ := by
  apply top_unique
  intro g _
  rw [B.mem_parabolic_iff]
  intro i j a b hij
  have he : i = j := (B.eq_singleBlockIndex hB i).trans
    (B.eq_singleBlockIndex hB j).symm
  exact False.elim ((ne_of_lt hij) he.symm)

/-- In one block, embedding the diagonal projection recovers every matrix. -/
theorem singleBlock_leviEmbedding_projection (g : B.parabolic R) :
    B.leviEmbedding R (B.leviProjection R g) = g.val := by
  apply Units.ext
  ext a b
  obtain ⟨⟨i, x⟩, rfl⟩ := B.indexEquiv.surjective a
  obtain ⟨⟨j, y⟩, rfl⟩ := B.indexEquiv.surjective b
  have he : j = i := (B.eq_singleBlockIndex hB j).trans
    (B.eq_singleBlockIndex hB i).symm
  subst j
  exact B.leviEmbedding_apply_same R (B.leviProjection R g) i x y

/-- The single-block embedding, with inverse given by actual diagonal extraction. -/
def singleBlockLeviEquiv : B.Levi R ≃* Langlands.GeneralLinear n R where
  toFun := B.leviEmbedding R
  invFun g := B.leviProjection R ⟨g, by rw [B.singleBlock_parabolic_eq_top hB R]; trivial⟩
  left_inv m := by
    exact B.leviProjection_section R m
  right_inv g := B.singleBlock_leviEmbedding_projection hB R _
  map_mul' := (B.leviEmbedding R).map_mul

@[simp] theorem singleBlockLeviEquiv_toMonoidHom :
    (B.singleBlockLeviEquiv hB R).toMonoidHom = B.leviEmbedding R := rfl

theorem singleBlock_leviEmbedding_surjective : Function.Surjective (B.leviEmbedding R) :=
  (B.singleBlockLeviEquiv hB R).surjective

/-- The actual single-block equivalence respects the matrix and product topologies. -/
def singleBlockLeviEquivContinuous [TopologicalSpace R] [IsTopologicalRing R] :
    B.Levi R ≃ₜ* Langlands.GeneralLinear n R where
  toMulEquiv := B.singleBlockLeviEquiv hB R
  continuous_toFun := (B.leviEmbeddingContinuous R).continuous
  continuous_invFun := (B.leviProjectionContinuous R).continuous.comp
    (continuous_id.subtype_mk _)

@[simp] theorem singleBlockLeviEquivContinuous_toMonoidHom
    [TopologicalSpace R] [IsTopologicalRing R] :
    (B.singleBlockLeviEquivContinuous hB R).toMonoidHom = B.leviEmbedding R := rfl

/-- Refining the sole block is exactly choosing a block shape of the total rank. -/
def singleBlockRefinementEquiv : Geometric.BlockRefinement B ≃ BlockShape n where
  toFun S := (S (B.singleBlockIndex hB)).rankCast (B.singleBlock_size hB _)
  invFun C i := C.rankCast (B.singleBlock_size hB i).symm
  left_inv S := by
    funext i
    have hi := B.eq_singleBlockIndex hB i
    subst i
    rfl
  right_inv C := rfl

/-- The refinement correspondence preserves the actual consecutive coordinates. -/
theorem singleBlockRefinement_index (S : Geometric.BlockRefinement B)
    (j : Fin (B.singleBlockRefinementEquiv hB S).length)
    (a : Fin ((B.singleBlockRefinementEquiv hB S).size j)) :
    (B.singleBlockRefinementEquiv hB S).index j a =
      B.index (B.singleBlockIndex hB) ((S (B.singleBlockIndex hB)).index j a) := by
  apply Fin.ext
  rw [B.singleBlock_index_val hB]
  rfl

/-- Parabolic membership agrees through the actual single-block embedding. -/
theorem singleBlock_mem_refinedParabolic_iff (S : Geometric.BlockRefinement B)
    (m : B.Levi R) :
    m ∈ Geometric.refinedParabolic R B S ↔
      B.leviEmbedding R m ∈ (B.singleBlockRefinementEquiv hB S).parabolic R := by
  rw [(B.singleBlockRefinementEquiv hB S).mem_parabolic_iff]
  change (∀ i, i ∈ Set.univ → m i ∈ (S i).parabolic R) ↔ _
  constructor
  · intro hm j k a b hkj
    rw [B.singleBlockRefinement_index hB S, B.singleBlockRefinement_index hB S,
      B.leviEmbedding_apply_same]
    exact ((S (B.singleBlockIndex hB)).mem_parabolic_iff R _).mp
      (hm _ (Set.mem_univ _)) j k a b hkj
  · intro hm i _
    have hi := B.eq_singleBlockIndex hB i
    subst i
    rw [(S (B.singleBlockIndex hB)).mem_parabolic_iff]
    intro j k a b hkj
    have hh := hm j k a b hkj
    simpa only [B.singleBlockRefinement_index hB S j a,
      B.singleBlockRefinement_index hB S k b, B.leviEmbedding_apply_same] using hh

/-- Unipotent membership agrees under the same refinement correspondence. -/
theorem singleBlock_mem_refinedUnipotent_iff (S : Geometric.BlockRefinement B)
    (m : B.Levi R) :
    m ∈ Geometric.refinedUnipotent R B S ↔
      B.leviEmbedding R m ∈ (B.singleBlockRefinementEquiv hB S).unipotentSubgroup R := by
  rw [(B.singleBlockRefinementEquiv hB S).mem_unipotentSubgroup_iff]
  change (∀ i, i ∈ Set.univ → m i ∈ (S i).unipotentSubgroup R) ↔ _
  constructor
  · intro hm
    have hm0 := ((S (B.singleBlockIndex hB)).mem_unipotentSubgroup_iff R _).mp
      (hm _ (Set.mem_univ _))
    constructor
    · apply (B.singleBlock_mem_refinedParabolic_iff hB R S m).mp
      intro i _
      exact ((S i).mem_unipotentSubgroup_iff R _).mp (hm i (Set.mem_univ _)) |>.1
    · intro j a b
      rw [B.singleBlockRefinement_index hB S, B.singleBlockRefinement_index hB S,
        B.leviEmbedding_apply_same]
      exact hm0.2 j a b
  · rintro ⟨hp, hu⟩ i _
    have hi := B.eq_singleBlockIndex hB i
    subst i
    rw [(S (B.singleBlockIndex hB)).mem_unipotentSubgroup_iff]
    constructor
    · exact (B.singleBlock_mem_refinedParabolic_iff hB R S m).mpr hp _ (Set.mem_univ _)
    · intro j a b
      have hh := hu j a b
      simp only [B.singleBlockRefinement_index hB S j a,
        B.singleBlockRefinement_index hB S j b, B.leviEmbedding_apply_same] at hh
      exact hh

/-- The image of the actual refined parabolic is the corresponding standard parabolic. -/
theorem singleBlock_refinedParabolic_map (S : Geometric.BlockRefinement B) :
    (Geometric.refinedParabolic R B S).map (B.leviEmbedding R) =
      (B.singleBlockRefinementEquiv hB S).parabolic R := by
  ext g
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact (B.singleBlock_mem_refinedParabolic_iff hB R S m).mp hm
  · intro hg
    obtain ⟨m, rfl⟩ := B.singleBlock_leviEmbedding_surjective hB R g
    exact ⟨m, (B.singleBlock_mem_refinedParabolic_iff hB R S m).mpr hg, rfl⟩

/-- The same shape identifies the actual refined unipotent subgroup image. -/
theorem singleBlock_refinedUnipotent_map (S : Geometric.BlockRefinement B) :
    (Geometric.refinedUnipotent R B S).map (B.leviEmbedding R) =
      (B.singleBlockRefinementEquiv hB S).unipotentSubgroup R := by
  ext g
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact (B.singleBlock_mem_refinedUnipotent_iff hB R S m).mp hm
  · intro hg
    obtain ⟨m, rfl⟩ := B.singleBlock_leviEmbedding_surjective hB R g
    exact ⟨m, (B.singleBlock_mem_refinedUnipotent_iff hB R S m).mpr hg, rfl⟩

/-- Properness is preserved by the one-block refinement correspondence. -/
theorem singleBlock_refinedParabolic_ne_top_iff (S : Geometric.BlockRefinement B) :
    Geometric.refinedParabolic R B S ≠ ⊤ ↔
      (B.singleBlockRefinementEquiv hB S).parabolic R ≠ ⊤ := by
  apply not_congr
  constructor
  · intro hp
    rw [← B.singleBlock_refinedParabolic_map hB R S, hp]
    exact Subgroup.map_top_of_surjective _ (B.singleBlock_leviEmbedding_surjective hB R)
  · intro hp
    apply top_unique
    intro m _
    apply (B.singleBlock_mem_refinedParabolic_iff hB R S m).mpr
    rw [hp]
    trivial

end Langlands.GeneralLinear.BlockShape
