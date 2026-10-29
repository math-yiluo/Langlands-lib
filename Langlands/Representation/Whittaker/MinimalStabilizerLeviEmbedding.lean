import Langlands.Group.GL.BlockModulus
import Langlands.Group.GL.SingletonBlocks
import Langlands.Group.GL.UpperUnipotent
import Langlands.Representation.Geometric.WeylDefinitions
import Langlands.Representation.Geometric.ClosedSubgroupDefinitions

/-!
# The Levi upper-unipotent group inside a minimal orbit stabilizer

For a block shape `B` and a minimal representative `v` of `W_B \ S_n`, put
`r = permutation n K v`. Conjugation `m ↦ r m r⁻¹` maps the ordered product of the
block upper-unipotent groups of the Levi into the full upper-unipotent group, and in
fact into the orbit stabilizer `U ∩ r P r⁻¹` of the representative `r`.
-/

noncomputable section

namespace Langlands.Whittaker

open GeneralLinear Geometric

universe uR uK

section Determinant

variable {R : Type uR} [CommRing R] {n : ℕ} (B : BlockShape n)

/-- Every diagonal block of an element of the product of the block upper-unipotent
groups has determinant one. -/
theorem pi_upperUnipotent_determinant_eq_one
    (m : Subgroup.pi Set.univ (fun i : Fin B.length => upperUnipotent (B.size i) R))
    (i : Fin B.length) :
    GeneralLinear.determinant ((m : B.Levi R) i) = 1 := by
  have hm : (m : B.Levi R) i ∈ upperUnipotent (B.size i) R := m.property i (Set.mem_univ i)
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one,
    Matrix.det_of_isUpperTriangular hm.1]
  exact Finset.prod_eq_one (fun a _ => hm.2 a)

end Determinant

variable {n : ℕ} (B : BlockShape n) (K : Type uK) [Field K]

/-- Conjugating a block-diagonal unitriangular matrix by the permutation matrix of a
minimal representative gives a unitriangular matrix. This uses the strict
monotonicity of the representative on each block. -/
theorem permutation_conj_leviEmbedding_mem_upperUnipotent
    (v : MinimalRepresentatives B (BlockShape.singletons n))
    (m : Subgroup.pi Set.univ (fun i : Fin B.length => upperUnipotent (B.size i) K)) :
    permutation n K v.val * B.leviEmbedding K (m : B.Levi K) *
        (permutation n K v.val)⁻¹ ∈ upperUnipotent n K := by
  have hm (i : Fin B.length) : (m : B.Levi K) i ∈ upperUnipotent (B.size i) K :=
    m.property i (Set.mem_univ i)
  refine ⟨?_, ?_⟩
  · intro x y hyx
    rw [permutation_conjugate_entry]
    obtain ⟨⟨i, a⟩, ha⟩ := B.indexEquiv.surjective (v.val⁻¹ x)
    obtain ⟨⟨j, b⟩, hb⟩ := B.indexEquiv.surjective (v.val⁻¹ y)
    rw [← ha, ← hb]
    change B.leviEmbedding K (m : B.Levi K) (B.index i a) (B.index j b) = 0
    by_cases hij : i = j
    · subst hij
      rw [B.leviEmbedding_apply_same]
      have hxa : v.val (B.index i a) = x := by
        change v.val (B.indexEquiv ⟨i, a⟩) = x
        rw [ha]
        simp
      have hyb : v.val (B.index i b) = y := by
        change v.val (B.indexEquiv ⟨i, b⟩) = y
        rw [hb]
        simp
      have hba : b < a := by
        apply (v.property.1 i).lt_iff_lt.mp
        change v.val (B.index i b) < v.val (B.index i a)
        rw [hxa, hyb]
        exact hyx
      exact UpperUnipotent.entry_eq_zero ⟨_, hm i⟩ hba
    · exact B.leviEmbedding_apply_ne K _ a b hij
  · intro x
    rw [permutation_conjugate_entry]
    obtain ⟨⟨i, a⟩, ha⟩ := B.indexEquiv.surjective (v.val⁻¹ x)
    rw [← ha]
    change B.leviEmbedding K (m : B.Levi K) (B.index i a) (B.index i a) = 1
    rw [B.leviEmbedding_apply_same]
    exact UpperUnipotent.entry_diag ⟨_, hm i⟩ a

/-- The raw homomorphism `m ↦ r m r⁻¹` from the product of the block
upper-unipotent groups into the full upper-unipotent group, `r = permutation n K v`.
A character of the upper-unipotent group can be composed with it. -/
def minimalLeviUpperUnipotentEmbedding
    (v : MinimalRepresentatives B (BlockShape.singletons n)) :
    Subgroup.pi Set.univ (fun i : Fin B.length => upperUnipotent (B.size i) K) →*
      upperUnipotent n K :=
  ((MulAut.conj (permutation n K v.val)).toMonoidHom.comp
      ((B.leviEmbedding K).comp
        (Subgroup.pi Set.univ
          (fun i : Fin B.length => upperUnipotent (B.size i) K)).subtype)).codRestrict
    (upperUnipotent n K)
    (fun m => permutation_conj_leviEmbedding_mem_upperUnipotent B K v m)

/-- The ambient matrix of the raw embedding. -/
@[simp] theorem minimalLeviUpperUnipotentEmbedding_val
    (v : MinimalRepresentatives B (BlockShape.singletons n))
    (m : Subgroup.pi Set.univ (fun i : Fin B.length => upperUnipotent (B.size i) K)) :
    (minimalLeviUpperUnipotentEmbedding B K v m : Langlands.GeneralLinear n K) =
      permutation n K v.val * B.leviEmbedding K (m : B.Levi K) *
        (permutation n K v.val)⁻¹ := rfl

/-- The embedding `m ↦ r m r⁻¹` of the product of the block upper-unipotent groups
into the actual orbit stabilizer `orbitStabilizer P U r`. -/
def minimalStabilizerLeviEmbedding
    (v : MinimalRepresentatives B (BlockShape.singletons n)) :
    Subgroup.pi Set.univ (fun i : Fin B.length => upperUnipotent (B.size i) K) →*
      orbitStabilizer (B.parabolic K) (upperUnipotent n K) (permutation n K v.val) :=
  (minimalLeviUpperUnipotentEmbedding B K v).codRestrict
    (orbitStabilizer (B.parabolic K) (upperUnipotent n K) (permutation n K v.val))
    (fun m => by
      change (MulAut.conj (permutation n K v.val)⁻¹)
        ((minimalLeviUpperUnipotentEmbedding B K v m : upperUnipotent n K) :
          Langlands.GeneralLinear n K) ∈ B.parabolic K
      rw [minimalLeviUpperUnipotentEmbedding_val, MulAut.conj_apply]
      have h : (permutation n K v.val)⁻¹ *
            (permutation n K v.val * B.leviEmbedding K (m : B.Levi K) *
              (permutation n K v.val)⁻¹) * (permutation n K v.val)⁻¹⁻¹ =
          B.leviEmbedding K (m : B.Levi K) := by group
      rw [h]
      exact (B.leviInParabolic K (m : B.Levi K)).property)

/-- The underlying upper-unipotent element is the raw embedding. -/
@[simp] theorem minimalStabilizerLeviEmbedding_val
    (v : MinimalRepresentatives B (BlockShape.singletons n))
    (m : Subgroup.pi Set.univ (fun i : Fin B.length => upperUnipotent (B.size i) K)) :
    (minimalStabilizerLeviEmbedding B K v m : upperUnipotent n K) =
      minimalLeviUpperUnipotentEmbedding B K v m := rfl

/-- Ambient evaluation law: the underlying matrix is exactly `r m r⁻¹`. -/
theorem minimalStabilizerLeviEmbedding_val_val
    (v : MinimalRepresentatives B (BlockShape.singletons n))
    (m : Subgroup.pi Set.univ (fun i : Fin B.length => upperUnipotent (B.size i) K)) :
    ((minimalStabilizerLeviEmbedding B K v m : upperUnipotent n K) :
        Langlands.GeneralLinear n K) =
      permutation n K v.val * B.leviEmbedding K (m : B.Levi K) *
        (permutation n K v.val)⁻¹ := rfl

/-- The underlying matrix lies in the actual upper-unipotent group. -/
theorem minimalStabilizerLeviEmbedding_mem_upperUnipotent
    (v : MinimalRepresentatives B (BlockShape.singletons n))
    (m : Subgroup.pi Set.univ (fun i : Fin B.length => upperUnipotent (B.size i) K)) :
    ((minimalStabilizerLeviEmbedding B K v m : upperUnipotent n K) :
        Langlands.GeneralLinear n K) ∈ upperUnipotent n K :=
  (minimalStabilizerLeviEmbedding B K v m : upperUnipotent n K).property

/-- Conjugating back to the inducing parabolic recovers the block-diagonal section. -/
theorem stabilizerToInducing_minimalStabilizerLeviEmbedding
    (v : MinimalRepresentatives B (BlockShape.singletons n))
    (m : Subgroup.pi Set.univ (fun i : Fin B.length => upperUnipotent (B.size i) K)) :
    stabilizerToInducing (B.parabolic K) (upperUnipotent n K) (permutation n K v.val)
        (minimalStabilizerLeviEmbedding B K v m) =
      B.leviInParabolic K (m : B.Levi K) := by
  apply Subtype.ext
  rw [stabilizerToInducing_apply, B.leviInParabolic_val]
  change (permutation n K v.val)⁻¹ *
      (permutation n K v.val * B.leviEmbedding K (m : B.Levi K) *
        (permutation n K v.val)⁻¹) * permutation n K v.val =
    B.leviEmbedding K (m : B.Levi K)
  group

/-- The Levi projection of the conjugated element is the original Levi element. -/
theorem leviProjection_stabilizerToInducing_minimalStabilizerLeviEmbedding
    (v : MinimalRepresentatives B (BlockShape.singletons n))
    (m : Subgroup.pi Set.univ (fun i : Fin B.length => upperUnipotent (B.size i) K)) :
    B.leviProjection K
        (stabilizerToInducing (B.parabolic K) (upperUnipotent n K) (permutation n K v.val)
          (minimalStabilizerLeviEmbedding B K v m)) =
      (m : B.Levi K) := by
  rw [stabilizerToInducing_minimalStabilizerLeviEmbedding, B.leviProjection_section]

/-- The raw embedding is injective. -/
theorem minimalLeviUpperUnipotentEmbedding_injective
    (v : MinimalRepresentatives B (BlockShape.singletons n)) :
    Function.Injective (minimalLeviUpperUnipotentEmbedding B K v) := by
  intro m m' h
  apply Subtype.ext
  apply B.leviEmbedding_injective K
  have h' := congrArg (fun u : upperUnipotent n K => (u : Langlands.GeneralLinear n K)) h
  simpa only [minimalLeviUpperUnipotentEmbedding_val, mul_left_inj, mul_right_inj] using h'

/-- The embedding into the orbit stabilizer is injective. -/
theorem minimalStabilizerLeviEmbedding_injective
    (v : MinimalRepresentatives B (BlockShape.singletons n)) :
    Function.Injective (minimalStabilizerLeviEmbedding B K v) := by
  intro m m' h
  apply minimalLeviUpperUnipotentEmbedding_injective B K v
  rw [← minimalStabilizerLeviEmbedding_val, ← minimalStabilizerLeviEmbedding_val, h]

section Topology

variable [TopologicalSpace K] [IsTopologicalRing K]

/-- The raw embedding is continuous for the subgroup and product topologies. -/
theorem continuous_minimalLeviUpperUnipotentEmbedding
    (v : MinimalRepresentatives B (BlockShape.singletons n)) :
    Continuous (minimalLeviUpperUnipotentEmbedding B K v) := by
  apply Continuous.subtype_mk
  change Continuous (fun m : Subgroup.pi Set.univ
      (fun i : Fin B.length => upperUnipotent (B.size i) K) =>
    permutation n K v.val * B.leviEmbedding K (m : B.Levi K) * (permutation n K v.val)⁻¹)
  exact (continuous_const.mul ((B.leviEmbeddingContinuous K).continuous.comp
    continuous_subtype_val)).mul continuous_const

/-- The embedding into the orbit stabilizer is continuous for the inherited subgroup
topologies and the product topology. -/
theorem continuous_minimalStabilizerLeviEmbedding
    (v : MinimalRepresentatives B (BlockShape.singletons n)) :
    Continuous (minimalStabilizerLeviEmbedding B K v) :=
  (continuous_minimalLeviUpperUnipotentEmbedding B K v).subtype_mk _

end Topology

section Modulus

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uK} p} (T : F.TopologicalData)
  {B} (v : MinimalRepresentatives B (BlockShape.singletons n))

/-- The positive half modulus of the parabolic is trivial on the conjugated Levi
upper-unipotent elements, because every diagonal block has determinant one. -/
theorem parabolicHalfModulus_stabilizerToInducing_minimalStabilizerLeviEmbedding
    (m : Subgroup.pi Set.univ
      (fun i : Fin B.length => upperUnipotent (B.size i) F.Carrier)) :
    T.parabolicHalfModulus B
        (stabilizerToInducing (B.parabolic F.Carrier) (upperUnipotent n F.Carrier)
          (permutation n F.Carrier v.val)
          (minimalStabilizerLeviEmbedding B F.Carrier v m)) = 1 := by
  rw [stabilizerToInducing_minimalStabilizerLeviEmbedding,
    T.parabolicHalfModulus_section, T.leviHalfModulus_eq_one]
  apply T.normOneLevi_le_ker_leviModulus B
  rw [T.mem_normOneLevi]
  intro i
  rw [PadicField.TopologicalData.determinantNorm, MonoidHom.comp_apply,
    pi_upperUnipotent_determinant_eq_one B m i, map_one]

end Modulus

end Langlands.Whittaker
