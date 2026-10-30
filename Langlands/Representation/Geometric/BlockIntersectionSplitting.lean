import Langlands.Group.GL.Blocks
import Langlands.Representation.Geometric.GeneralIntersections

/-! Canonical Levi-first coordinates on a decomposable block intersection. -/

namespace Langlands.Geometric

open GeneralLinear
open scoped Pointwise

universe uR

variable {n : ℕ} (R : Type uR) [CommRing R] (B : BlockShape n)

/-- Every parabolic element has a Levi-then-radical factorization. -/
theorem blockParabolic_mem_levi_mul_unipotent (g : B.parabolic R) :
    g.val ∈ (B.leviSubgroup R : Set (GeneralLinear n R)) *
      (B.unipotentSubgroup R : Set (GeneralLinear n R)) := by
  let m := B.leviProjection R g
  let u : B.parabolic R := (B.leviInParabolic R m)⁻¹ * g
  have hu : u ∈ B.unipotentRadical R := by
    change B.leviProjection R u = 1
    simp only [u, map_mul, map_inv, B.leviProjection_section, m, inv_mul_cancel]
  refine ⟨B.leviEmbedding R m, ⟨m, rfl⟩,
    u.val, ⟨u, hu, rfl⟩, ?_⟩
  change B.leviEmbedding R m * ((B.leviEmbedding R m)⁻¹ * g.val) = g.val
  exact mul_inv_cancel_left _ _

/-- Projection identifies the Levi factor in every Levi-first factorization. -/
theorem blockParabolic_levi_factor_unique (g : B.parabolic R)
    {m u : GeneralLinear n R} (hm : m ∈ B.leviSubgroup R)
    (hu : u ∈ B.unipotentSubgroup R) (hmu : m * u = g.val) :
    B.leviEmbedding R (B.leviProjection R g) = m := by
  rcases hm with ⟨m, rfl⟩
  rcases hu with ⟨u, hu, rfl⟩
  have h : B.leviInParabolic R m * u = g := Subtype.ext hmu
  have hp : B.leviProjection R u = 1 := hu
  rw [← h, map_mul, B.leviProjection_section, hp, mul_one]

variable (H : Subgroup (GeneralLinear n R))
  (hd : General.IsDecomposable H (B.leviSubgroup R) (B.unipotentSubgroup R))

include hd in
/-- Literal decomposability forces the canonical diagonal projection into `H`. -/
theorem blockIntersection_leviProjection_mem (g : ↥(H ⊓ B.parabolic R)) :
    B.leviEmbedding R (B.leviProjection R ⟨g.val, g.property.2⟩) ∈ H := by
  let gp : B.parabolic R := ⟨g.val, g.property.2⟩
  obtain ⟨m, hm, u, hu, hmu⟩ :=
    (General.isDecomposable_iff _ _ _).mp hd g.val g.property.1
      (blockParabolic_mem_levi_mul_unipotent R B gp)
  rw [blockParabolic_levi_factor_unique R B gp hm.2 hu.2 hmu]
  exact hm.1

/-- The canonical Levi coordinate in the actual intersection. -/
def blockIntersectionLeviPart (g : ↥(H ⊓ B.parabolic R)) : ↥(H ⊓ B.leviSubgroup R) :=
  ⟨B.leviEmbedding R (B.leviProjection R ⟨g.val, g.property.2⟩),
    blockIntersection_leviProjection_mem R B H hd g,
    ⟨B.leviProjection R ⟨g.val, g.property.2⟩, rfl⟩⟩

/-- Remove the canonical Levi coordinate by multiplication on the left. -/
def blockIntersectionUnipotentPart (g : ↥(H ⊓ B.parabolic R)) :
    ↥(H ⊓ B.unipotentSubgroup R) := by
  let gp : B.parabolic R := ⟨g.val, g.property.2⟩
  let u : B.parabolic R :=
    (B.leviInParabolic R (B.leviProjection R gp))⁻¹ * gp
  have hu : u ∈ B.unipotentRadical R := by
    change B.leviProjection R u = 1
    simp only [u, map_mul, map_inv, B.leviProjection_section, inv_mul_cancel]
  exact ⟨u.val,
    H.mul_mem (H.inv_mem (blockIntersectionLeviPart R B H hd g).property.1)
      g.property.1,
    ⟨u, hu, rfl⟩⟩

@[simp]
theorem blockIntersectionLeviPart_val (g : ↥(H ⊓ B.parabolic R)) :
    (blockIntersectionLeviPart R B H hd g).val =
      B.leviEmbedding R (B.leviProjection R ⟨g.val, g.property.2⟩) := rfl

@[simp]
theorem blockIntersectionUnipotentPart_val (g : ↥(H ⊓ B.parabolic R)) :
    (blockIntersectionUnipotentPart R B H hd g).val =
      (blockIntersectionLeviPart R B H hd g).val⁻¹ * g.val := rfl

/-- The actual intersection is canonically parametrized by Levi-first factors. -/
def blockIntersectionDecomposition :
    (↥(H ⊓ B.parabolic R)) ≃
      (↥(H ⊓ B.leviSubgroup R)) × (↥(H ⊓ B.unipotentSubgroup R)) where
  toFun g :=
    (blockIntersectionLeviPart R B H hd g, blockIntersectionUnipotentPart R B H hd g)
  invFun mu := ⟨mu.1.val * mu.2.val,
    H.mul_mem mu.1.property.1 mu.2.property.1,
    (B.parabolic R).mul_mem
      (B.leviAsParabolic R ⟨mu.1.val, mu.1.property.2⟩).property
      ((B.mem_unipotentSubgroup_iff R mu.2.val).mp mu.2.property.2).1⟩
  left_inv g := by
    apply Subtype.ext
    change (blockIntersectionLeviPart R B H hd g).val *
      ((blockIntersectionLeviPart R B H hd g).val⁻¹ * g.val) = g.val
    exact mul_inv_cancel_left _ _
  right_inv mu := by
    have hm := blockParabolic_levi_factor_unique R B
      ⟨mu.1.val * mu.2.val,
        (B.parabolic R).mul_mem
          (B.leviAsParabolic R ⟨mu.1.val, mu.1.property.2⟩).property
          ((B.mem_unipotentSubgroup_iff R mu.2.val).mp mu.2.property.2).1⟩
      mu.1.property.2 mu.2.property.2 rfl
    apply Prod.ext
    · exact Subtype.ext hm
    · apply Subtype.ext
      change (B.leviEmbedding R (B.leviProjection R _))⁻¹ *
        (mu.1.val * mu.2.val) = mu.2.val
      rw [hm, inv_mul_cancel_left]

/-- The two factors of any intersection factorization are the canonical ones. -/
theorem blockIntersectionDecomposition_eq_factors
    (g : ↥(H ⊓ B.parabolic R)) (m : ↥(H ⊓ B.leviSubgroup R))
    (u : ↥(H ⊓ B.unipotentSubgroup R)) (hmu : m.val * u.val = g.val) :
    blockIntersectionDecomposition R B H hd g = (m, u) := by
  apply (blockIntersectionDecomposition R B H hd).symm.injective
  rw [Equiv.symm_apply_apply]
  exact Subtype.ext hmu.symm

section Topology

variable [TopologicalSpace R] [IsTopologicalRing R]

/-- Continuity uses the published actual diagonal-block maps. -/
theorem continuous_blockIntersectionLeviPart :
    Continuous (blockIntersectionLeviPart R B H hd) :=
  ((B.leviEmbeddingContinuous R).continuous.comp
    ((B.leviProjectionContinuous R).continuous.comp
      (continuous_subtype_val.subtype_mk _))).subtype_mk _

/-- The left radical coordinate is continuous in the actual subgroup topology. -/
theorem continuous_blockIntersectionUnipotentPart :
    Continuous (blockIntersectionUnipotentPart R B H hd) :=
  (((continuous_subtype_val.comp (continuous_blockIntersectionLeviPart R B H hd)).inv).mul
    continuous_subtype_val).subtype_mk _

/-- The canonical Levi-first factorization is a homeomorphism of spaces. -/
def blockIntersectionDecompositionHomeomorph :
    (↥(H ⊓ B.parabolic R)) ≃ₜ
      (↥(H ⊓ B.leviSubgroup R)) × (↥(H ⊓ B.unipotentSubgroup R)) where
  toEquiv := blockIntersectionDecomposition R B H hd
  continuous_toFun :=
    (continuous_blockIntersectionLeviPart R B H hd).prodMk
      (continuous_blockIntersectionUnipotentPart R B H hd)
  continuous_invFun :=
    ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _

@[simp]
theorem blockIntersectionDecompositionHomeomorph_fst_val (g : ↥(H ⊓ B.parabolic R)) :
    (blockIntersectionDecompositionHomeomorph R B H hd g).1.val =
      B.leviEmbedding R (B.leviProjection R ⟨g.val, g.property.2⟩) := rfl

@[simp]
theorem blockIntersectionDecompositionHomeomorph_snd_val (g : ↥(H ⊓ B.parabolic R)) :
    (blockIntersectionDecompositionHomeomorph R B H hd g).2.val =
      (B.leviEmbedding R (B.leviProjection R ⟨g.val, g.property.2⟩))⁻¹ * g.val := rfl

@[simp]
theorem blockIntersectionDecompositionHomeomorph_symm_val
    (mu : (↥(H ⊓ B.leviSubgroup R)) × (↥(H ⊓ B.unipotentSubgroup R))) :
    ((blockIntersectionDecompositionHomeomorph R B H hd).symm mu).val =
      mu.1.val * mu.2.val := rfl

/-- The homeomorphism has the constructed Levi-first equivalence as underlying map. -/
theorem blockIntersectionDecompositionHomeomorph_toEquiv :
    (blockIntersectionDecompositionHomeomorph R B H hd).toEquiv =
      blockIntersectionDecomposition R B H hd := rfl

/-- The homeomorphism sends `m*u` to the given factors `(m,u)`. -/
theorem blockIntersectionDecompositionHomeomorph_eq_factors
    (g : ↥(H ⊓ B.parabolic R)) (m : ↥(H ⊓ B.leviSubgroup R))
    (u : ↥(H ⊓ B.unipotentSubgroup R)) (hmu : m.val * u.val = g.val) :
    blockIntersectionDecompositionHomeomorph R B H hd g = (m, u) :=
  blockIntersectionDecomposition_eq_factors R B H hd g m u hmu

end Topology

end Langlands.Geometric
