import Langlands.Representation.Geometric.GeneralIntersectionNormalizers
import Langlands.Representation.Geometric.RefinementDefinitions
import Langlands.Representation.Geometric.GeometricLemmaStatement
import Langlands.Group.GL.OppositeBlocks
import Langlands.Group.HaarModulus

/-! Continuous transport from product-Levi coordinates to the actual
intersection subgroups of BZ77 section 6.3. -/

noncomputable section

namespace Langlands.Geometric

open GeneralLinear

universe uG uR

namespace General

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The published re-association `intersectionInAmbient`, packaged with its
two published continuity lemmas. -/
def intersectionInAmbientContinuous (M K : Subgroup G) (w : G) :
    intersectionIn M K w ≃ₜ* intersectionSource M K w where
  toMulEquiv := intersectionInAmbient M K w
  continuous_toFun := continuous_intersectionInAmbient M K w
  continuous_invFun := continuous_intersectionInAmbient_symm M K w

@[simp]
theorem intersectionInAmbientContinuous_apply (M K : Subgroup G) (w : G)
    (m : intersectionIn M K w) :
    (intersectionInAmbientContinuous M K w m : G) = m.val.val := rfl

@[simp]
theorem intersectionInAmbientContinuous_symm_apply (M K : Subgroup G) (w : G)
    (g : intersectionSource M K w) :
    ((intersectionInAmbientContinuous M K w).symm g).val.val = g.val := rfl

end General

section Relabel

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Relabel an actual subgroup along an equality of subgroups.
The underlying element is unchanged in both directions. -/
def subgroupEqualityContinuous {H K : Subgroup G} (h : H = K) : H ≃ₜ* K where
  toFun x := ⟨x.val, h ▸ x.property⟩
  invFun y := ⟨y.val, h ▸ y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

@[simp]
theorem subgroupEqualityContinuous_apply {H K : Subgroup G} (h : H = K) (x : H) :
    (subgroupEqualityContinuous h x : G) = x := rfl

@[simp]
theorem subgroupEqualityContinuous_symm_apply {H K : Subgroup G} (h : H = K) (y : K) :
    ((subgroupEqualityContinuous h).symm y : G) = y := rfl

end Relabel

variable (R : Type uR) [CommRing R] {n : ℕ}

section Coordinates

variable (B : BlockShape n) (w : Equiv.Perm (Fin n)) (K : Subgroup (GeneralLinear n R))

/-- The inverse block coordinates of an actual intersection element satisfy
the coordinate membership condition. -/
theorem leviEquiv_symm_mem_comap
    (y : General.intersectionIn (B.leviSubgroup R) K (permutation n R w)) :
    (B.leviEquiv R).symm y.val ∈ K.comap (conjugatedLeviMap R B w) := by
  change permutation n R w * (B.leviEquiv R ((B.leviEquiv R).symm y.val)).val *
    (permutation n R w)⁻¹ ∈ K
  rw [MulEquiv.apply_symm_apply]
  exact y.property

/-- The restriction of `B.leviEquiv R` from the coordinate intersection to
the actual intersection `M ∩ g⁻¹ K g` in the embedded Levi `M`. -/
def coordinateIntersectionMulEquiv :
    K.comap (conjugatedLeviMap R B w) ≃*
      General.intersectionIn (B.leviSubgroup R) K (permutation n R w) where
  toFun x := ⟨B.leviEquiv R x.val, x.property⟩
  invFun y := ⟨(B.leviEquiv R).symm y.val, leviEquiv_symm_mem_comap R B w K y⟩
  left_inv x := Subtype.ext ((B.leviEquiv R).symm_apply_apply x.val)
  right_inv y := Subtype.ext ((B.leviEquiv R).apply_symm_apply y.val)
  map_mul' a b := Subtype.ext ((B.leviEquiv R).map_mul a.val b.val)

section Topology

variable [TopologicalSpace R] [IsTopologicalRing R]

/-- The same restriction of `B.leviEquivContinuous R`, for the induced
subgroup topologies on both sides. -/
def coordinateIntersectionEquiv :
    K.comap (conjugatedLeviMap R B w) ≃ₜ*
      General.intersectionIn (B.leviSubgroup R) K (permutation n R w) where
  toMulEquiv := coordinateIntersectionMulEquiv R B w K
  continuous_toFun := by
    change Continuous (fun x : K.comap (conjugatedLeviMap R B w) =>
      (⟨B.leviEquivContinuous R x.val, x.property⟩ :
        General.intersectionIn (B.leviSubgroup R) K (permutation n R w)))
    exact ((B.leviEquivContinuous R).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    change Continuous (fun y : General.intersectionIn (B.leviSubgroup R) K
        (permutation n R w) =>
      (⟨(B.leviEquivContinuous R).symm y.val, leviEquiv_symm_mem_comap R B w K y⟩ :
        K.comap (conjugatedLeviMap R B w)))
    exact ((B.leviEquivContinuous R).symm.continuous.comp
      continuous_subtype_val).subtype_mk _

theorem coordinateIntersectionEquiv_apply (x : K.comap (conjugatedLeviMap R B w)) :
    coordinateIntersectionEquiv R B w K x = ⟨B.leviEquiv R x.val, x.property⟩ := rfl

theorem coordinateIntersectionEquiv_apply_eq_leviEquivContinuous
    (x : K.comap (conjugatedLeviMap R B w)) :
    (coordinateIntersectionEquiv R B w K x).val = B.leviEquivContinuous R x.val := rfl

@[simp]
theorem coordinateIntersectionEquiv_apply_val (x : K.comap (conjugatedLeviMap R B w)) :
    ((coordinateIntersectionEquiv R B w K x).val : GeneralLinear n R) =
      B.leviEmbedding R x.val := rfl

theorem coordinateIntersectionEquiv_symm_apply
    (y : General.intersectionIn (B.leviSubgroup R) K (permutation n R w)) :
    (coordinateIntersectionEquiv R B w K).symm y =
      ⟨(B.leviEquiv R).symm y.val, leviEquiv_symm_mem_comap R B w K y⟩ := rfl

@[simp]
theorem leviEmbedding_coordinateIntersectionEquiv_symm
    (y : General.intersectionIn (B.leviSubgroup R) K (permutation n R w)) :
    B.leviEmbedding R ((coordinateIntersectionEquiv R B w K).symm y).val = y.val.val :=
  congrArg Subtype.val ((B.leviEquiv R).apply_symm_apply y.val)

/-- The composite with the published re-association to the literal ambient
intersection `M ⊓ K.comap (conj g)`. -/
def coordinateIntersectionAmbientEquiv :
    K.comap (conjugatedLeviMap R B w) ≃ₜ*
      intersectionSource (B.leviSubgroup R) K (permutation n R w) :=
  (coordinateIntersectionEquiv R B w K).trans
    (General.intersectionInAmbientContinuous (B.leviSubgroup R) K (permutation n R w))

@[simp]
theorem coordinateIntersectionAmbientEquiv_apply (x : K.comap (conjugatedLeviMap R B w)) :
    (coordinateIntersectionAmbientEquiv R B w K x : GeneralLinear n R) =
      B.leviEmbedding R x.val := rfl

theorem coordinateIntersectionAmbientEquiv_symm_apply
    (g : intersectionSource (B.leviSubgroup R) K (permutation n R w)) :
    ((coordinateIntersectionAmbientEquiv R B w K).symm g).val =
      (B.leviEquiv R).symm ⟨g.val, g.property.1⟩ := rfl

@[simp]
theorem leviEmbedding_coordinateIntersectionAmbientEquiv_symm
    (g : intersectionSource (B.leviSubgroup R) K (permutation n R w)) :
    B.leviEmbedding R ((coordinateIntersectionAmbientEquiv R B w K).symm g).val = g.val :=
  congrArg Subtype.val ((B.leviEquiv R).apply_symm_apply ⟨g.val, g.property.1⟩)

end Topology

end Coordinates

section SourceIntersections

variable [TopologicalSpace R] [IsTopologicalRing R]
variable (B C : BlockShape n) (w : Equiv.Perm (Fin n))

/-- The specialization `K = C.parabolic R`, with domain `sourceParabolic`. -/
abbrev sourceParabolicIntersectionEquiv :
    sourceParabolic R B C w ≃ₜ*
      General.intersectionIn (B.leviSubgroup R) (C.parabolic R) (permutation n R w) :=
  coordinateIntersectionEquiv R B w (C.parabolic R)

/-- The specialization `K = C.leviSubgroup R`, with domain `sourceLevi`. -/
abbrev sourceLeviIntersectionEquiv :
    sourceLevi R B C w ≃ₜ*
      General.intersectionIn (B.leviSubgroup R) (C.leviSubgroup R) (permutation n R w) :=
  coordinateIntersectionEquiv R B w (C.leviSubgroup R)

/-- The specialization `K = C.unipotentSubgroup R`, with domain `sourceUnipotent`. -/
abbrev sourceUnipotentIntersectionEquiv :
    sourceUnipotent R B C w ≃ₜ*
      General.intersectionIn (B.leviSubgroup R) (C.unipotentSubgroup R) (permutation n R w) :=
  coordinateIntersectionEquiv R B w (C.unipotentSubgroup R)

end SourceIntersections

section Refined

variable [TopologicalSpace R] [IsTopologicalRing R]
variable (B C : BlockShape n) (w : Equiv.Perm (Fin n)) (S : BlockRefinement B)
  (hS : IsIntersectionRefinement (F := R) B C w S)

/-- The refined Levi, relabelled by `hS.2.1`, transported to the actual
intersection `M ∩ g⁻¹ N g`. -/
def refinedLeviIntersectionEquiv :
    refinedLevi R B S ≃ₜ*
      General.intersectionIn (B.leviSubgroup R) (C.leviSubgroup R) (permutation n R w) :=
  (subgroupEqualityContinuous hS.2.1.symm).trans
    (coordinateIntersectionEquiv R B w (C.leviSubgroup R))

/-- The refined radical, relabelled by `hS.2.2`, transported to the literal
ambient intersection `M ⊓ V.comap (conj g)`. -/
def refinedUnipotentIntersectionEquiv :
    refinedUnipotent R B S ≃ₜ*
      intersectionSource (B.leviSubgroup R) (C.unipotentSubgroup R) (permutation n R w) :=
  (subgroupEqualityContinuous hS.2.2.symm).trans
    (coordinateIntersectionAmbientEquiv R B w (C.unipotentSubgroup R))

@[simp]
theorem refinedLeviIntersectionEquiv_apply_val (m : refinedLevi R B S) :
    ((refinedLeviIntersectionEquiv R B C w S hS m).val : GeneralLinear n R) =
      B.leviEmbedding R m.val := rfl

theorem refinedLeviIntersectionEquiv_symm_apply
    (y : General.intersectionIn (B.leviSubgroup R) (C.leviSubgroup R) (permutation n R w)) :
    ((refinedLeviIntersectionEquiv R B C w S hS).symm y).val = (B.leviEquiv R).symm y.val :=
  rfl

@[simp]
theorem leviEmbedding_refinedLeviIntersectionEquiv_symm
    (y : General.intersectionIn (B.leviSubgroup R) (C.leviSubgroup R) (permutation n R w)) :
    B.leviEmbedding R ((refinedLeviIntersectionEquiv R B C w S hS).symm y).val = y.val.val :=
  leviEmbedding_coordinateIntersectionEquiv_symm R B w (C.leviSubgroup R) y

@[simp]
theorem refinedUnipotentIntersectionEquiv_apply (u : refinedUnipotent R B S) :
    (refinedUnipotentIntersectionEquiv R B C w S hS u : GeneralLinear n R) =
      B.leviEmbedding R u.val := rfl

theorem refinedUnipotentIntersectionEquiv_symm_apply
    (g : intersectionSource (B.leviSubgroup R) (C.unipotentSubgroup R) (permutation n R w)) :
    ((refinedUnipotentIntersectionEquiv R B C w S hS).symm g).val =
      (B.leviEquiv R).symm ⟨g.val, g.property.1⟩ := rfl

@[simp]
theorem leviEmbedding_refinedUnipotentIntersectionEquiv_symm
    (g : intersectionSource (B.leviSubgroup R) (C.unipotentSubgroup R) (permutation n R w)) :
    B.leviEmbedding R ((refinedUnipotentIntersectionEquiv R B C w S hS).symm g).val = g.val :=
  leviEmbedding_coordinateIntersectionAmbientEquiv_symm R B w (C.unipotentSubgroup R) g

/-- The two transports intertwine the refined Levi action on the refined
radical with the actual intersection action on `M ∩ g⁻¹ V g`. -/
theorem refinedUnipotentIntersectionEquiv_normalizerConj
    (m : refinedLevi R B S) (u : refinedUnipotent R B S) :
    refinedUnipotentIntersectionEquiv R B C w S hS
        (HaarModulus.normalizerConj (refinedUnipotent R B S)
          (refinedLeviNormalizer R B S m) u) =
      HaarModulus.normalizerConj
        (intersectionSource (B.leviSubgroup R) (C.unipotentSubgroup R) (permutation n R w))
        (General.intersectionToCorrectionNormalizer (B.leviSubgroup R) (C.leviSubgroup R)
          (B.leviSubgroup R) (C.unipotentSubgroup R) (permutation n R w)
          (B.leviSubgroup R).le_normalizer
          (C.leviSubgroup_le_normalizer_unipotentSubgroup R)
          (refinedLeviIntersectionEquiv R B C w S hS m))
        (refinedUnipotentIntersectionEquiv R B C w S hS u) := by
  apply Subtype.ext
  change B.leviEmbedding R (m.val * u.val * m.val⁻¹) =
    B.leviEmbedding R m.val * B.leviEmbedding R u.val * (B.leviEmbedding R m.val)⁻¹
  rw [map_mul, map_mul, map_inv]

end Refined

end Langlands.Geometric
