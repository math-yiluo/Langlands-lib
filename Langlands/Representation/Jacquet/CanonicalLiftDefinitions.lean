import Langlands.Representation.Compact.ProjectionProof
import Langlands.Representation.Smooth.FixedVectors.LawsProof
import Langlands.Representation.Jacquet.Coinvariants

/-!
# Compressed compact actions and carriers for canonical Jacquet lifts

These are elementary constructions from the normalized compact average. No
stabilization, invertibility, or canonical-lift isomorphism is asserted.
-/

noncomputable section

namespace Langlands.Jacquet

universe uR uG uV uW

section QuotientRestriction

variable {R : Type uR} [CommRing R]
variable {G : Type uG} [Group G]
variable {V : Type uV} [AddCommGroup V] [Module R V]

/-- The actual quotient map restricted to fixed vectors, with values fixed by
`M ∩ K`, viewed as the subgroup `K.comap M.subtype` of `M`. -/
def fixedJacquetMap (ρ : Representation R G V) (N M : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer N) (K : Subgroup G) :
    fixedVectors ρ K →ₗ[R] fixedVectors (action ρ N M hMN) (K.comap M.subtype) :=
  ((mk ρ N).comp (fixedVectors ρ K).subtype).codRestrict
    (fixedVectors (action ρ N M hMN) (K.comap M.subtype)) (by
      intro v k
      change action ρ N M hMN k.val (mk ρ N v.val) = mk ρ N v.val
      rw [action_mk]
      exact congrArg (mk ρ N) (v.property ⟨k.val.val, k.property⟩))

@[simp]
theorem fixedJacquetMap_apply (ρ : Representation R G V) (N M : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer N) (K : Subgroup G) (v : fixedVectors ρ K) :
    (fixedJacquetMap ρ N M hMN K v : Coinvariants ρ N) = mk ρ N (v : V) := rfl

theorem subtype_comp_fixedJacquetMap (ρ : Representation R G V) (N M : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer N) (K : Subgroup G) :
    (fixedVectors (action ρ N M hMN) (K.comap M.subtype)).subtype.comp
        (fixedJacquetMap ρ N M hMN K) =
      (mk ρ N).comp (fixedVectors ρ K).subtype := rfl

end QuotientRestriction

section CompactCompression

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Act by `g` and then apply the normalized compact average, on the actual
fixed-vector submodule. This is not an unspecified Hecke operator. -/
def compressedAction (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G) :
    Module.End ℂ (fixedVectors ρ K.toSubgroup) :=
  ((Compact.averageMap ρ hρ K hK).comp
    ((ρ g).comp (fixedVectors ρ K.toSubgroup).subtype)).codRestrict
      (fixedVectors ρ K.toSubgroup)
      (fun v => Compact.averageMap_mem_fixedVectors ρ hρ K hK (ρ g v.val))

@[simp]
theorem compressedAction_apply (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)
    (v : fixedVectors ρ K.toSubgroup) :
    (compressedAction ρ hρ K hK g v : V) =
      Compact.averageMap ρ hρ K hK (ρ g (v : V)) := rfl

@[simp]
theorem compressedAction_one (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    compressedAction ρ hρ K hK 1 = LinearMap.id := by
  ext v
  change Compact.averageMap ρ hρ K hK (ρ 1 v.val) = v.val
  simpa using Compact.averageMap_id ρ hρ K hK v.val v.property

/-- Intertwiners commute with compression, between independently sized carriers. -/
theorem compressedAction_natural (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (hρ : IsSmooth ρ) (hσ : IsSmooth σ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (g : G) (f : ρ.IntertwiningMap σ) :
    (fixedVectorsMap f K.toSubgroup).comp (compressedAction ρ hρ K hK g) =
      (compressedAction σ hσ K hK g).comp (fixedVectorsMap f K.toSubgroup) := by
  ext v
  change f (Compact.averageMap ρ hρ K hK (ρ g v.val)) =
    Compact.averageMap σ hσ K hK (σ g (f v.val))
  have h := LinearMap.congr_fun (Compact.averageMap_commute ρ σ hρ hσ K hK f)
    (ρ g v.val)
  change f (Compact.averageMap ρ hρ K hK (ρ g v.val)) =
    Compact.averageMap σ hσ K hK (f (ρ g v.val)) at h
  rw [h, f.isIntertwining]

/-- The intersection of the ranges of all powers of the compressed action.
The name does not assert finite-dimensional stabilization. -/
def stableImage (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G) :
    Submodule ℂ (fixedVectors ρ K.toSubgroup) :=
  ⨅ r : ℕ, LinearMap.range (compressedAction ρ hρ K hK g ^ r)

@[simp]
theorem mem_stableImage (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)
    (v : fixedVectors ρ K.toSubgroup) :
    v ∈ stableImage ρ hρ K hK g ↔
      ∀ r : ℕ, ∃ w : fixedVectors ρ K.toSubgroup,
        (compressedAction ρ hρ K hK g ^ r) w = v := by
  simp [stableImage, LinearMap.mem_range]

/-- The actual submodule supremum of the kernels of all powers. -/
def powerKernelSup (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G) :
    Submodule ℂ (fixedVectors ρ K.toSubgroup) :=
  ⨆ r : ℕ, LinearMap.ker (compressedAction ρ hρ K hK g ^ r)

/-- Inclusion of the stable-image carrier into the fixed-vector module. -/
def stableImageInclusion (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G) :
    stableImage ρ hρ K hK g →ₗ[ℂ] fixedVectors ρ K.toSubgroup :=
  (stableImage ρ hρ K hK g).subtype

/-- Inclusion of the stable-image carrier into the original representation. -/
def stableImageToRepresentation (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G) :
    stableImage ρ hρ K hK g →ₗ[ℂ] V :=
  (fixedVectors ρ K.toSubgroup).subtype.comp (stableImageInclusion ρ hρ K hK g)

/-- Each power range is preserved by the operator, hence so is their intersection. -/
theorem compressedAction_mem_stableImage (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)
    (v : fixedVectors ρ K.toSubgroup) (hv : v ∈ stableImage ρ hρ K hK g) :
    compressedAction ρ hρ K hK g v ∈ stableImage ρ hρ K hK g := by
  rw [mem_stableImage] at hv ⊢
  intro r
  obtain ⟨w, rfl⟩ := hv r
  refine ⟨compressedAction ρ hρ K hK g w, ?_⟩
  change ((compressedAction ρ hρ K hK g ^ r) * compressedAction ρ hρ K hK g) w =
    (compressedAction ρ hρ K hK g * (compressedAction ρ hρ K hK g ^ r)) w
  rw [← pow_succ, ← pow_succ']

/-- Restriction to the actual stable image, without an invertibility claim. -/
def stableImageAction (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G) :
    Module.End ℂ (stableImage ρ hρ K hK g) :=
  ((compressedAction ρ hρ K hK g).comp
    (stableImageInclusion ρ hρ K hK g)).codRestrict
      (stableImage ρ hρ K hK g)
      (fun v => compressedAction_mem_stableImage ρ hρ K hK g v.val v.property)

@[simp]
theorem stableImageAction_apply (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)
    (v : stableImage ρ hρ K hK g) :
    (stableImageAction ρ hρ K hK g v : fixedVectors ρ K.toSubgroup) =
      compressedAction ρ hρ K hK g (v : fixedVectors ρ K.toSubgroup) := rfl

theorem stableImageInclusion_comp_action (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G) :
    (stableImageInclusion ρ hρ K hK g).comp (stableImageAction ρ hρ K hK g) =
      (compressedAction ρ hρ K hK g).comp (stableImageInclusion ρ hρ K hK g) := rfl

/-- Restriction of the actual Jacquet quotient to the stable-image carrier.
Its codomain uses the unnormalized descended action; bijectivity is not assumed. -/
def stableImageJacquetMap (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N) :
    stableImage ρ hρ K hK g →ₗ[ℂ]
      fixedVectors (action ρ N M hMN) (K.toSubgroup.comap M.subtype) :=
  (fixedJacquetMap ρ N M hMN K.toSubgroup).comp (stableImageInclusion ρ hρ K hK g)

@[simp]
theorem stableImageJacquetMap_apply (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N)
    (v : stableImage ρ hρ K hK g) :
    (stableImageJacquetMap ρ hρ K hK g N M hMN v : Coinvariants ρ N) =
      mk ρ N (stableImageToRepresentation ρ hρ K hK g v) := rfl

theorem subtype_comp_stableImageJacquetMap (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N) :
    (fixedVectors (action ρ N M hMN) (K.toSubgroup.comap M.subtype)).subtype.comp
        (stableImageJacquetMap ρ hρ K hK g N M hMN) =
      (mk ρ N).comp (stableImageToRepresentation ρ hρ K hK g) := rfl

end CompactCompression

end Langlands.Jacquet
