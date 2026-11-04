import Langlands.Representation.Jacquet.CanonicalLiftDefinitions

/-! The actual Jacquet quotient on the image of one compact compression. -/

noncomputable section

namespace Langlands.Jacquet

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Restrict the actual fixed-vector Jacquet quotient to the range of a single
compact compression. No stabilization or bijectivity is asserted. -/
def compressedImageJacquetMap (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N) :
    LinearMap.range (compressedAction ρ hρ K hK g) →ₗ[ℂ]
      fixedVectors (action ρ N M hMN) (K.toSubgroup.comap M.subtype) :=
  (fixedJacquetMap ρ N M hMN K.toSubgroup).comp
    (LinearMap.range (compressedAction ρ hρ K hK g)).subtype

@[simp]
theorem compressedImageJacquetMap_apply (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N)
    (v : LinearMap.range (compressedAction ρ hρ K hK g)) :
    compressedImageJacquetMap ρ hρ K hK g N M hMN v =
      fixedJacquetMap ρ N M hMN K.toSubgroup v.val := rfl

/-- Invert precisely the restricted quotient, when its bijectivity has been
proved, and include the result in the actual fixed-vector space. -/
def compressedImageLift (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N)
    (hb : Function.Bijective (compressedImageJacquetMap ρ hρ K hK g N M hMN)) :
    fixedVectors (action ρ N M hMN) (K.toSubgroup.comap M.subtype) →ₗ[ℂ]
      fixedVectors ρ K.toSubgroup :=
  (LinearMap.range (compressedAction ρ hρ K hK g)).subtype.comp
    (LinearEquiv.ofBijective
      (compressedImageJacquetMap ρ hρ K hK g N M hMN) hb).symm.toLinearMap

@[simp]
theorem fixedJacquetMap_compressedImageLift (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N)
    (hb : Function.Bijective (compressedImageJacquetMap ρ hρ K hK g N M hMN))
    (y : fixedVectors (action ρ N M hMN) (K.toSubgroup.comap M.subtype)) :
    fixedJacquetMap ρ N M hMN K.toSubgroup
        (compressedImageLift ρ hρ K hK g N M hMN hb y) = y :=
  (LinearEquiv.ofBijective
    (compressedImageJacquetMap ρ hρ K hK g N M hMN) hb).apply_symm_apply y

theorem compressedImageLift_mem_range (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N)
    (hb : Function.Bijective (compressedImageJacquetMap ρ hρ K hK g N M hMN))
    (y : fixedVectors (action ρ N M hMN) (K.toSubgroup.comap M.subtype)) :
    compressedImageLift ρ hρ K hK g N M hMN hb y ∈
      LinearMap.range (compressedAction ρ hρ K hK g) :=
  ((LinearEquiv.ofBijective
    (compressedImageJacquetMap ρ hρ K hK g N M hMN) hb).symm y).property

/-- A vector in the single compression image is determined by its quotient
class, once the restricted quotient is bijective. -/
theorem compressedImageLift_unique (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N)
    (hb : Function.Bijective (compressedImageJacquetMap ρ hρ K hK g N M hMN))
    (y : fixedVectors (action ρ N M hMN) (K.toSubgroup.comap M.subtype))
    (v : fixedVectors ρ K.toSubgroup)
    (hv : v ∈ LinearMap.range (compressedAction ρ hρ K hK g))
    (hj : fixedJacquetMap ρ N M hMN K.toSubgroup v = y) :
    v = compressedImageLift ρ hρ K hK g N M hMN hb y := by
  let e := LinearEquiv.ofBijective
    (compressedImageJacquetMap ρ hρ K hK g N M hMN) hb
  have he : e ⟨v, hv⟩ = y := hj
  have h := congrArg (fun z => (e.symm z).val) he
  change v = (e.symm y).val
  simpa only [LinearEquiv.symm_apply_apply] using h

theorem range_compressedImageLift (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N)
    (hb : Function.Bijective (compressedImageJacquetMap ρ hρ K hK g N M hMN)) :
    LinearMap.range (compressedImageLift ρ hρ K hK g N M hMN hb) =
      LinearMap.range (compressedAction ρ hρ K hK g) := by
  ext v
  constructor
  · rintro ⟨y, rfl⟩
    exact compressedImageLift_mem_range ρ hρ K hK g N M hMN hb y
  · intro hv
    exact ⟨fixedJacquetMap ρ N M hMN K.toSubgroup v,
      (compressedImageLift_unique ρ hρ K hK g N M hMN hb _ v hv rfl).symm⟩

/-- Equal actual compression images give equal inverse lifts. Establishing
that image equality for contracting elements is a separate obligation. -/
theorem compressedImageLift_eq_of_range_eq (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g g' : G)
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N)
    (hb : Function.Bijective (compressedImageJacquetMap ρ hρ K hK g N M hMN))
    (hb' : Function.Bijective (compressedImageJacquetMap ρ hρ K hK g' N M hMN))
    (heq : LinearMap.range (compressedAction ρ hρ K hK g) =
      LinearMap.range (compressedAction ρ hρ K hK g')) :
    compressedImageLift ρ hρ K hK g N M hMN hb =
      compressedImageLift ρ hρ K hK g' N M hMN hb' := by
  apply LinearMap.ext
  intro y
  symm
  apply compressedImageLift_unique ρ hρ K hK g N M hMN hb y
  · rw [heq]
    exact compressedImageLift_mem_range ρ hρ K hK g' N M hMN hb' y
  · exact fixedJacquetMap_compressedImageLift ρ hρ K hK g' N M hMN hb' y

end Langlands.Jacquet
