import Langlands.Algebra.IdempotentedRingRightLimit
import Langlands.Algebra.IdempotentedRingUniformity
import Mathlib.Topology.Algebra.IsUniformGroup.Constructions

/-!
# The actual coordinate uniformity on right-compatible families

Renard I.1.3, printed p.9/PDF15. The uniformity uses the actual coordinates
and the original pointwise additive group of the explicit inverse limit.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra
namespace IdempotentedRingRightLimit

open Filter Set
open scoped Uniformity Topology

universe uA

variable {A : Type uA} [NonUnitalRing A]

/-- The actual coordinate, regarded as an additive map into the original ring. -/
def coordinate (e : Idempotent A) : IdempotentedRingRightLimit A →+ A :=
  e.rightImage.subtype.comp (evaluation e)

@[simp] theorem coordinate_apply (e : Idempotent A)
    (x : IdempotentedRingRightLimit A) : coordinate e x = x.val e := rfl

/-- The source's zero-coordinate subgroup. -/
def coordinateKernel (e : Idempotent A) : AddSubgroup (IdempotentedRingRightLimit A) :=
  (coordinate e).ker

@[simp] theorem mem_coordinateKernel (e : Idempotent A)
    (x : IdempotentedRingRightLimit A) :
    x ∈ coordinateKernel e ↔ x.val e = 0 := Iff.rfl

theorem coordinateKernel_antitone :
    Antitone (coordinateKernel (A := A)) := by
  intro e f hef x hx
  change x.val e = 0
  rw [← x.property.2 e f hef, (mem_coordinateKernel f x).mp hx, zero_mul]

/-- Equality of the actual `e` coordinates. -/
def coordinateEntourage (e : Idempotent A) :
    Set (IdempotentedRingRightLimit A × IdempotentedRingRightLimit A) :=
  {p | p.1.val e = p.2.val e}

@[simp] theorem mem_coordinateEntourage (e : Idempotent A)
    (x y : IdempotentedRingRightLimit A) :
    (x, y) ∈ coordinateEntourage e ↔ x.val e = y.val e := Iff.rfl

theorem coordinateEntourage_antitone :
    Antitone (coordinateEntourage (A := A)) := by
  intro e f hef p hp
  change p.1.val e = p.2.val e
  rw [← p.1.property.2 e f hef, ← p.2.property.2 e f hef]
  exact congrArg (fun a : A => a * (e : A)) hp

theorem coordinateEntourage_eq_kernel (e : Idempotent A) :
    coordinateEntourage e =
      {p : IdempotentedRingRightLimit A × IdempotentedRingRightLimit A |
        p.1 - p.2 ∈ coordinateKernel e} := by
  ext p
  change (p.1.val e = p.2.val e) ↔ p.1.val e - p.2.val e = 0
  exact sub_eq_zero.symm

theorem coordinateKernel_common_refinement (hA : IsIdempotented A)
    (e f : Idempotent A) :
    ∃ g : Idempotent A, e ≤ g ∧ f ≤ g ∧
      coordinateKernel g ≤ coordinateKernel e ⊓ coordinateKernel f := by
  classical
  obtain ⟨g, hg⟩ := hA.finite_upper_bound {e, f}
  have he : e ≤ g := hg e (by simp)
  have hf : f ≤ g := hg f (by simp)
  exact ⟨g, he, hf, le_inf (coordinateKernel_antitone he)
    (coordinateKernel_antitone hf)⟩

theorem coordinateEntourage_directed (hA : IsIdempotented A) :
    Directed (· ≥ ·) (coordinateEntourage (A := A)) := by
  intro e f
  obtain ⟨g, he, hf, _⟩ := coordinateKernel_common_refinement hA e f
  exact ⟨g, coordinateEntourage_antitone he, coordinateEntourage_antitone hf⟩

/-- The actual infimum of discrete coordinate pullback uniformities.
Users install it locally on the existing family carrier. -/
@[instance_reducible]
def uniformSpace (A : Type uA) [NonUnitalRing A] :
    UniformSpace (IdempotentedRingRightLimit A) :=
  ⨅ e : Idempotent A,
    UniformSpace.comap (fun x : IdempotentedRingRightLimit A => x.val e)
      (⊥ : UniformSpace A)

theorem uniformity_eq :
    𝓤[uniformSpace A] = ⨅ e : Idempotent A, 𝓟 (coordinateEntourage e) := by
  rw [uniformSpace, iInf_uniformity]
  congr 1
  funext e
  rw [uniformity_comap, bot_uniformity, comap_principal]
  rfl

theorem uniformity_hasBasis (hA : IsIdempotented A) :
    (𝓤[uniformSpace A]).HasBasis (fun _ : Idempotent A => True)
      coordinateEntourage := by
  let : Nonempty (Idempotent A) := ⟨⟨0, IsIdempotentElem.zero⟩⟩
  rw [uniformity_eq]
  exact hasBasis_iInf_principal (coordinateEntourage_directed hA)

theorem nhds_hasBasis (hA : IsIdempotented A) (b : IdempotentedRingRightLimit A) :
    let := uniformSpace A
    (𝓝 b).HasBasis (fun _ : Idempotent A => True)
      (fun e => {x : IdempotentedRingRightLimit A | x.val e = b.val e}) := by
  let := uniformSpace A
  exact nhds_basis_uniformity (uniformity_hasBasis hA)

theorem coordinate_fiber_eq_translate (b : IdempotentedRingRightLimit A)
    (e : Idempotent A) :
    {x : IdempotentedRingRightLimit A | x.val e = b.val e} =
      {x : IdempotentedRingRightLimit A | x - b ∈ coordinateKernel e} := by
  ext x
  change (x.val e = b.val e) ↔ x.val e - b.val e = 0
  exact sub_eq_zero.symm

/-- The source's left translates `b + Ā(1-e)` of the coordinate kernels. -/
theorem coordinate_fiber_eq_image_add (b : IdempotentedRingRightLimit A)
    (e : Idempotent A) :
    {x : IdempotentedRingRightLimit A | x.val e = b.val e} =
      (fun k => b + k) '' (coordinateKernel e : Set (IdempotentedRingRightLimit A)) := by
  rw [image_add_left, coordinate_fiber_eq_translate]
  ext x
  change x - b ∈ coordinateKernel e ↔ -b + x ∈ coordinateKernel e
  rw [neg_add_eq_sub]

theorem nhds_hasBasis_translate (hA : IsIdempotented A)
    (b : IdempotentedRingRightLimit A) :
    let := uniformSpace A
    (𝓝 b).HasBasis (fun _ : Idempotent A => True)
      (fun e => (fun k => b + k) ''
        (coordinateKernel e : Set (IdempotentedRingRightLimit A))) := by
  let := uniformSpace A
  simpa only [coordinate_fiber_eq_image_add] using nhds_hasBasis hA b

theorem nhds_zero_hasBasis (hA : IsIdempotented A) :
    let := uniformSpace A
    (𝓝 (0 : IdempotentedRingRightLimit A)).HasBasis
      (fun _ : Idempotent A => True)
      (fun e => (coordinateKernel e : Set (IdempotentedRingRightLimit A))) := by
  let := uniformSpace A
  exact nhds_hasBasis hA 0

theorem uniformContinuous_coordinate (e : Idempotent A) :
    @UniformContinuous (IdempotentedRingRightLimit A) A (uniformSpace A)
      (⊥ : UniformSpace A) (coordinate e) := by
  rw [uniformContinuous_iff_le_comap]
  exact iInf_le _ e

/-- The original pointwise additive group is a uniform additive group. -/
theorem uniformAddGroup (A : Type uA) [NonUnitalRing A] :
    let := uniformSpace A
    IsUniformAddGroup (IdempotentedRingRightLimit A) := by
  change @IsUniformAddGroup (IdempotentedRingRightLimit A)
    (⨅ e : Idempotent A,
      UniformSpace.comap (fun x : IdempotentedRingRightLimit A => x.val e)
        (⊥ : UniformSpace A)) _
  apply isUniformAddGroup_iInf
  intro e
  let : UniformSpace A := ⊥
  exact IsUniformAddGroup.comap (coordinate e)

/-- The full product of discrete original carriers, with no compatibility restriction. -/
@[instance_reducible]
def discreteProductUniformSpace (A : Type uA) [NonUnitalRing A] :
    UniformSpace (Idempotent A → A) :=
  @Pi.uniformSpace (Idempotent A) (fun _ => A) (fun _ => ⊥)

/-- Exact equality with the pullback along the actual family inclusion. -/
theorem uniformSpace_eq_product_comap (A : Type uA) [NonUnitalRing A] :
    UniformSpace.comap (fun x : IdempotentedRingRightLimit A => x.val)
      (discreteProductUniformSpace A) = uniformSpace A := by
  rw [discreteProductUniformSpace, Pi.uniformSpace_eq, UniformSpace.comap_iInf]
  simp_rw [← UniformSpace.comap_comap]
  rfl

/-- In particular this is exactly the usual subtype uniformity in that product. -/
theorem uniformSpace_eq_subtype (A : Type uA) [NonUnitalRing A] :
    let : UniformSpace A := ⊥
    uniformSpace A = (inferInstance : UniformSpace (IdempotentedRingRightLimit A)) := by
  let : UniformSpace A := ⊥
  exact (uniformSpace_eq_product_comap A).symm

/-- The actual inclusion into the full discrete product is a uniform embedding. -/
theorem isUniformEmbedding_val (A : Type uA) [NonUnitalRing A] :
    let := uniformSpace A
    let : UniformSpace (Idempotent A → A) := discreteProductUniformSpace A
    IsUniformEmbedding (fun x : IdempotentedRingRightLimit A => x.val) := by
  let := uniformSpace A
  let : UniformSpace (Idempotent A → A) := discreteProductUniformSpace A
  exact ⟨isUniformInducing_iff_uniformSpace.mpr (uniformSpace_eq_product_comap A),
    Subtype.val_injective⟩

/-- Coordinate extensionality makes the actual family space Hausdorff. -/
theorem hausdorff (A : Type uA) [NonUnitalRing A] :
    let := uniformSpace A
    T2Space (IdempotentedRingRightLimit A) := by
  let : UniformSpace A := ⊥
  rw [uniformSpace_eq_subtype A]
  infer_instance

/-- Pullback by the original canonical map is exactly the original-ring uniformity. -/
theorem comap_canonical (A : Type uA) [NonUnitalRing A] :
    UniformSpace.comap (canonical (A := A)) (uniformSpace A) =
      idempotentedRingUniformSpace A := by
  rw [uniformSpace, UniformSpace.comap_iInf]
  simp_rw [← UniformSpace.comap_comap]
  rfl

theorem isUniformInducing_canonical (A : Type uA) [NonUnitalRing A] :
    let := idempotentedRingUniformSpace A
    let := uniformSpace A
    IsUniformInducing (canonical (A := A)) := by
  let := idempotentedRingUniformSpace A
  let := uniformSpace A
  exact isUniformInducing_iff_uniformSpace.mpr (comap_canonical A)

theorem isUniformEmbedding_canonical (hA : IsIdempotented A) :
    let := idempotentedRingUniformSpace A
    let := uniformSpace A
    IsUniformEmbedding (canonical (A := A)) := by
  let := idempotentedRingUniformSpace A
  let := uniformSpace A
  exact ⟨isUniformInducing_canonical A, canonical_injective hA⟩

/-! Complete unapplied interfaces retain the arbitrary original ring universe. -/

example : {A : Type uA} → [NonUnitalRing A] → (e : Idempotent A) →
    IdempotentedRingRightLimit A →+ A :=
  @coordinate.{uA}

example : {A : Type uA} → [NonUnitalRing A] → (e : Idempotent A) →
    AddSubgroup (IdempotentedRingRightLimit A) :=
  @coordinateKernel.{uA}

example : {A : Type uA} → [NonUnitalRing A] →
    Antitone (coordinateKernel (A := A)) :=
  @coordinateKernel_antitone.{uA}

example : {A : Type uA} → [NonUnitalRing A] → (e : Idempotent A) →
    Set (IdempotentedRingRightLimit A × IdempotentedRingRightLimit A) :=
  @coordinateEntourage.{uA}

example : {A : Type uA} → [NonUnitalRing A] →
    Antitone (coordinateEntourage (A := A)) :=
  @coordinateEntourage_antitone.{uA}

example : {A : Type uA} → [NonUnitalRing A] → (e : Idempotent A) →
    coordinateEntourage e =
      {p : IdempotentedRingRightLimit A × IdempotentedRingRightLimit A |
        p.1 - p.2 ∈ coordinateKernel e} :=
  @coordinateEntourage_eq_kernel.{uA}

example : {A : Type uA} → [NonUnitalRing A] → IsIdempotented A →
    (e f : Idempotent A) →
    ∃ g : Idempotent A, e ≤ g ∧ f ≤ g ∧
      coordinateKernel g ≤ coordinateKernel e ⊓ coordinateKernel f :=
  @coordinateKernel_common_refinement.{uA}

example : {A : Type uA} → [NonUnitalRing A] → IsIdempotented A →
    Directed (· ≥ ·) (coordinateEntourage (A := A)) :=
  @coordinateEntourage_directed.{uA}

example : (A : Type uA) → [NonUnitalRing A] →
    UniformSpace (IdempotentedRingRightLimit A) :=
  uniformSpace.{uA}

example : {A : Type uA} → [NonUnitalRing A] →
    𝓤[uniformSpace A] = ⨅ e : Idempotent A, 𝓟 (coordinateEntourage e) :=
  @uniformity_eq.{uA}

example : {A : Type uA} → [NonUnitalRing A] → IsIdempotented A →
    (𝓤[uniformSpace A]).HasBasis (fun _ : Idempotent A => True) coordinateEntourage :=
  @uniformity_hasBasis.{uA}

example : {A : Type uA} → [NonUnitalRing A] → IsIdempotented A →
    (b : IdempotentedRingRightLimit A) →
    let := uniformSpace A
    (𝓝 b).HasBasis (fun _ : Idempotent A => True)
      (fun e => {x : IdempotentedRingRightLimit A | x.val e = b.val e}) :=
  @nhds_hasBasis.{uA}

example : {A : Type uA} → [NonUnitalRing A] → (b : IdempotentedRingRightLimit A) →
    (e : Idempotent A) →
    {x : IdempotentedRingRightLimit A | x.val e = b.val e} =
      {x : IdempotentedRingRightLimit A | x - b ∈ coordinateKernel e} :=
  @coordinate_fiber_eq_translate.{uA}

example : {A : Type uA} → [NonUnitalRing A] → (b : IdempotentedRingRightLimit A) →
    (e : Idempotent A) →
    {x : IdempotentedRingRightLimit A | x.val e = b.val e} =
      (fun k => b + k) '' (coordinateKernel e : Set (IdempotentedRingRightLimit A)) :=
  @coordinate_fiber_eq_image_add.{uA}

example : {A : Type uA} → [NonUnitalRing A] → IsIdempotented A →
    (b : IdempotentedRingRightLimit A) →
    let := uniformSpace A
    (𝓝 b).HasBasis (fun _ : Idempotent A => True)
      (fun e => (fun k => b + k) ''
        (coordinateKernel e : Set (IdempotentedRingRightLimit A))) :=
  @nhds_hasBasis_translate.{uA}

example : {A : Type uA} → [NonUnitalRing A] → IsIdempotented A →
    let := uniformSpace A
    (𝓝 (0 : IdempotentedRingRightLimit A)).HasBasis
      (fun _ : Idempotent A => True)
      (fun e => (coordinateKernel e : Set (IdempotentedRingRightLimit A))) :=
  @nhds_zero_hasBasis.{uA}

example : {A : Type uA} → [NonUnitalRing A] → (e : Idempotent A) →
    @UniformContinuous (IdempotentedRingRightLimit A) A (uniformSpace A)
      (⊥ : UniformSpace A) (coordinate e) :=
  @uniformContinuous_coordinate.{uA}

example : (A : Type uA) → [NonUnitalRing A] →
    let := uniformSpace A
    IsUniformAddGroup (IdempotentedRingRightLimit A) :=
  uniformAddGroup.{uA}

example : (A : Type uA) → [NonUnitalRing A] → UniformSpace (Idempotent A → A) :=
  discreteProductUniformSpace.{uA}

example : (A : Type uA) → [NonUnitalRing A] →
    UniformSpace.comap (fun x : IdempotentedRingRightLimit A => x.val)
      (discreteProductUniformSpace A) = uniformSpace A :=
  uniformSpace_eq_product_comap.{uA}

example : (A : Type uA) → [NonUnitalRing A] →
    let : UniformSpace A := ⊥
    uniformSpace A = (inferInstance : UniformSpace (IdempotentedRingRightLimit A)) :=
  uniformSpace_eq_subtype.{uA}

/-! The instance found above is Mathlib's subtype uniformity of the full discrete product. -/
example (A : Type uA) [NonUnitalRing A] :
    uniformSpace A =
      @instUniformSpaceSubtype (Idempotent A → A) (· ∈ rightCompatibleFamilies A)
        (discreteProductUniformSpace A) :=
  uniformSpace_eq_subtype A

example : (A : Type uA) → [NonUnitalRing A] →
    let := uniformSpace A
    let : UniformSpace (Idempotent A → A) := discreteProductUniformSpace A
    IsUniformEmbedding (fun x : IdempotentedRingRightLimit A => x.val) :=
  isUniformEmbedding_val.{uA}

example : (A : Type uA) → [NonUnitalRing A] →
    let := uniformSpace A
    T2Space (IdempotentedRingRightLimit A) :=
  hausdorff.{uA}

example : (A : Type uA) → [NonUnitalRing A] →
    UniformSpace.comap (canonical (A := A)) (uniformSpace A) =
      idempotentedRingUniformSpace A :=
  comap_canonical.{uA}

example : (A : Type uA) → [NonUnitalRing A] →
    let := idempotentedRingUniformSpace A
    let := uniformSpace A
    IsUniformInducing (canonical (A := A)) :=
  isUniformInducing_canonical.{uA}

example : {A : Type uA} → [NonUnitalRing A] → IsIdempotented A →
    let := idempotentedRingUniformSpace A
    let := uniformSpace A
    IsUniformEmbedding (canonical (A := A)) :=
  @isUniformEmbedding_canonical.{uA}

end IdempotentedRingRightLimit
end Langlands.Algebra
