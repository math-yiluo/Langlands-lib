import Langlands.Algebra.NonUnitalModuleLeftLimit
import Langlands.Algebra.NonUnitalModuleUniformity

/-!
# The actual coordinate uniformity on left-compatible module families

Renard I.1.4, printed p.9/PDF15. The full product of discrete original
vector carriers provides the exact ambient subspace comparison.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra
namespace NonUnitalModuleLeftLimit

open Filter Set
open scoped Uniformity Topology

universe uA uM

variable {A : Type uA} [NonUnitalRing A]
  {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]

/-- The actual coordinate, included in the original additive vector group. -/
def coordinate (e : Idempotent A) : NonUnitalModuleLeftLimit A M →+ M :=
  (e.leftImage M).subtype.comp (evaluation e)

@[simp] theorem coordinate_apply (e : Idempotent A) (x : NonUnitalModuleLeftLimit A M) :
    coordinate e x = x.val e := rfl

/-- The actual subgroup of families vanishing at `e`. -/
def coordinateKernel (e : Idempotent A) : AddSubgroup (NonUnitalModuleLeftLimit A M) :=
  (coordinate e).ker

@[simp] theorem mem_coordinateKernel (e : Idempotent A)
    (x : NonUnitalModuleLeftLimit A M) :
    x ∈ coordinateKernel e ↔ x.val e = 0 := Iff.rfl

theorem coordinateKernel_antitone :
    Antitone (coordinateKernel (A := A) (M := M)) := by
  intro e f hef x hx
  change x.val e = 0
  rw [← x.property.2 e f hef, (mem_coordinateKernel f x).mp hx, smul_zero]

/-- Equality of the actual module-family coordinates at `e`. -/
def coordinateEntourage (e : Idempotent A) :
    Set (NonUnitalModuleLeftLimit A M × NonUnitalModuleLeftLimit A M) :=
  {p | p.1.val e = p.2.val e}

@[simp] theorem mem_coordinateEntourage (e : Idempotent A)
    (x y : NonUnitalModuleLeftLimit A M) :
    (x, y) ∈ coordinateEntourage e ↔ x.val e = y.val e := Iff.rfl

theorem coordinateEntourage_antitone :
    Antitone (coordinateEntourage (A := A) (M := M)) := by
  intro e f hef p hp
  change p.1.val e = p.2.val e
  rw [← p.1.property.2 e f hef, ← p.2.property.2 e f hef]
  exact congrArg (fun m : M => (e : A) • m) hp

theorem coordinateEntourage_eq_kernel (e : Idempotent A) :
    coordinateEntourage e =
      {p : NonUnitalModuleLeftLimit A M × NonUnitalModuleLeftLimit A M |
        p.1 - p.2 ∈ coordinateKernel e} := by
  ext p
  change (p.1.val e = p.2.val e) ↔ p.1.val e - p.2.val e = 0
  exact sub_eq_zero.symm

theorem coordinateKernel_common_refinement (hA : IsIdempotented A)
    (e f : Idempotent A) :
    ∃ g : Idempotent A, e ≤ g ∧ f ≤ g ∧
      coordinateKernel (M := M) g ≤ coordinateKernel e ⊓ coordinateKernel f := by
  classical
  obtain ⟨g, hg⟩ := hA.finite_upper_bound {e, f}
  have he : e ≤ g := hg e (by simp)
  have hf : f ≤ g := hg f (by simp)
  exact ⟨g, he, hf, le_inf (coordinateKernel_antitone he)
    (coordinateKernel_antitone hf)⟩

theorem coordinateEntourage_directed (hA : IsIdempotented A) :
    Directed (· ≥ ·) (coordinateEntourage (A := A) (M := M)) := by
  intro e f
  obtain ⟨g, he, hf, _⟩ := coordinateKernel_common_refinement (M := M) hA e f
  exact ⟨g, coordinateEntourage_antitone he, coordinateEntourage_antitone hf⟩

/-- The actual infimum of discrete-coordinate pullbacks on the existing family group. -/
@[instance_reducible]
def uniformSpace (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M] :
    UniformSpace (NonUnitalModuleLeftLimit A M) :=
  ⨅ e : Idempotent A,
    UniformSpace.comap (fun x : NonUnitalModuleLeftLimit A M => x.val e)
      (⊥ : UniformSpace M)

theorem uniformity_eq :
    𝓤[uniformSpace A M] = ⨅ e : Idempotent A, 𝓟 (coordinateEntourage (M := M) e) := by
  rw [uniformSpace, iInf_uniformity]
  congr 1
  funext e
  rw [uniformity_comap, bot_uniformity, comap_principal]
  rfl

theorem uniformity_hasBasis (hA : IsIdempotented A) :
    (𝓤[uniformSpace A M]).HasBasis (fun _ : Idempotent A => True)
      coordinateEntourage := by
  let : Nonempty (Idempotent A) := ⟨⟨0, IsIdempotentElem.zero⟩⟩
  rw [uniformity_eq]
  exact hasBasis_iInf_principal (coordinateEntourage_directed (M := M) hA)

theorem nhds_hasBasis (hA : IsIdempotented A) (b : NonUnitalModuleLeftLimit A M) :
    let := uniformSpace A M
    (𝓝 b).HasBasis (fun _ : Idempotent A => True)
      (fun e => {x : NonUnitalModuleLeftLimit A M | x.val e = b.val e}) := by
  let := uniformSpace A M
  exact nhds_basis_uniformity (uniformity_hasBasis (M := M) hA)

theorem coordinate_fiber_eq_translate (b : NonUnitalModuleLeftLimit A M)
    (e : Idempotent A) :
    {x : NonUnitalModuleLeftLimit A M | x.val e = b.val e} =
      {x : NonUnitalModuleLeftLimit A M | x - b ∈ coordinateKernel e} := by
  ext x
  change (x.val e = b.val e) ↔ x.val e - b.val e = 0
  exact sub_eq_zero.symm

theorem nhds_hasBasis_kernel (hA : IsIdempotented A) (b : NonUnitalModuleLeftLimit A M) :
    let := uniformSpace A M
    (𝓝 b).HasBasis (fun _ : Idempotent A => True)
      (fun e => {x : NonUnitalModuleLeftLimit A M | x - b ∈ coordinateKernel e}) := by
  let := uniformSpace A M
  simpa only [coordinate_fiber_eq_translate] using nhds_hasBasis hA b

theorem coordinate_fiber_eq_image_add (b : NonUnitalModuleLeftLimit A M)
    (e : Idempotent A) :
    {x : NonUnitalModuleLeftLimit A M | x.val e = b.val e} =
      (fun k => b + k) '' (coordinateKernel (M := M) e : Set (NonUnitalModuleLeftLimit A M)) := by
  rw [image_add_left, coordinate_fiber_eq_translate]
  ext x
  change x - b ∈ coordinateKernel e ↔ -b + x ∈ coordinateKernel e
  rw [neg_add_eq_sub]

theorem nhds_hasBasis_translate (hA : IsIdempotented A) (b : NonUnitalModuleLeftLimit A M) :
    let := uniformSpace A M
    (𝓝 b).HasBasis (fun _ : Idempotent A => True)
      (fun e => (fun k => b + k) ''
        (coordinateKernel (M := M) e : Set (NonUnitalModuleLeftLimit A M))) := by
  let := uniformSpace A M
  simpa only [coordinate_fiber_eq_image_add] using nhds_hasBasis hA b

theorem nhds_zero_hasBasis (hA : IsIdempotented A) :
    let := uniformSpace A M
    (𝓝 (0 : NonUnitalModuleLeftLimit A M)).HasBasis
      (fun _ : Idempotent A => True)
      (fun e => (coordinateKernel (M := M) e : Set (NonUnitalModuleLeftLimit A M))) := by
  let := uniformSpace A M
  exact nhds_hasBasis hA 0

theorem uniformContinuous_coordinate (e : Idempotent A) :
    @UniformContinuous (NonUnitalModuleLeftLimit A M) M (uniformSpace A M)
      (⊥ : UniformSpace M) (coordinate e) := by
  rw [uniformContinuous_iff_le_comap]
  exact iInf_le _ e

/-- The original pointwise additive group is uniform. -/
theorem uniformAddGroup (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M] :
    @IsUniformAddGroup (NonUnitalModuleLeftLimit A M) (uniformSpace A M) _ := by
  change @IsUniformAddGroup (NonUnitalModuleLeftLimit A M)
    (⨅ e : Idempotent A,
      UniformSpace.comap (fun x : NonUnitalModuleLeftLimit A M => x.val e)
        (⊥ : UniformSpace M)) _
  apply isUniformAddGroup_iInf
  intro e
  let : UniformSpace M := ⊥
  exact IsUniformAddGroup.comap (coordinate (M := M) e)

/-- The full product of discrete original vector carriers. -/
@[instance_reducible]
def discreteProductUniformSpace (A : Type uA) (M : Type uM)
    [NonUnitalRing A] : UniformSpace (Idempotent A → M) :=
  @Pi.uniformSpace (Idempotent A) (fun _ => M) (fun _ => ⊥)

theorem uniformSpace_eq_product_comap (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M] :
    UniformSpace.comap (fun x : NonUnitalModuleLeftLimit A M => x.val)
      (discreteProductUniformSpace A M) = uniformSpace A M := by
  rw [discreteProductUniformSpace, Pi.uniformSpace_eq, UniformSpace.comap_iInf]
  simp_rw [← UniformSpace.comap_comap]
  rfl

/-- Exact equality with the usual subtype uniformity in that full discrete product. -/
theorem uniformSpace_eq_subtype (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M] :
    uniformSpace A M =
      @instUniformSpaceSubtype (Idempotent A → M) (· ∈ leftCompatibleFamilies A M)
        (discreteProductUniformSpace A M) :=
  (uniformSpace_eq_product_comap A M).symm

theorem isUniformEmbedding_val (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M] :
    @IsUniformEmbedding (NonUnitalModuleLeftLimit A M) (Idempotent A → M)
      (uniformSpace A M) (discreteProductUniformSpace A M) Subtype.val := by
  let := uniformSpace A M
  let : UniformSpace (Idempotent A → M) := discreteProductUniformSpace A M
  exact ⟨isUniformInducing_iff_uniformSpace.mpr (uniformSpace_eq_product_comap A M),
    Subtype.val_injective⟩

theorem hausdorff (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M] :
    @T2Space (NonUnitalModuleLeftLimit A M) (uniformSpace A M).toTopologicalSpace := by
  let : UniformSpace M := ⊥
  rw [uniformSpace_eq_subtype A M]
  infer_instance

/-- The canonical pullback is exactly the actual original-vector uniformity. -/
theorem comap_canonical (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M] :
    UniformSpace.comap (canonical (A := A) (M := M)) (uniformSpace A M) =
      nonUnitalModuleUniformSpace A M := by
  rw [uniformSpace, UniformSpace.comap_iInf]
  simp_rw [← UniformSpace.comap_comap]
  rfl

theorem isUniformInducing_canonical (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M] :
    @IsUniformInducing M (NonUnitalModuleLeftLimit A M)
      (nonUnitalModuleUniformSpace A M) (uniformSpace A M) canonical := by
  let := nonUnitalModuleUniformSpace A M
  let := uniformSpace A M
  exact isUniformInducing_iff_uniformSpace.mpr (comap_canonical A M)

theorem isUniformEmbedding_canonical (hM : IsNondegenerate A M) :
    @IsUniformEmbedding M (NonUnitalModuleLeftLimit A M)
      (nonUnitalModuleUniformSpace A M) (uniformSpace A M) canonical := by
  let := nonUnitalModuleUniformSpace A M
  let := uniformSpace A M
  exact ⟨isUniformInducing_canonical A M, canonical_injective hM⟩

/-! Complete unapplied interfaces at independent original scalar/vector universes. -/

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (e : Idempotent A) → NonUnitalModuleLeftLimit A M →+ M :=
  @coordinate.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (e : Idempotent A) → AddSubgroup (NonUnitalModuleLeftLimit A M) :=
  @coordinateKernel.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    Antitone (coordinateKernel (A := A) (M := M)) :=
  @coordinateKernel_antitone.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (e : Idempotent A) →
    Set (NonUnitalModuleLeftLimit A M × NonUnitalModuleLeftLimit A M) :=
  @coordinateEntourage.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    Antitone (coordinateEntourage (A := A) (M := M)) :=
  @coordinateEntourage_antitone.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (e : Idempotent A) →
    coordinateEntourage e =
      {p : NonUnitalModuleLeftLimit A M × NonUnitalModuleLeftLimit A M |
        p.1 - p.2 ∈ coordinateKernel e} :=
  @coordinateEntourage_eq_kernel.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] → IsIdempotented A →
    (e f : Idempotent A) →
    ∃ g : Idempotent A, e ≤ g ∧ f ≤ g ∧
      coordinateKernel (M := M) g ≤ coordinateKernel e ⊓ coordinateKernel f :=
  @coordinateKernel_common_refinement.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] → IsIdempotented A →
    Directed (· ≥ ·) (coordinateEntourage (A := A) (M := M)) :=
  @coordinateEntourage_directed.{uA, uM}

example : (A : Type uA) → (M : Type uM) →
    [NonUnitalRing A] → [AddCommGroup M] → [NonUnitalModule A M] →
    UniformSpace (NonUnitalModuleLeftLimit A M) :=
  uniformSpace.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    𝓤[uniformSpace A M] = ⨅ e : Idempotent A, 𝓟 (coordinateEntourage (M := M) e) :=
  @uniformity_eq.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] → IsIdempotented A →
    (𝓤[uniformSpace A M]).HasBasis (fun _ : Idempotent A => True) coordinateEntourage :=
  @uniformity_hasBasis.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] → IsIdempotented A →
    (b : NonUnitalModuleLeftLimit A M) →
    let := uniformSpace A M
    (𝓝 b).HasBasis (fun _ : Idempotent A => True)
      (fun e => {x : NonUnitalModuleLeftLimit A M | x.val e = b.val e}) :=
  @nhds_hasBasis.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (b : NonUnitalModuleLeftLimit A M) → (e : Idempotent A) →
    {x : NonUnitalModuleLeftLimit A M | x.val e = b.val e} =
      {x : NonUnitalModuleLeftLimit A M | x - b ∈ coordinateKernel e} :=
  @coordinate_fiber_eq_translate.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] → IsIdempotented A →
    (b : NonUnitalModuleLeftLimit A M) →
    let := uniformSpace A M
    (𝓝 b).HasBasis (fun _ : Idempotent A => True)
      (fun e => {x : NonUnitalModuleLeftLimit A M | x - b ∈ coordinateKernel e}) :=
  @nhds_hasBasis_kernel.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (b : NonUnitalModuleLeftLimit A M) → (e : Idempotent A) →
    {x : NonUnitalModuleLeftLimit A M | x.val e = b.val e} =
      (fun k => b + k) '' (coordinateKernel (M := M) e : Set (NonUnitalModuleLeftLimit A M)) :=
  @coordinate_fiber_eq_image_add.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] → IsIdempotented A →
    (b : NonUnitalModuleLeftLimit A M) →
    let := uniformSpace A M
    (𝓝 b).HasBasis (fun _ : Idempotent A => True)
      (fun e => (fun k => b + k) ''
        (coordinateKernel (M := M) e : Set (NonUnitalModuleLeftLimit A M))) :=
  @nhds_hasBasis_translate.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] → IsIdempotented A →
    let := uniformSpace A M
    (𝓝 (0 : NonUnitalModuleLeftLimit A M)).HasBasis
      (fun _ : Idempotent A => True)
      (fun e => (coordinateKernel (M := M) e : Set (NonUnitalModuleLeftLimit A M))) :=
  @nhds_zero_hasBasis.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (e : Idempotent A) →
    @UniformContinuous (NonUnitalModuleLeftLimit A M) M (uniformSpace A M)
      (⊥ : UniformSpace M) (coordinate e) :=
  @uniformContinuous_coordinate.{uA, uM}

example : (A : Type uA) → (M : Type uM) →
    [NonUnitalRing A] → [AddCommGroup M] → [NonUnitalModule A M] →
    @IsUniformAddGroup (NonUnitalModuleLeftLimit A M) (uniformSpace A M) _ :=
  uniformAddGroup.{uA, uM}

example : (A : Type uA) → (M : Type uM) → [NonUnitalRing A] →
    UniformSpace (Idempotent A → M) :=
  discreteProductUniformSpace.{uA, uM}

example : (A : Type uA) → (M : Type uM) →
    [NonUnitalRing A] → [AddCommGroup M] → [NonUnitalModule A M] →
    UniformSpace.comap (fun x : NonUnitalModuleLeftLimit A M => x.val)
      (discreteProductUniformSpace A M) = uniformSpace A M :=
  uniformSpace_eq_product_comap.{uA, uM}

example : (A : Type uA) → (M : Type uM) →
    [NonUnitalRing A] → [AddCommGroup M] → [NonUnitalModule A M] →
    uniformSpace A M =
      @instUniformSpaceSubtype (Idempotent A → M) (· ∈ leftCompatibleFamilies A M)
        (discreteProductUniformSpace A M) :=
  uniformSpace_eq_subtype.{uA, uM}

example : (A : Type uA) → (M : Type uM) →
    [NonUnitalRing A] → [AddCommGroup M] → [NonUnitalModule A M] →
    @IsUniformEmbedding (NonUnitalModuleLeftLimit A M) (Idempotent A → M)
      (uniformSpace A M) (discreteProductUniformSpace A M) Subtype.val :=
  isUniformEmbedding_val.{uA, uM}

example : (A : Type uA) → (M : Type uM) →
    [NonUnitalRing A] → [AddCommGroup M] → [NonUnitalModule A M] →
    @T2Space (NonUnitalModuleLeftLimit A M) (uniformSpace A M).toTopologicalSpace :=
  hausdorff.{uA, uM}

example : (A : Type uA) → (M : Type uM) →
    [NonUnitalRing A] → [AddCommGroup M] → [NonUnitalModule A M] →
    UniformSpace.comap (canonical (A := A) (M := M)) (uniformSpace A M) =
      nonUnitalModuleUniformSpace A M :=
  comap_canonical.{uA, uM}

example : (A : Type uA) → (M : Type uM) →
    [NonUnitalRing A] → [AddCommGroup M] → [NonUnitalModule A M] →
    @IsUniformInducing M (NonUnitalModuleLeftLimit A M)
      (nonUnitalModuleUniformSpace A M) (uniformSpace A M) canonical :=
  isUniformInducing_canonical.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] → IsNondegenerate A M →
    @IsUniformEmbedding M (NonUnitalModuleLeftLimit A M)
      (nonUnitalModuleUniformSpace A M) (uniformSpace A M) canonical :=
  @isUniformEmbedding_canonical.{uA, uM}

example : {A : Type} → [NonUnitalRing A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] → IsNondegenerate A M →
    @IsUniformEmbedding M (NonUnitalModuleLeftLimit A M)
      (nonUnitalModuleUniformSpace A M) (uniformSpace A M) canonical :=
  @isUniformEmbedding_canonical.{0, 1}

example : {A : Type 1} → [NonUnitalRing A] →
    {M : Type} → [AddCommGroup M] → [NonUnitalModule A M] → IsNondegenerate A M →
    @IsUniformEmbedding M (NonUnitalModuleLeftLimit A M)
      (nonUnitalModuleUniformSpace A M) (uniformSpace A M) canonical :=
  @isUniformEmbedding_canonical.{1, 0}

end NonUnitalModuleLeftLimit
end Langlands.Algebra
