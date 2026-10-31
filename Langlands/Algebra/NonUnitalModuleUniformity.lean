import Langlands.Algebra.NonUnitalModule
import Mathlib.Topology.Algebra.IsUniformGroup.Constructions
import Mathlib.Algebra.Group.Subgroup.Lattice

/-!
# Residual-coordinate uniformity on original nonunital modules

Renard I.1.4, printed p.9/PDF15. The actual original left coordinates
define the uniformity; all vector operations retain the original action.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra

open Filter Set
open scoped Uniformity Topology

universe uA uM

variable {A : Type uA} [NonUnitalRing A]
  {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]

namespace Idempotent

/-- The actual original additive coordinate `m ↦ e • m`. -/
def leftActionCoordinate (e : Idempotent A) : M →+ M where
  toFun m := (e : A) • m
  map_zero' := smul_zero _
  map_add' m n := smul_add (e : A) m n

@[simp] theorem leftActionCoordinate_apply (e : Idempotent A) (m : M) :
    e.leftActionCoordinate m = (e : A) • m := rfl

/-- The source's `(1-e) • M`, defined without an original identity. -/
def leftActionKernel (e : Idempotent A) : AddSubgroup M :=
  (e.leftActionCoordinate (M := M)).ker

@[simp] theorem mem_leftActionKernel (e : Idempotent A) (m : M) :
    m ∈ e.leftActionKernel ↔ (e : A) • m = 0 := Iff.rfl

theorem mem_leftActionKernel_iff_residual (e : Idempotent A) (m : M) :
    m ∈ e.leftActionKernel ↔ ∃ n : M, m = n - (e : A) • n := by
  constructor
  · intro hm
    exact ⟨m, by rw [(mem_leftActionKernel e m).mp hm, sub_zero]⟩
  · rintro ⟨n, rfl⟩
    change (e : A) • (n - (e : A) • n) = 0
    rw [smul_sub, ← mul_smul, e.property.eq, sub_self]

theorem leftActionKernel_antitone :
    Antitone (leftActionKernel (A := A) (M := M)) := by
  intro e f hef m hm
  have h := congrArg (fun n : M => (e : A) • n) (mem_leftActionKernel f m |>.mp hm)
  change (e : A) • m = 0
  simpa only [← mul_smul, ((le_iff_mul e f).mp hef).2, smul_zero] using h

/-- Equality of the actual left coordinates on original vectors. -/
def leftActionEntourage (e : Idempotent A) : Set (M × M) :=
  {p | (e : A) • p.1 = (e : A) • p.2}

@[simp] theorem mem_leftActionEntourage (e : Idempotent A) (m n : M) :
    (m, n) ∈ e.leftActionEntourage ↔ (e : A) • m = (e : A) • n := Iff.rfl

theorem leftActionEntourage_antitone :
    Antitone (leftActionEntourage (A := A) (M := M)) := by
  intro e f hef p hp
  have h := congrArg (fun m : M => (e : A) • m) hp
  change (e : A) • p.1 = (e : A) • p.2
  simpa only [← mul_smul, ((le_iff_mul e f).mp hef).2] using h

theorem leftActionEntourage_eq_kernel (e : Idempotent A) :
    e.leftActionEntourage =
      {p : M × M | p.1 - p.2 ∈ e.leftActionKernel} := by
  ext p
  change ((e : A) • p.1 = (e : A) • p.2) ↔ (e : A) • (p.1 - p.2) = 0
  rw [smul_sub, sub_eq_zero]

end Idempotent

theorem nonUnitalModule_kernel_common_refinement (hA : IsIdempotented A)
    (e f : Idempotent A) :
    ∃ g : Idempotent A, e ≤ g ∧ f ≤ g ∧
      g.leftActionKernel (M := M) ≤ e.leftActionKernel ⊓ f.leftActionKernel := by
  classical
  obtain ⟨g, hg⟩ := hA.finite_upper_bound {e, f}
  have he : e ≤ g := hg e (by simp)
  have hf : f ≤ g := hg f (by simp)
  exact ⟨g, he, hf, le_inf (Idempotent.leftActionKernel_antitone he)
    (Idempotent.leftActionKernel_antitone hf)⟩

theorem nonUnitalModule_entourage_directed (hA : IsIdempotented A) :
    Directed (· ≥ ·) (Idempotent.leftActionEntourage (A := A) (M := M)) := by
  intro e f
  obtain ⟨g, he, hf, _⟩ := nonUnitalModule_kernel_common_refinement (M := M) hA e f
  exact ⟨g, Idempotent.leftActionEntourage_antitone he,
    Idempotent.leftActionEntourage_antitone hf⟩

/-- The actual infimum of discrete original left-coordinate pullbacks.
Users install this definition locally on the original vector carrier. -/
@[instance_reducible]
def nonUnitalModuleUniformSpace (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M] : UniformSpace M :=
  ⨅ e : Idempotent A,
    UniformSpace.comap (fun m : M => (e : A) • m) (⊥ : UniformSpace M)

theorem nonUnitalModule_uniformity :
    𝓤[nonUnitalModuleUniformSpace A M] =
      ⨅ e : Idempotent A, 𝓟 (e.leftActionEntourage (M := M)) := by
  rw [nonUnitalModuleUniformSpace, iInf_uniformity]
  congr 1
  funext e
  rw [uniformity_comap, bot_uniformity, comap_principal]
  rfl

theorem nonUnitalModule_uniformity_hasBasis (hA : IsIdempotented A) :
    (𝓤[nonUnitalModuleUniformSpace A M]).HasBasis
      (fun _ : Idempotent A => True) Idempotent.leftActionEntourage := by
  let : Nonempty (Idempotent A) := ⟨⟨0, IsIdempotentElem.zero⟩⟩
  rw [nonUnitalModule_uniformity]
  exact hasBasis_iInf_principal (nonUnitalModule_entourage_directed (M := M) hA)

theorem nonUnitalModule_nhds_hasBasis (hA : IsIdempotented A) (b : M) :
    let := nonUnitalModuleUniformSpace A M
    (𝓝 b).HasBasis (fun _ : Idempotent A => True)
      (fun e => {m : M | (e : A) • (m - b) = 0}) := by
  let := nonUnitalModuleUniformSpace A M
  have h := nhds_basis_uniformity (nonUnitalModule_uniformity_hasBasis (M := M) hA) (x := b)
  simpa only [Idempotent.leftActionEntourage, mem_ofPred_eq,
    smul_sub, sub_eq_zero] using h

theorem nonUnitalModule_fiber_eq_image_add (b : M) (e : Idempotent A) :
    {m : M | (e : A) • (m - b) = 0} =
      (fun k => b + k) '' (e.leftActionKernel (M := M) : Set M) := by
  rw [image_add_left]
  ext m
  change (e : A) • (m - b) = 0 ↔ (e : A) • (-b + m) = 0
  rw [neg_add_eq_sub]

theorem nonUnitalModule_nhds_hasBasis_translate (hA : IsIdempotented A) (b : M) :
    let := nonUnitalModuleUniformSpace A M
    (𝓝 b).HasBasis (fun _ : Idempotent A => True)
      (fun e => (fun k => b + k) '' (e.leftActionKernel (M := M) : Set M)) := by
  let := nonUnitalModuleUniformSpace A M
  simpa only [nonUnitalModule_fiber_eq_image_add] using nonUnitalModule_nhds_hasBasis hA b

theorem nonUnitalModule_nhds_zero_hasBasis (hA : IsIdempotented A) :
    let := nonUnitalModuleUniformSpace A M
    (𝓝 (0 : M)).HasBasis (fun _ : Idempotent A => True)
      (fun e => (e.leftActionKernel (M := M) : Set M)) := by
  let := nonUnitalModuleUniformSpace A M
  change (𝓝 (0 : M)).HasBasis (fun _ : Idempotent A => True)
    (fun e => {m : M | (e : A) • m = 0})
  simpa only [sub_zero] using nonUnitalModule_nhds_hasBasis hA (0 : M)

theorem nonUnitalModule_uniformContinuous_coordinate (e : Idempotent A) :
    @UniformContinuous M M (nonUnitalModuleUniformSpace A M)
      (⊥ : UniformSpace M) (e.leftActionCoordinate (M := M)) := by
  rw [uniformContinuous_iff_le_comap]
  exact iInf_le _ e

/-- The original additive commutative group is uniform for the actual constructed uniformity. -/
theorem nonUnitalModule_uniformAddGroup (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M] :
    @IsUniformAddGroup M (nonUnitalModuleUniformSpace A M) _ := by
  change @IsUniformAddGroup M
    (⨅ e : Idempotent A,
      UniformSpace.comap (fun m : M => (e : A) • m) (⊥ : UniformSpace M)) _
  apply isUniformAddGroup_iInf
  intro e
  let : UniformSpace M := ⊥
  exact IsUniformAddGroup.comap (e.leftActionCoordinate (M := M))

/-- Original nondegeneracy lets the left coordinates distinguish original vectors. -/
theorem nonUnitalModule_coordinatesSeparate (hM : IsNondegenerate A M) (m n : M) :
    (∀ e : Idempotent A, (e : A) • m = (e : A) • n) ↔ m = n := by
  constructor
  · intro h
    obtain ⟨e, he⟩ := hM (m - n)
    have hz : (e : A) • (m - n) = 0 := by rw [smul_sub, h e, sub_self]
    exact sub_eq_zero.mp (he.symm.trans hz)
  · rintro rfl _
    rfl

theorem nonUnitalModule_hausdorff (hA : IsIdempotented A) (hM : IsNondegenerate A M) :
    @T2Space M (nonUnitalModuleUniformSpace A M).toTopologicalSpace := by
  let := nonUnitalModuleUniformSpace A M
  have hb := nonUnitalModule_uniformity_hasBasis (M := M) hA
  have : T0Space M := t0Space_iff_uniformity.mpr (by
    intro m n hmn
    apply (nonUnitalModule_coordinatesSeparate hM m n).mp
    intro e
    exact hmn (e.leftActionEntourage (M := M)) (hb.mem_of_mem (i := e) trivial))
  infer_instance

/-! Complete unapplied interfaces retain independent original ring/vector universes. -/

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (e : Idempotent A) → M →+ M :=
  @Idempotent.leftActionCoordinate.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (e : Idempotent A) → AddSubgroup M :=
  @Idempotent.leftActionKernel.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (e : Idempotent A) → (m : M) →
    m ∈ e.leftActionKernel ↔ ∃ n : M, m = n - (e : A) • n :=
  @Idempotent.mem_leftActionKernel_iff_residual.{uA, uM}

example : (A : Type uA) → (M : Type uM) →
    [NonUnitalRing A] → [AddCommGroup M] → [NonUnitalModule A M] → UniformSpace M :=
  nonUnitalModuleUniformSpace.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] → IsIdempotented A →
    (𝓤[nonUnitalModuleUniformSpace A M]).HasBasis
      (fun _ : Idempotent A => True) Idempotent.leftActionEntourage :=
  @nonUnitalModule_uniformity_hasBasis.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    IsIdempotented A → (b : M) →
    let := nonUnitalModuleUniformSpace A M
    (𝓝 b).HasBasis (fun _ : Idempotent A => True)
      (fun e => (fun k => b + k) '' (e.leftActionKernel (M := M) : Set M)) :=
  @nonUnitalModule_nhds_hasBasis_translate.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] → IsIdempotented A →
    let := nonUnitalModuleUniformSpace A M
    (𝓝 (0 : M)).HasBasis (fun _ : Idempotent A => True)
      (fun e => (e.leftActionKernel (M := M) : Set M)) :=
  @nonUnitalModule_nhds_zero_hasBasis.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (e : Idempotent A) →
    @UniformContinuous M M (nonUnitalModuleUniformSpace A M)
      (⊥ : UniformSpace M) (e.leftActionCoordinate (M := M)) :=
  @nonUnitalModule_uniformContinuous_coordinate.{uA, uM}

example : (A : Type uA) → (M : Type uM) →
    [NonUnitalRing A] → [AddCommGroup M] → [NonUnitalModule A M] →
    @IsUniformAddGroup M (nonUnitalModuleUniformSpace A M) _ :=
  nonUnitalModule_uniformAddGroup.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    IsNondegenerate A M → (m n : M) →
    (∀ e : Idempotent A, (e : A) • m = (e : A) • n) ↔ m = n :=
  @nonUnitalModule_coordinatesSeparate.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    IsIdempotented A → IsNondegenerate A M →
    @T2Space M (nonUnitalModuleUniformSpace A M).toTopologicalSpace :=
  @nonUnitalModule_hausdorff.{uA, uM}

example : {A : Type} → [NonUnitalRing A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    IsIdempotented A → IsNondegenerate A M →
    @T2Space M (nonUnitalModuleUniformSpace A M).toTopologicalSpace :=
  @nonUnitalModule_hausdorff.{0, 1}

example : {A : Type 1} → [NonUnitalRing A] →
    {M : Type} → [AddCommGroup M] → [NonUnitalModule A M] →
    IsIdempotented A → IsNondegenerate A M →
    @T2Space M (nonUnitalModuleUniformSpace A M).toTopologicalSpace :=
  @nonUnitalModule_hausdorff.{1, 0}

end Langlands.Algebra
