import Langlands.AlgebraicGeometry.RadicalLocalizationIdempotents
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Flat.TorsionFree

/-! # Connectedness across a reduced regular principal divisor -/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry

/-- On a dense subset, the closure of the trace of a clopen set recovers that clopen. -/
lemma closure_inter_dense_of_isClopen
    {T : Type u} [TopologicalSpace T] {D C : Set T}
    (hD : Dense D) (hC : IsClopen C) : closure (C ∩ D) = C := by
  exact (closure_minimal Set.inter_subset_left hC.isClosed).antisymm
    (hD.open_subset_closure_inter hC.isOpen)

/-- Local clopen extensions across a dense set glue by taking closure. -/
theorem isClopen_closure_of_local_extensions
    {T : Type u} [TopologicalSpace T] {D s : Set T} (hD : Dense D)
    (hlocal : ∀ x : T, ∃ V : Opens T, x ∈ V ∧
      ∃ C : Set V, IsClopen C ∧
        (Subtype.val : V → T) ⁻¹' s = C ∩ (Subtype.val ⁻¹' D)) :
    IsClopen (closure s) := by
  refine ⟨isClosed_closure, ?_⟩
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨V, hxV, C, hC, hCs⟩ := hlocal x
  have hdV : Dense ((Subtype.val : V → T) ⁻¹' D) :=
    hD.preimage V.isOpen.isOpenMap_subtype_val
  have heq : (Subtype.val : V → T) ⁻¹' closure s = C := by
    calc
      _ = closure ((Subtype.val : V → T) ⁻¹' s) :=
        IsOpenMap.preimage_closure_eq_closure_preimage
          (f := (Subtype.val : V → T)) V.isOpen.isOpenMap_subtype_val
          continuous_subtype_val s
      _ = closure (C ∩ (Subtype.val ⁻¹' D)) := congrArg closure hCs
      _ = C := closure_inter_dense_of_isClopen hdV hC
  refine ⟨Subtype.val '' C, ?_, V.isOpen.isOpenMap_subtype_val C hC.isOpen, ?_⟩
  · rintro y ⟨z, hz, rfl⟩
    exact (Set.ext_iff.mp heq z).mpr hz
  · exact ⟨⟨x, hxV⟩, (Set.ext_iff.mp heq ⟨x, hxV⟩).mp hx, rfl⟩

/-- A clopen subset of a basic open extends across a reduced regular principal divisor. -/
theorem exists_clopen_basicOpen_of_radical
    {A : Type u} [CommRing A] (t : A) (ht : t ∈ nonZeroDivisors A)
    (hrad : (Ideal.span {t}).IsRadical)
    {s : Set (PrimeSpectrum.basicOpen t)} (hs : IsClopen s) :
    ∃ C : Set (PrimeSpectrum A), IsClopen C ∧ (Subtype.val ⁻¹' C) = s := by
  let S := Localization.Away t
  let j := PrimeSpectrum.comap (algebraMap A S)
  have hrange : Set.range j = (PrimeSpectrum.basicOpen t : Set (PrimeSpectrum A)) :=
    PrimeSpectrum.localization_away_comap_range S t
  let q : PrimeSpectrum S → (PrimeSpectrum.basicOpen t) :=
    fun x => ⟨j x, by
      change j x ∈ (PrimeSpectrum.basicOpen t : Set (PrimeSpectrum A))
      rw [← hrange]
      exact Set.mem_range_self x⟩
  have hq : Continuous q := (PrimeSpectrum.continuous_comap _).subtype_mk _
  obtain ⟨C, hC, hCs⟩ := exists_clopen_of_away_radical t ht hrad (hs.preimage hq)
  refine ⟨C, hC, ?_⟩
  ext x
  have hx : x.1 ∈ Set.range j := by rw [hrange]; exact x.2
  obtain ⟨y, hy⟩ := hx
  have hqy : q y = x := Subtype.ext hy
  rw [← hqy]
  exact Set.ext_iff.mp hCs y

set_option backward.isDefEq.respectTransparency false in
/-- Every clopen of a regular reduced principal open in an affine scheme extends. -/
theorem exists_clopen_affine_basicOpen_of_radical
    (X : Scheme.{u}) [IsAffine X] (t : Γ(X, ⊤))
    (ht : t ∈ nonZeroDivisors Γ(X, ⊤)) (hrad : (Ideal.span {t}).IsRadical)
    {s : Set (X.basicOpen t)} (hs : IsClopen s) :
    ∃ C : Set X, IsClopen C ∧ (Subtype.val ⁻¹' C) = s := by
  let E := X.isoSpec.inv.homeomorph
  have hD : X.isoSpec.inv ⁻¹' (X.basicOpen t : Set X) =
      (PrimeSpectrum.basicOpen t : Set (PrimeSpectrum Γ(X, ⊤))) := by
    simpa only [IsAffineOpen.fromSpec_top, Scheme.Hom.coe_preimage] using
      congrArg (fun W : (Spec Γ(X, ⊤)).Opens => (W : Set (Spec Γ(X, ⊤))))
      ((isAffineOpen_top X).fromSpec_preimage_basicOpen t)
  let e : (PrimeSpectrum.basicOpen t) ≃ₜ (X.basicOpen t) :=
    E.sets hD.symm
  obtain ⟨C, hC, hCs⟩ := exists_clopen_basicOpen_of_radical t ht hrad
    (hs.preimage e.continuous)
  refine ⟨E.symm ⁻¹' C, hC.preimage E.symm.continuous, ?_⟩
  apply Set.preimage_injective.mpr e.surjective
  change (fun x : (PrimeSpectrum.basicOpen t) => E.symm (e x).1) ⁻¹' C = e ⁻¹' s
  have he : (fun x : (PrimeSpectrum.basicOpen t) => E.symm (e x).1) = Subtype.val := by
    funext x
    exact E.symm_apply_apply x.1
  rw [he]
  exact hCs

set_option backward.isDefEq.respectTransparency false in
/-- Affine clopen extensions of a dense principal open glue on an arbitrary scheme. -/
theorem exists_clopen_basicOpen_of_locally_radical
    (X : Scheme.{u}) (t : Γ(X, ⊤))
    (hDense : Dense (X.basicOpen t : Set X))
    (hreg : ∀ (U : X.Opens), IsAffineOpen U →
      U.ι.appTop t ∈ nonZeroDivisors Γ(U, ⊤))
    (hrad : ∀ (U : X.Opens), IsAffineOpen U →
      (Ideal.span {U.ι.appTop t}).IsRadical)
    {s : Set (X.basicOpen t)} (hs : IsClopen s) :
    ∃ C : Set X, IsClopen C ∧ (Subtype.val ⁻¹' C) = s := by
  let D := X.basicOpen t
  let s₀ : Set X := Subtype.val '' s
  have hlocal : ∀ x : X, ∃ U : Opens X, x ∈ U ∧
      ∃ C : Set U, IsClopen C ∧
        (Subtype.val : U → X) ⁻¹' s₀ = C ∩ (Subtype.val ⁻¹' (D : Set X)) := by
    intro x
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ (⊤ : X.Opens) from trivial)
    let : IsAffine U := hU
    have hDU (y : U) :
        y ∈ U.toScheme.basicOpen (U.ι.appTop t) ↔ y.1 ∈ D :=
      (congrArg (fun W : U.toScheme.Opens => y ∈ W)
        (U.ι.preimage_basicOpen_top t)).to_iff.symm
    let q : U.toScheme.basicOpen (U.ι.appTop t) → D :=
      fun y => ⟨y.1.1, (hDU y.1).mp y.2⟩
    have hq : Continuous q :=
      (U.ι.continuous.comp continuous_subtype_val).subtype_mk _
    obtain ⟨C, hC, hCs⟩ := exists_clopen_affine_basicOpen_of_radical U.toScheme
      (U.ι.appTop t) (hreg U hU) (hrad U hU) (hs.preimage hq)
    refine ⟨U, hxU, C, hC, ?_⟩
    ext y
    constructor
    · rintro ⟨z, hz, hzy⟩
      have hyD : y.1 ∈ D := hzy ▸ z.2
      have hyD' := (hDU y).mpr hyD
      have hqz : q ⟨y, hyD'⟩ = z := Subtype.ext hzy.symm
      refine ⟨?_, hyD⟩
      apply (Set.ext_iff.mp hCs ⟨y, hyD'⟩).mpr
      change q ⟨y, hyD'⟩ ∈ s
      rw [hqz]
      exact hz
    · rintro ⟨hyC, hyD⟩
      have hyD' := (hDU y).mpr hyD
      refine ⟨q ⟨y, hyD'⟩, ?_, rfl⟩
      exact (Set.ext_iff.mp hCs ⟨y, hyD'⟩).mp hyC
  refine ⟨closure s₀, isClopen_closure_of_local_extensions hDense hlocal, ?_⟩
  calc
    _ = closure ((Subtype.val : D → X) ⁻¹' s₀) :=
      IsOpenMap.preimage_closure_eq_closure_preimage
        (f := (Subtype.val : D → X)) D.isOpen.isOpenMap_subtype_val
        continuous_subtype_val s₀
    _ = closure s := by rw [Set.preimage_image_eq _ Subtype.val_injective]
    _ = s := hs.isClosed.closure_eq

set_option backward.isDefEq.respectTransparency false in
/-- A dense principal open with regular reduced local divisors preserves preconnectedness. -/
theorem preconnectedSpace_basicOpen_of_locally_radical
    (X : Scheme.{u}) [PreconnectedSpace X] (t : Γ(X, ⊤))
    (hDense : Dense (X.basicOpen t : Set X))
    (hreg : ∀ (U : X.Opens), IsAffineOpen U →
      U.ι.appTop t ∈ nonZeroDivisors Γ(U, ⊤))
    (hrad : ∀ (U : X.Opens), IsAffineOpen U →
      (Ideal.span {U.ι.appTop t}).IsRadical) :
    PreconnectedSpace (X.basicOpen t) := by
  refine preconnectedSpace_iff_clopen.mpr fun s hs => ?_
  obtain ⟨C, hC, hCs⟩ := exists_clopen_basicOpen_of_locally_radical X t hDense hreg hrad hs
  rcases (preconnectedSpace_iff_clopen.mp inferInstance) C hC with h | h
  · left
    simpa [h] using hCs.symm
  · right
    simpa [h] using hCs.symm

set_option backward.isDefEq.respectTransparency false in
/-- The closure of the ambient image of a principal-open clopen is clopen. -/
theorem isClopen_closure_image_basicOpen_of_locally_radical
    (X : Scheme.{u}) (t : Γ(X, ⊤))
    (hDense : Dense (X.basicOpen t : Set X))
    (hreg : ∀ (U : X.Opens), IsAffineOpen U →
      U.ι.appTop t ∈ nonZeroDivisors Γ(U, ⊤))
    (hrad : ∀ (U : X.Opens), IsAffineOpen U →
      (Ideal.span {U.ι.appTop t}).IsRadical)
    (s : Clopens ↥(X.basicOpen t)) :
    IsClopen (closure ((Subtype.val : X.basicOpen t → X) '' s.carrier)) := by
  obtain ⟨C, hC, hCs⟩ :=
    exists_clopen_basicOpen_of_locally_radical X t hDense hreg hrad s.isClopen
  change Subtype.val ⁻¹' C = s.carrier at hCs
  have himage : (Subtype.val : X.basicOpen t → X) '' s.carrier =
      C ∩ (X.basicOpen t : Set X) := by
    rw [← hCs, Set.image_preimage_eq_inter_range, Subtype.range_coe]
  rw [himage, closure_inter_dense_of_isClopen hDense hC]
  exact hC

/-- Extend a clopen from a dense regular reduced principal open by taking its closure. -/
def clopenExtensionOfLocallyRadical
    (X : Scheme.{u}) (t : Γ(X, ⊤))
    (hDense : Dense (X.basicOpen t : Set X))
    (hreg : ∀ (U : X.Opens), IsAffineOpen U →
      U.ι.appTop t ∈ nonZeroDivisors Γ(U, ⊤))
    (hrad : ∀ (U : X.Opens), IsAffineOpen U →
      (Ideal.span {U.ι.appTop t}).IsRadical)
    (s : Clopens ↥(X.basicOpen t)) : Clopens X :=
  ⟨closure ((Subtype.val : X.basicOpen t → X) '' s.carrier),
    isClopen_closure_image_basicOpen_of_locally_radical X t hDense hreg hrad s⟩

set_option backward.isDefEq.respectTransparency false in
/-- The clopen extension has exactly the original trace on the principal open. -/
@[simp] theorem clopenExtensionOfLocallyRadical_trace
    (X : Scheme.{u}) (t : Γ(X, ⊤))
    (hDense : Dense (X.basicOpen t : Set X))
    (hreg : ∀ (U : X.Opens), IsAffineOpen U →
      U.ι.appTop t ∈ nonZeroDivisors Γ(U, ⊤))
    (hrad : ∀ (U : X.Opens), IsAffineOpen U →
      (Ideal.span {U.ι.appTop t}).IsRadical)
    (s : Clopens ↥(X.basicOpen t)) :
    (Subtype.val : X.basicOpen t → X) ⁻¹'
      (clopenExtensionOfLocallyRadical X t hDense hreg hrad s : Set X) = s.carrier := by
  change (Subtype.val : X.basicOpen t → X) ⁻¹'
    closure ((Subtype.val : X.basicOpen t → X) '' s.carrier) = _
  rw [IsOpenMap.preimage_closure_eq_closure_preimage
    (f := (Subtype.val : X.basicOpen t → X))
    (X.basicOpen t).isOpen.isOpenMap_subtype_val continuous_subtype_val,
    Set.preimage_image_eq _ Subtype.val_injective]
  exact s.isClosed.closure_eq

end Langlands.AlgebraicGeometry
