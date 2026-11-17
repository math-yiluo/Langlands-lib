import Langlands.GroupScheme.IntegralModel.Smoothening.SmoothSections
import Langlands.CommutativeAlgebra.SmoothDVRUniformizerDivision
import Langlands.AlgebraicGeometry.FlatReducedDvrConnectedness
import Mathlib.AlgebraicGeometry.Fiber

/-! # Functions on a smooth DVR scheme and its special fibre -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme.IntegralModel.Smoothening

namespace Langlands.AlgebraicGeometry.SmoothDvrGlobalSections

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (Y : Over (Spec (CommRingCat.of R)))

/-- A base scalar as an actual global function. -/
def scalar (r : R) : Γ(Y.left, ⊤) :=
  Y.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)

omit [IsDomain R] [IsDiscreteValuationRing R] in
lemma scalar_eq_algebraMap (r : R) :
    scalar Y r = algebraMap R ((algΓ (CommRingCat.of R)).obj Y).unop r := rfl

/-- The basic open of a uniformizer is the complement of the special fibre. -/
lemma mem_basicOpen_scalar_iff {π : R} (hπ : Irreducible π) (x : Y.left) :
    x ∈ Y.left.basicOpen (scalar Y π) ↔ Y.hom x ≠ IsLocalRing.closedPoint R := by
  rw [scalar, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
  change π ∉ (Y.hom x).asIdeal ↔ _
  rcases FlatReducedDvrConnectedness.point_eq_generic_or_closed R (Y.hom x) with h | h
  · rw [h]
    refine ⟨fun _ => ?_, fun _ => ?_⟩
    · intro heq
      exact IsDiscreteValuationRing.not_a_field R (congrArg PrimeSpectrum.asIdeal heq).symm
    · simpa only [Ideal.mem_bot] using hπ.ne_zero
  · rw [h]
    have hmem : π ∈ IsLocalRing.maximalIdeal R :=
      (IsLocalRing.mem_maximalIdeal π).mpr hπ.not_isUnit
    exact ⟨fun hn => (hn hmem).elim, fun hn => (hn rfl).elim⟩

/-- A function on an affine open that vanishes at every special-fibre point
is divisible by the restricted uniformizer. -/
theorem exists_eq_scalar_mul_of_isAffineOpen [Smooth Y.hom]
    {π : R} (hπ : Irreducible π) (U : Y.left.affineOpens) (f : Γ(Y.left, U.1))
    (hf : ∀ x ∈ U.1, Y.hom x = IsLocalRing.closedPoint R →
      x ∉ Y.left.basicOpen f) :
    ∃ g : Γ(Y.left, U.1), f = topRes U.1 (scalar Y π) * g := by
  let := openAlgebra Y U.1
  have := smooth_openAlgebra Y U
  have hscalar : algebraMap R Γ(Y.left, U.1) π = topRes U.1 (scalar Y π) := rfl
  rw [← hscalar]
  change algebraMap R Γ(Y.left, U.1) π ∣ f
  apply Langlands.CommutativeAlgebra.SmoothDVRUniformizerDivision.dvd_of_forall_mem_prime hπ
  intro P hP hπP
  let q : PrimeSpectrum Γ(Y.left, U.1) := ⟨P, hP⟩
  let x := U.2.fromSpec q
  have hxU : x ∈ U.1 := U.2.range_fromSpec.le ⟨q, rfl⟩
  have hmem : ∀ a : Γ(Y.left, U.1), x ∈ Y.left.basicOpen a ↔ a ∉ P := fun a => by
    change q ∈ U.2.fromSpec ⁻¹ᵁ Y.left.basicOpen a ↔ _
    rw [U.2.fromSpec_preimage_basicOpen]
    rfl
  have hxs : Y.hom x = IsLocalRing.closedPoint R := by
    by_contra hne
    have hxb : x ∈ Y.left.basicOpen (scalar Y π) :=
      (mem_basicOpen_scalar_iff Y hπ x).mpr hne
    have hxr : x ∈ Y.left.basicOpen (topRes U.1 (scalar Y π)) := by
      rw [topRes, Scheme.basicOpen_res]
      exact ⟨hxU, hxb⟩
    rw [hmem, ← hscalar] at hxr
    exact hxr hπP
  by_contra hfP
  exact hf x hxU hxs ((hmem f).mpr hfP)

/-- A global function vanishing at every special-fibre point is globally
divisible by the uniformizer; the local quotients glue by flatness. -/
theorem exists_eq_scalar_mul_of_vanishing [Smooth Y.hom]
    {π : R} (hπ : Irreducible π) (f : Γ(Y.left, ⊤))
    (hf : ∀ x : Y.left, Y.hom x = IsLocalRing.closedPoint R →
      x ∉ Y.left.basicOpen f) :
    ∃ g : Γ(Y.left, ⊤), f = scalar Y π * g := by
  refine exists_eq_mul_of_affine (scalar Y π) f ?_ ?_
  · intro U t ht
    exact eq_zero_of_algebraMap_mul_eq_zero Y hπ.ne_zero U.1 t ht
  · intro U
    apply exists_eq_scalar_mul_of_isAffineOpen Y hπ U
    intro x hx hxs hxb
    rw [topRes, Scheme.basicOpen_res] at hxb
    exact hf x hxs hxb.2

/-- Restriction to the actual special fibre detects pointwise vanishing there. -/
theorem specialFiber_appTop_eq_zero_iff [Smooth Y.hom] (f : Γ(Y.left, ⊤)) :
    (Y.hom.fiberι (IsLocalRing.closedPoint R)).appTop f = 0 ↔
      ∀ x : Y.left, Y.hom x = IsLocalRing.closedPoint R →
        x ∉ Y.left.basicOpen f := by
  let s : Spec (CommRingCat.of R) := IsLocalRing.closedPoint R
  let q := Y.hom.fiberι s
  have : Smooth (Y.hom.fiberToSpecResidueField s) :=
    MorphismProperty.of_isPullback (CategoryTheory.IsPullback.of_hasPullback _ _) inferInstance
  have : IsReduced (Y.hom.fiber s) :=
    SmoothReducedProof.isReduced_of_smooth_over_field
      ((Spec (CommRingCat.of R)).residueField s) _ (Y.hom.fiberToSpecResidueField s)
  constructor
  · intro hf x hxs hxf
    have hxq : x ∈ Set.range q := by
      rw [Y.hom.range_fiberι s]
      exact hxs
    obtain ⟨y, rfl⟩ := hxq
    have hy : y ∈ (Y.hom.fiber s).basicOpen (q.appTop f) := by
      rw [← Scheme.preimage_basicOpen_top]
      exact hxf
    rw [show q.appTop f = 0 from hf, Scheme.basicOpen_zero] at hy
    exact hy
  · intro hf
    apply eq_zero_of_basicOpen_eq_bot
    rw [← Scheme.preimage_basicOpen_top]
    apply le_bot_iff.mp
    intro y hy
    exact hf (q y) ((Y.hom.range_fiberι s).le ⟨y, rfl⟩) hy

/-- A uniformizer restricts to zero on the actual special fibre. -/
lemma specialFiber_appTop_scalar [Smooth Y.hom] {π : R} (hπ : Irreducible π) :
    (Y.hom.fiberι (IsLocalRing.closedPoint R)).appTop (scalar Y π) = 0 := by
  apply (specialFiber_appTop_eq_zero_iff Y _).mpr
  intro x hxs hxb
  exact (mem_basicOpen_scalar_iff Y hπ x).mp hxb hxs

/-- The actual special-fibre restriction map has precisely the uniformizer ideal
as its kernel. -/
theorem ker_specialFiber_appTop [Smooth Y.hom] {π : R} (hπ : Irreducible π) :
    RingHom.ker (Y.hom.fiberι (IsLocalRing.closedPoint R)).appTop.hom =
      Ideal.span {scalar Y π} := by
  ext f
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  constructor
  · intro hf
    exact exists_eq_scalar_mul_of_vanishing Y hπ f
      ((specialFiber_appTop_eq_zero_iff Y f).mp hf)
  · rintro ⟨g, rfl⟩
    rw [map_mul, specialFiber_appTop_scalar Y hπ, zero_mul]

/-- The natural map from global functions modulo the uniformizer to the actual
special-fibre global functions. -/
def specialFiberSectionMap [Smooth Y.hom] {π : R} (hπ : Irreducible π) :
    (Γ(Y.left, ⊤) ⧸ Ideal.span {scalar Y π}) →+*
      Γ(Y.hom.fiber (IsLocalRing.closedPoint R), ⊤) :=
  Ideal.Quotient.lift _ (Y.hom.fiberι (IsLocalRing.closedPoint R)).appTop.hom
    (by rw [← ker_specialFiber_appTop Y hπ]; exact fun _ h => h)

@[simp]
theorem specialFiberSectionMap_mk [Smooth Y.hom] {π : R} (hπ : Irreducible π)
    (f : Γ(Y.left, ⊤)) :
    specialFiberSectionMap Y hπ (Ideal.Quotient.mk _ f) =
      (Y.hom.fiberι (IsLocalRing.closedPoint R)).appTop f := rfl

/-- Global functions modulo the uniformizer inject into the functions on the
actual special fibre, without an affine-source hypothesis. -/
theorem specialFiberSectionMap_injective [Smooth Y.hom] {π : R} (hπ : Irreducible π) :
    Function.Injective (specialFiberSectionMap Y hπ) := by
  apply RingHom.lift_injective_of_ker_le_ideal
  rw [ker_specialFiber_appTop Y hπ]

end Langlands.AlgebraicGeometry.SmoothDvrGlobalSections
