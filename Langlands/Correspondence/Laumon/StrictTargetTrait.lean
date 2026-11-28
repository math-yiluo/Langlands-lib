import Langlands.Correspondence.Laumon.Completion
import Langlands.Correspondence.Laumon.EndRingDvr
import WeilConjectures.SixFunctors.NearbyCycles.StrictlyHenselianTrait

/-!
# The strict target trait and its Galois action

Use the integral closure of the end ring in the chosen maximal unramified subextension,
with the geometric generic point and the special point given by reduction modulo `t`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.Henniart.Laumon

open AlgebraicGeometry.ProEtale.CondensedRing

variable (k : Type u) [Field k]

/-- The uniformizer `t` of the strict target trait, the image of the uniformizer of the end
trait. -/
def strictUniformizer : endStrictRing k :=
  endStrictRingHom k (endUniformizer k .zero)

/-- The ideal `(t)` of the strict target trait. -/
def strictMaximalIdeal : Ideal (endStrictRing k) :=
  Ideal.span {strictUniformizer k}

/-- The residue ring `R^nr / (t)` of the strict target trait. -/
abbrev strictResidueRing : Type u :=
  endStrictRing k ⧸ strictMaximalIdeal k

/-- The residue map `R^nr → R^nr / (t)`. -/
def strictResidue : endStrictRing k →+* strictResidueRing k :=
  Ideal.Quotient.mk _

/-- The map of the original constants into the strict residue ring. -/
def strictResidueBaseHom : k →+* strictResidueRing k :=
  (strictResidue k).comp ((endStrictRingHom k).comp (endConstantHom k))

/-- Reduction on the strict target extends reduction on the end trait. -/
theorem strictResidue_comp_endStrictRingHom :
    (strictResidue k).comp (endStrictRingHom k) =
      (strictResidueBaseHom k).comp (endResidue k) := by
  refine RingHom.ext fun r => Ideal.Quotient.eq.mpr ?_
  have hdvd : endUniformizer k .zero ∣ r - endConstantHom k (endResidue k r) := by
    rw [endRing_dvd_iff, endPowerSeriesHom_endUniformizer, PowerSeries.X_dvd_iff,
      RingHom.map_sub, RingHom.map_sub, endPowerSeriesHom_endConstantHom, PowerSeries.constantCoeff_C,
      ← endResidue_apply, sub_self]
  have h := map_dvd (endStrictRingHom k) hdvd
  exact Ideal.mem_span_singleton.mpr ((RingHom.map_sub (endStrictRingHom k) _ _) ▸ h)

/-- The geometric generic point of the strict target trait: `R^nr ⊂ K^nr ⊂ Ω_s`. -/
def strictGenericHom : endStrictRing k →+* endGenericClosure k :=
  (endUnramifiedField k).toSubfield.subtype.comp (endStrictRing k).subtype

private def constantsInUnramified : endConstants k →+* endUnramifiedField k :=
  (endConstants k).subtype.codRestrict (endUnramifiedField k).toSubfield
    fun c => IntermediateField.subset_adjoin _ _ c.2

private theorem constantsInUnramified_mem (c : endConstants k) :
    constantsInUnramified k c ∈ endStrictRing k := by
  have hc : RingHom.IsIntegralElem
      ((endUnramifiedInclusion k).comp ((endRing k).subtype.comp (endConstantHom k)))
      (constantsInUnramified k c) := by
    obtain ⟨p, hp, hpc⟩ := c.2
    refine ⟨p, hp, (endUnramifiedField k).toSubfield.subtype.injective ?_⟩
    rw [Polynomial.hom_eval₂, RingHom.map_zero]
    exact hpc
  exact RingHom.isIntegralElem.of_comp (endConstantHom k)
    ((endUnramifiedInclusion k).comp (endRing k).subtype) hc

/-- The geometric constants included in the strict end ring. -/
def strictConstantsHom : endConstants k →+* endStrictRing k :=
  (constantsInUnramified k).codRestrict (endStrictRing k) (constantsInUnramified_mem k)

/-- Reduction of the geometric constants. -/
def strictConstantsResidue : endConstants k →+* strictResidueRing k :=
  (strictResidue k).comp (strictConstantsHom k)

/-- The pointed strict target trait. -/
def strictTargetTrait :
    NearbyCyclesModel (Spec (.of (endGenericClosure k))) (Spec (.of (strictResidueRing k))) :=
  NearbyCyclesModel.ofTrait (strictGenericHom k) (strictResidue k)

section Galois

variable {k}

theorem galois_comp_constants (σ : Gal(endGenericClosure k/endField k)) :
    (σ : endGenericClosure k →+* endGenericClosure k).comp
        ((algebraMap (endField k) (endGenericClosure k)).comp
          ((endRing k).subtype.comp (endConstantHom k))) =
      (algebraMap (endField k) (endGenericClosure k)).comp
          ((endRing k).subtype.comp (endConstantHom k)) :=
  RingHom.ext fun _ => σ.commutes _

theorem galois_mem_endConstants (σ : Gal(endGenericClosure k/endField k))
    {c : endGenericClosure k} (hc : c ∈ endConstants k) : σ c ∈ endConstants k := by
  obtain ⟨p, hp, hpc⟩ := hc
  refine ⟨p, hp, ?_⟩
  change Polynomial.eval₂ ((algebraMap (endField k) (endGenericClosure k)).comp
    ((endRing k).subtype.comp (endConstantHom k))) (σ c) p = 0
  change Polynomial.eval₂ ((algebraMap (endField k) (endGenericClosure k)).comp
    ((endRing k).subtype.comp (endConstantHom k))) c p = 0 at hpc
  have h := congrArg (σ : endGenericClosure k →+* endGenericClosure k) hpc
  rw [Polynomial.hom_eval₂, galois_comp_constants, map_zero] at h
  exact h

theorem galois_mem_endUnramifiedField (σ : Gal(endGenericClosure k/endField k))
    {x : endGenericClosure k} (hx : x ∈ endUnramifiedField k) :
    σ x ∈ endUnramifiedField k := by
  have h1 : σ x ∈ (endUnramifiedField k).map σ.toAlgHom := ⟨x, hx, rfl⟩
  rw [endUnramifiedField, IntermediateField.adjoin_map] at h1
  refine IntermediateField.adjoin_le_iff.mpr ?_ h1
  rintro _ ⟨c, hc, rfl⟩
  exact IntermediateField.subset_adjoin _ _ (galois_mem_endConstants σ hc)

/-- The restriction of `σ` to the maximal unramified subextension. -/
def unramifiedGalois (σ : Gal(endGenericClosure k/endField k)) :
    endUnramifiedField k →+* endUnramifiedField k :=
  (σ.toRingHom.comp (endUnramifiedField k).toSubfield.subtype).codRestrict
    (endUnramifiedField k).toSubalgebra.toSubsemiring
    fun x => galois_mem_endUnramifiedField σ x.2

theorem galois_mem_endStrictRing (σ : Gal(endGenericClosure k/endField k))
    {x : endUnramifiedField k} (hx : x ∈ endStrictRing k) :
    unramifiedGalois σ x ∈ endStrictRing k :=
  letI := endStrictAlgebra k
  (isIntegral_algHom_iff
    ({ unramifiedGalois σ with
      commutes' := fun r => Subtype.ext (σ.commutes ((r : endRing k) : endField k)) } :
        endUnramifiedField k →ₐ[endRing k] endUnramifiedField k)
    (unramifiedGalois σ).injective (x := x)).mpr hx

/-- The restriction of `σ` to the strict target trait. -/
def strictRingGalois (σ : Gal(endGenericClosure k/endField k)) :
    endStrictRing k →+* endStrictRing k :=
  ((unramifiedGalois σ).comp (endStrictRing k).subtype).codRestrict (endStrictRing k)
    fun x => galois_mem_endStrictRing σ x.2

theorem strictRingGalois_endStrictRingHom (σ : Gal(endGenericClosure k/endField k))
    (r : endRing k) : strictRingGalois σ (endStrictRingHom k r) = endStrictRingHom k r :=
  Subtype.ext (Subtype.ext (σ.commutes ((r : endRing k) : endField k)))

theorem strictRingGalois_comp_endStrictRingHom (σ : Gal(endGenericClosure k/endField k)) :
    (strictRingGalois σ).comp (endStrictRingHom k) = endStrictRingHom k :=
  RingHom.ext (strictRingGalois_endStrictRingHom σ)

theorem strictMaximalIdeal_le_comap (σ : Gal(endGenericClosure k/endField k)) :
    strictMaximalIdeal k ≤ (strictMaximalIdeal k).comap (strictRingGalois σ) := by
  refine Ideal.span_le.mpr ?_
  rintro _ rfl
  change strictRingGalois σ (endStrictRingHom k (endUniformizer k .zero)) ∈ strictMaximalIdeal k
  rw [strictRingGalois_endStrictRingHom]
  exact Ideal.subset_span rfl

/-- The residue automorphism of `σ`. -/
def strictResidueGalois (σ : Gal(endGenericClosure k/endField k)) :
    strictResidueRing k →+* strictResidueRing k :=
  Ideal.quotientMap (strictMaximalIdeal k) (strictRingGalois σ) (strictMaximalIdeal_le_comap σ)

theorem strictResidueGalois_comp (σ : Gal(endGenericClosure k/endField k)) :
    (strictResidueGalois σ).comp (strictResidue k) =
      (strictResidue k).comp (strictRingGalois σ) :=
  RingHom.ext fun x => Ideal.quotientMap_mk (I := strictMaximalIdeal k) (J := strictMaximalIdeal k)
    (H := strictMaximalIdeal_le_comap σ) (x := x)

theorem strictResidueGalois_comp_baseHom (σ : Gal(endGenericClosure k/endField k)) :
    (strictResidueGalois σ).comp (strictResidueBaseHom k) = strictResidueBaseHom k :=
  RingHom.ext fun c =>
    let r : endRing k := endConstantHom k c
    (congrArg (fun h : endStrictRing k →+* strictResidueRing k => h (endStrictRingHom k r))
      (strictResidueGalois_comp σ)).trans
      (congrArg (strictResidue k) (strictRingGalois_endStrictRingHom σ r))

/-- The automorphism of the pointed strict target trait. -/
def strictTargetTraitAut (σ : Gal(endGenericClosure k/endField k)) :
    (strictTargetTrait k).Hom (strictTargetTrait k) (Spec.map (CommRingCat.ofHom σ.toRingHom))
      (Spec.map (CommRingCat.ofHom (strictResidueGalois σ))) :=
  NearbyCyclesModel.ofTraitHom (strictGenericHom k) (strictResidue k) (strictGenericHom k)
    (strictResidue k) (strictRingGalois σ) σ.toRingHom (strictResidueGalois σ)
    (RingHom.ext fun _ => rfl) (strictResidueGalois_comp σ)

end Galois

attribute [local instance] Langlands.LocalField.Laurent.valuativeRel

open Langlands.LocalGalois.SepClosed Langlands.Weil.Local.SepClosed in
/-- The strict end ring is a strictly henselian DVR of fraction field `K^nr`, generated over the
end ring by the geometric constants. Reduction identifies the constants with the residue ring.
The Galois restriction has kernel inertia and gives the completed residue action and Weil degree. -/
def StrictTargetTraitGaloisStatement : Prop :=
  ∀ (k : Type u) [Field k] [Finite k],
    (∃ h : IsStrictlyHenselianLocalRing (endStrictRing k),
      IsDiscreteValuationRing (endStrictRing k) ∧
        @IsLocalRing.maximalIdeal (endStrictRing k) _
            h.toHenselianLocalRing.toIsLocalRing = strictMaximalIdeal k) ∧
    endStrictRing k = Subring.closure
      (Set.range ((endUnramifiedInclusion k).comp (endRing k).subtype) ∪
        {x : endUnramifiedField k | (x : endGenericClosure k) ∈ endConstants k}) ∧
    (∀ z : endUnramifiedField k, ∃ a b : endStrictRing k, b ≠ 0 ∧
      z = (a : endUnramifiedField k) / (b : endUnramifiedField k)) ∧
    Function.Bijective (strictConstantsResidue k) ∧
    (∀ σ τ : Gal(endGenericClosure k/endField k),
      strictRingGalois (σ * τ) = (strictRingGalois σ).comp (strictRingGalois τ) ∧
      strictResidueGalois (σ * τ) = (strictResidueGalois σ).comp (strictResidueGalois τ)) ∧
    (∀ σ : Gal(endGenericClosure k/endField k),
      (σ ∈ (endUnramifiedField k).fixingSubgroup ↔ strictRingGalois σ = RingHom.id _) ∧
      (σ ∈ (endUnramifiedField k).fixingSubgroup ↔ strictResidueGalois σ = RingHom.id _)) ∧
    (∀ τ : strictResidueRing k →+* strictResidueRing k,
      τ.comp (strictResidueBaseHom k) = strictResidueBaseHom k →
      ∃ σ : Gal(endGenericClosure k/endField k), strictResidueGalois σ = τ) ∧
    (∀ (w : localWeilGroup (LaurentSeries k) (SeparableClosure (LaurentSeries k)))
        (y : strictResidueRing k),
      strictResidueGalois (completionRestriction k
          (localProjection (LaurentSeries k) (SeparableClosure (LaurentSeries k)) w)) y ^
          (Nat.card k ^ (localDegreeInt (LaurentSeries k) (SeparableClosure (LaurentSeries k))
            w).toNat) =
        y ^ (Nat.card k ^ (-localDegreeInt (LaurentSeries k)
          (SeparableClosure (LaurentSeries k)) w).toNat)) ∧
    ∃ φ : strictResidueRing k ≃+* AlgebraicClosure (localResidueField (LaurentSeries k)),
      ∀ (σ : Gal(SeparableClosure (LaurentSeries k)/LaurentSeries k)) (y : strictResidueRing k),
        φ (strictResidueGalois (completionRestriction k σ) y) =
          AlgEquiv.toAlgHom
            (absoluteResidueHom (LaurentSeries k) (SeparableClosure (LaurentSeries k)) σ) (φ y)

end Langlands.Henniart.Laumon
