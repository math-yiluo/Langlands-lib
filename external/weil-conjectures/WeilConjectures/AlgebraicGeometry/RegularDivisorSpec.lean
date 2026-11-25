/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.RegularDivisor
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.HenselianPairSections
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Principal regular divisors of affine schemes

For a ring `S` and a non-zero-divisor `a ∈ S` with `S/(a)` regular, the closed immersion
`Spec (S/(a)) ⟶ Spec S` is a regular divisor; two such divisors `V(a)`, `V(b)` meet transversely
at a single point if `S/(a, b)` is a field.

## Main results

- `AlgebraicGeometry.isRegular_spec`: the spectrum of a regular ring is regular.
- `AlgebraicGeometry.isRegularDivisor_specMap_quotient`: `Spec (S/(a)) ⟶ Spec S` is a regular
  divisor.
- `AlgebraicGeometry.meetTransverselyAt_specMap_quotient`: `V(a)` and `V(b)` meet transversely at
  the point `V(a, b)` when `S/(a, b)` is a field.
- `AlgebraicGeometry.Etale.range_specMap_quotientMk`: the image of `Spec (S/I) ⟶ Spec S` is `V(I)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {S : Type u} [CommRing S]

/-- The spectrum of a regular ring is a regular scheme. -/
lemma isRegular_spec [IsRegularRing S] : IsRegular (Spec (.of S)) :=
  ⟨fun z ↦ IsRegularLocalRing.of_ringEquiv
    (Spec.stalkIso (.of S) z).commRingCatIsoToRingEquiv.symm⟩

/-- For a non-zero-divisor `a ∈ S` with `S/(a)` regular, `Spec (S/(a)) ⟶ Spec S` is a regular
divisor. -/
lemma isRegularDivisor_specMap_quotient {a : S} (ha : a ∈ nonZeroDivisors S)
    [IsRegularRing (S ⧸ Ideal.span {a})] :
    IsRegularDivisor (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a})))) := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a})))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  refine ⟨isEffectiveCartierCenter_iff_isInvertible_ker.mpr
    (Scheme.IdealSheafData.IsInvertible.of_isAffine ?_), isRegular_spec⟩
  have key : RingHom.ker (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (Ideal.span {a})))).appTop.hom =
      (RingHom.ker (Ideal.Quotient.mk (Ideal.span {a}))).comap
        (Scheme.ΓSpecIso (.of S)).hom.hom := by
    ext x
    rw [RingHom.mem_ker, Ideal.mem_comap, RingHom.mem_ker, ← map_eq_zero_iff _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).hom).1,
      ← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply]
    rfl
  rw [Scheme.ker_of_isAffine, Scheme.IdealSheafData.ofIdealTop_ideal, key, Ideal.mk_ker]
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id, CommRingCat.hom_id, Ideal.map_id]
  exact (Ideal.isRegularPrincipal_span_singleton ha).comap_of_bijective
    (ConcreteCategory.bijective_of_isIso _)

/-- For ideals `I, J ≤ K` of `S` with `K ≤ I ⊔ J`, the square of quotient maps
`S → S/I → S/K`, `S → S/J → S/K` is a pushout of commutative rings. -/
lemma isPushout_quotient_factor {I J K : Ideal S} (hI : I ≤ K) (hJ : J ≤ K)
    (hK : K ≤ I ⊔ J) :
    IsPushout (CommRingCat.ofHom (Ideal.Quotient.mk I))
      (CommRingCat.ofHom (Ideal.Quotient.mk J)) (CommRingCat.ofHom (Ideal.Quotient.factor hI))
      (CommRingCat.ofHom (Ideal.Quotient.factor hJ)) := by
  have w : CommRingCat.ofHom (Ideal.Quotient.mk I) ≫
      CommRingCat.ofHom (Ideal.Quotient.factor hI) =
      CommRingCat.ofHom (Ideal.Quotient.mk J) ≫ CommRingCat.ofHom (Ideal.Quotient.factor hJ) := by
    ext x
    simp
  refine IsPushout.of_isColimit' ⟨w⟩ (PushoutCocone.IsColimit.mk w
    (fun s ↦ CommRingCat.ofHom (Ideal.Quotient.lift K
      (CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ s.inl).hom fun x hx ↦ ?_)) ?_ ?_ ?_)
  · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp (hK hx)
    have hs := congr($(s.condition).hom z)
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at hs ⊢
    rw [map_add, map_add, hs, Ideal.Quotient.eq_zero_iff_mem.mpr hy,
      Ideal.Quotient.eq_zero_iff_mem.mpr hz, map_zero, map_zero, add_zero]
  · intro s
    ext x
    simp
  · intro s
    ext x
    have hs := congr($(s.condition).hom x)
    simpa using hs
  · intro s m h₁ _
    ext x
    have := congr($(h₁).hom (Ideal.Quotient.mk I x))
    simpa using this

/-- If `S/(a, b)` is a field `K`, the closed subschemes `V(a)` and `V(b)` of `Spec S` meet
transversely at the single point `V(a, b)`. -/
lemma meetTransverselyAt_specMap_quotient {a b : S} (hab : IsField (S ⧸ Ideal.span {a, b}))
    (z : Spec (.of S)) (hz : z.asIdeal = Ideal.span {a, b}) :
    MeetTransverselyAt (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a}))))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {b})))) z := by
  have hspan : Ideal.span {a, b} = Ideal.span {a} ⊔ Ideal.span {b} := by
    rw [← Ideal.span_union, Set.singleton_union]
  have hI : Ideal.span {a} ≤ Ideal.span {a, b} := hspan ▸ le_sup_left
  have hJ : Ideal.span {b} ≤ Ideal.span {a, b} := hspan ▸ le_sup_right
  refine ⟨S ⧸ Ideal.span {a, b}, hab.toField,
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hI)),
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hJ)),
    isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_quotient_factor hI hJ hspan.le), ?_⟩
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp_mk,
    Etale.range_specMap_quotientMk]
  have hmax : (Ideal.span {a, b}).IsMaximal := Ideal.Quotient.maximal_of_isField _ hab
  ext p
  simp only [Set.mem_singleton_iff, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
  refine ⟨fun hp ↦ PrimeSpectrum.ext ?_, fun hp ↦ hp ▸ hz.ge⟩
  rw [hz]
  exact (hmax.eq_of_le p.isPrime.ne_top hp).symm

end AlgebraicGeometry
