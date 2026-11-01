import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

universe u v w

namespace Langlands.AlgebraicGeometry.NoetherianApproximation

theorem isFractionRing_of_surjective_awayMap
    {R : Type v} {A : Type u} [CommRing R] [CommRing A] [IsDomain A]
    [Algebra R A] (C : Subalgebra R A) (r : C) (hr : r.val ≠ 0)
    (h : Function.Surjective (Localization.awayMap C.val.toRingHom r)) :
    IsFractionRing C (FractionRing A) := by
  have hmap : Function.Injective (algebraMap C (FractionRing A)) := by
    exact (IsFractionRing.injective A (FractionRing A)).comp Subtype.val_injective
  let : FaithfulSMul C (FractionRing A) :=
    (faithfulSMul_iff_algebraMap_injective C (FractionRing A)).mpr hmap
  apply IsFractionRing.of_field
  intro z
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective A z
  obtain ⟨c, m, hc⟩ := Localization.awayMap_surjective_iff.mp h a
  obtain ⟨d, n, hd⟩ := Localization.awayMap_surjective_iff.mp h b
  refine ⟨c * r ^ n, d * r ^ m, ?_⟩
  have hc' : algebraMap C (FractionRing A) c =
      algebraMap A (FractionRing A) r.val ^ m * algebraMap A (FractionRing A) a :=
    congrArg (algebraMap A (FractionRing A)) hc |>.trans (by simp)
  have hd' : algebraMap C (FractionRing A) d =
      algebraMap A (FractionRing A) r.val ^ n * algebraMap A (FractionRing A) b :=
    congrArg (algebraMap A (FractionRing A)) hd |>.trans (by simp)
  have hr' : algebraMap A (FractionRing A) r.val ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).mpr hr
  have hb' : algebraMap A (FractionRing A) b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).mpr
      (mem_nonZeroDivisors_iff_ne_zero.mp hb)
  simp only [map_mul, map_pow]
  rw [hc', hd']
  change algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) b =
    (algebraMap A (FractionRing A) r.val ^ m * algebraMap A (FractionRing A) a *
      algebraMap A (FractionRing A) r.val ^ n) /
    (algebraMap A (FractionRing A) r.val ^ n * algebraMap A (FractionRing A) b *
      algebraMap A (FractionRing A) r.val ^ m)
  field_simp

theorem finite_integralClosure_of_localization
    {R : Type u} {S : Type v} {K : Type w}
    [CommRing R] [CommRing S] [CommRing K]
    [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K]
    (r : R) [IsLocalization.Away r S]
    [IsLocalization.Away (algebraMap R K r) K]
    [Module.Finite R (integralClosure R K)] :
    Module.Finite S (integralClosure S K) := by
  let f : integralClosure R K →+* integralClosure S K :=
    { toFun := fun x ↦ ⟨x.val, x.property.tower_top⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  let : Algebra (integralClosure R K) (integralClosure S K) := f.toAlgebra
  let : IsScalarTower R (integralClosure R K) (integralClosure S K) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower (integralClosure R K) (integralClosure S K) K :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsLocalization.Away (algebraMap R (integralClosure R K) r)
      (integralClosure S K) :=
    IsLocalization.Away.integralClosure (S := K) (Rf := S) (Sf := K) r
  let : IsLocalization
      (Algebra.algebraMapSubmonoid (integralClosure R K) (Submonoid.powers r))
      (integralClosure S K) := by
    simpa using (inferInstance : IsLocalization.Away
      (algebraMap R (integralClosure R K) r) (integralClosure S K))
  exact Module.Finite.of_isLocalization R (integralClosure R K) (Submonoid.powers r)

theorem finite_localizedModule_integralClosure
    {R : Type u} {K : Type v} [CommRing R] [CommRing K] [Algebra R K]
    (r : R) [Algebra (Localization.Away r) K]
    [IsScalarTower R (Localization.Away r) K]
    [IsLocalization.Away (algebraMap R K r) K]
    [Module.Finite (Localization.Away r) (integralClosure (Localization.Away r) K)] :
    Module.Finite (Localization.Away r) (LocalizedModule.Away r (integralClosure R K)) := by
  let f : integralClosure R K →+* integralClosure (Localization.Away r) K :=
    { toFun := fun x ↦ ⟨x.val, x.property.tower_top⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  let : Algebra (integralClosure R K) (integralClosure (Localization.Away r) K) :=
    f.toAlgebra
  let : IsScalarTower R (integralClosure R K)
      (integralClosure (Localization.Away r) K) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower (integralClosure R K)
      (integralClosure (Localization.Away r) K) K :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsLocalization.Away (algebraMap R (integralClosure R K) r)
      (integralClosure (Localization.Away r) K) :=
    IsLocalization.Away.integralClosure (S := K) (Rf := Localization.Away r) (Sf := K) r
  let : IsLocalization
      (Algebra.algebraMapSubmonoid (integralClosure R K) (Submonoid.powers r))
      (integralClosure (Localization.Away r) K) := by
    simpa using (inferInstance : IsLocalization.Away
      (algebraMap R (integralClosure R K) r) (integralClosure (Localization.Away r) K))
  let e := IsLocalizedModule.linearEquiv (Submonoid.powers r)
    (IsScalarTower.toAlgHom R (integralClosure R K)
      (integralClosure (Localization.Away r) K)).toLinearMap
    (LocalizedModule.mkLinearMap (Submonoid.powers r) (integralClosure R K))
  exact Module.Finite.equiv (e.extendScalarsOfIsLocalization
    (Submonoid.powers r) (Localization.Away r))

theorem finite_normalization_localized_of_finite_subalgebra
    {R : Type v} {A : Type u} [CommRing R] [CommRing A] [IsDomain A]
    [Algebra R A] (C : Subalgebra R A) (r : C) (hr : r.val ≠ 0)
    (h : Function.Bijective (Localization.awayMap C.val.toRingHom r))
    [Module.Finite C (integralClosure C (FractionRing C))] :
    Module.Finite (Localization.Away r.val)
      (LocalizedModule.Away r.val (integralClosure A (FractionRing A))) := by
  let K := FractionRing A
  let S := Localization.Away r.val
  let : IsFractionRing C K := isFractionRing_of_surjective_awayMap C r hr h.surjective
  let e : FractionRing C ≃ₐ[C] K := IsLocalization.algEquiv (nonZeroDivisors C) (FractionRing C) K
  let : Module.Finite C (integralClosure C K) :=
    Module.Finite.equiv e.mapIntegralClosure.toLinearEquiv
  let g : Localization.Away r →ₐ[C] S :=
    { toRingHom := Localization.awayMap C.val.toRingHom r
      commutes' := fun c ↦ by
        change Localization.awayMap C.val.toRingHom r
          (algebraMap C (Localization.Away r) c) = algebraMap A S c.val
        exact IsLocalization.map_eq _ c }
  let : IsLocalization.Away r S :=
    IsLocalization.isLocalization_of_algEquiv (Submonoid.powers r)
      (AlgEquiv.ofBijective g h)
  have hu : IsUnit (algebraMap A K r.val) :=
    isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hr)
  let : Algebra S K := (IsLocalization.Away.lift r.val hu).toAlgebra
  let : IsScalarTower A S K := IsScalarTower.of_algebraMap_eq fun a ↦
    (IsLocalization.Away.lift_eq r.val hu a).symm
  let : IsScalarTower C S K := IsScalarTower.of_algebraMap_eq fun c ↦
    (IsLocalization.Away.lift_eq r.val hu c.val).symm
  let : IsLocalization.Away (algebraMap C K r) K :=
    IsLocalization.away_of_isUnit_of_bijective K hu Function.bijective_id
  let : IsLocalization.Away (algebraMap A K r.val) K :=
    IsLocalization.away_of_isUnit_of_bijective K hu Function.bijective_id
  let : Module.Finite S (integralClosure S K) := finite_integralClosure_of_localization r
  exact finite_localizedModule_integralClosure r.val

theorem finite_of_finite_localizations_near_maximal
    {R : Type u} {M : Type v} [CommRing R] [AddCommMonoid M] [Module R M]
    (h : ∀ q : Ideal R, q.IsMaximal → ∃ r : R, r ∉ q ∧
      Module.Finite (Localization.Away r) (LocalizedModule.Away r M)) :
    Module.Finite R M := by
  let t : Set R := {r | Module.Finite (Localization.Away r) (LocalizedModule.Away r M)}
  have ht : Ideal.span t = ⊤ := by
    by_contra hc
    obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal (Ideal.span t) hc
    obtain ⟨r, hr, hfin⟩ := h q hq
    exact hr (hle (Ideal.subset_span hfin))
  exact Module.Finite.of_localizationSpan t ht fun r ↦ r.property

end Langlands.AlgebraicGeometry.NoetherianApproximation
