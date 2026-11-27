import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Birational.RationalMap
import Mathlib.RingTheory.Localization.NumDen
import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal

/-! # Affine-valued extension in factorial local rings -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite Topology

universe u

namespace Langlands.AlgebraicGeometry.FactorialAffineExtension

/-- In a factorial domain these are the generic prime and all height-one primes. -/
def IsGenericOrPrimeElement {A : Type u} [CommRing A] (p : PrimeSpectrum A) : Prop :=
  p.asIdeal = ⊥ ∨ ∃ r : A, Prime r ∧ p.asIdeal = Ideal.span {r}

/-- The image of the generic and principal prime points under a local map of factorial
stalks detects these points in every open in the target spectrum. -/
theorem contains_primes_of_localMap {A B : CommRingCat.{u}} [IsDomain A] [IsDomain B]
    [UniqueFactorizationMonoid A] (f : B ⟶ A) [IsLocalHom f.hom]
    (U : (Spec B).Opens) (h : ∀ p : PrimeSpectrum A, IsGenericOrPrimeElement p → Spec.map f p ∈ U)
    (q : PrimeSpectrum B) (hq : IsGenericOrPrimeElement q) : q ∈ U := by
  suffices ∃ p : PrimeSpectrum A, IsGenericOrPrimeElement p ∧ q ≤ Spec.map f p by
    obtain ⟨p, hp, hqp⟩ := this
    exact ((PrimeSpectrum.le_iff_specializes _ _).mp hqp).mem_open U.isOpen (h p hp)
  rcases hq with hbot | ⟨r, hr, hqr⟩
  · exact ⟨⊥, Or.inl rfl, show q.asIdeal ≤ _ by rw [hbot]; exact bot_le⟩
  · have hnu : ¬ IsUnit (f r) := fun hu => hr.not_isUnit ((isUnit_map_iff f.hom r).mp hu)
    have find : ∃ p : PrimeSpectrum A, IsGenericOrPrimeElement p ∧ f r ∈ p.asIdeal := by
      by_cases he : f r = 0
      · exact ⟨⊥, Or.inl rfl, by simp [he]⟩
      · obtain ⟨t, ht, hd⟩ := WfDvdMonoid.exists_irreducible_factor hnu he
        have ht' := UniqueFactorizationMonoid.irreducible_iff_prime.mp ht
        refine ⟨⟨Ideal.span {t}, (Ideal.span_singleton_prime ht.ne_zero).mpr ht'⟩,
          Or.inr ⟨t, ht', rfl⟩, Ideal.mem_span_singleton.mpr hd⟩
    obtain ⟨p, hp, hpr⟩ := find
    refine ⟨p, hp, ?_⟩
    change q.asIdeal ≤ (p.comap f.hom).asIdeal
    rw [hqr, Ideal.span_singleton_le_iff_mem]
    exact hpr

private theorem restriction_bijective {A : CommRingCat.{u}} [IsDomain A]
    [UniqueFactorizationMonoid A] (U : (Spec A).Opens)
    (hU : ∀ p : PrimeSpectrum A, IsGenericOrPrimeElement p → p ∈ U) :
    Function.Bijective ((Spec A).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op) := by
  let Z := Spec A
  let K := Z.functionField
  let gen := genericPoint Z
  have hgen : gen ∈ U := by
    rw [show gen = (⊥ : PrimeSpectrum A) from genericPoint_eq_bot_of_affine A]
    exact hU ⊥ (Or.inl rfl)
  let : Nonempty U := ⟨⟨gen, hgen⟩⟩
  refine ⟨map_injective_of_isIntegral Z _, fun s => ?_⟩
  have hab : ∀ (p : PrimeSpectrum A) (hp : p ∈ U),
      ∃ c : A, ∃ d : p.asIdeal.primeCompl,
        Z.germToFunctionField U s * algebraMap A K d = algebraMap A K c := by
    intro p hp
    let v := Z.presheaf.germ U p hp s
    let : Algebra A (Z.presheaf.stalk p) := StructureSheaf.stalkAlgebra A p
    have : IsLocalization.AtPrime (Z.presheaf.stalk p) p.asIdeal :=
      StructureSheaf.IsLocalization.to_stalk A p
    obtain ⟨⟨c, d⟩, e⟩ := IsLocalization.surj p.asIdeal.primeCompl v
    refine ⟨c, d, ?_⟩
    let : Algebra (Z.presheaf.stalk p) K := stalkFunctionFieldAlgebra Z p
    have h := congrArg (algebraMap (Z.presheaf.stalk p) K) e
    have hmap (a : A) : algebraMap (Z.presheaf.stalk p) K
        (algebraMap A (Z.presheaf.stalk p) a) = algebraMap A K a :=
      StructureSheaf.toStalk_stalkSpecializes_apply (genericPoint_specializes (α := Z) p) a
    have hv : algebraMap (Z.presheaf.stalk p) K v = Z.germToFunctionField U s :=
      Scheme.algebraMap_germ_eq_germToFunctionField (X := Z) hp s
    simpa only [map_mul, hmap, hv] using h
  have hrange : ∃ a : A, algebraMap A K a = Z.germToFunctionField U s := by
    obtain ⟨a, b, hab', e⟩ := IsFractionRing.exists_reduced_fraction A (Z.germToFunctionField U s)
    by_cases hb : IsUnit (b : A)
    · obtain ⟨v, hv⟩ := hb
      refine ⟨a * ↑v⁻¹, ?_⟩
      rw [← e, eq_comm, IsLocalization.mk'_eq_iff_eq_mul, ← map_mul, ← hv, mul_assoc, Units.inv_mul, mul_one]
    · obtain ⟨r, hirr, hrb⟩ := WfDvdMonoid.exists_irreducible_factor hb (nonZeroDivisors.coe_ne_zero b)
      have hr := UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
      let p : PrimeSpectrum A := ⟨Ideal.span {r}, (Ideal.span_singleton_prime hr.ne_zero).mpr hr⟩
      obtain ⟨c, d, hcd⟩ := hab p (hU p (Or.inr ⟨r, hr, rfl⟩))
      have hmul : a * (d : A) = c * b := by
        apply IsFractionRing.injective A K
        rw [map_mul, map_mul, ← IsLocalization.mk'_spec K a b, e, mul_right_comm, hcd]
      have hrad : r ∣ a * (d : A) := hmul ▸ dvd_mul_of_dvd_right hrb c
      rcases hr.dvd_or_dvd hrad with hra | hrd
      · exact (hr.not_isUnit (hab' hra hrb)).elim
      · exact (d.2 (Ideal.mem_span_singleton.mpr hrd)).elim
  obtain ⟨a, ha⟩ := hrange
  refine ⟨algebraMap A Γ(Z, ⊤) a, Z.germToFunctionField_injective U ?_⟩
  rw [← ha]
  exact StructureSheaf.algebraMap_germ_apply U gen hgen a

/-- An affine-valued map on an open containing the generic and principal prime points of
an affine factorial scheme extends to the entire spectrum. -/
theorem exists_extension {A : CommRingCat.{u}} [IsDomain A] [UniqueFactorizationMonoid A]
    (U : (Spec A).Opens) (hU : ∀ p : PrimeSpectrum A, IsGenericOrPrimeElement p → p ∈ U)
    {H : Scheme.{u}} [IsAffine H] (g : U.toScheme ⟶ H) :
    ∃ g' : Spec A ⟶ H, U.ι ≫ g' = g := by
  let ρ := (Spec A).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
  have : IsIso ρ := (ConcreteCategory.isIso_iff_bijective _).mpr (restriction_bijective U hU)
  refine ⟨(Spec A).toSpecΓ ≫ Spec.map (inv ρ) ≫ Spec.map (g.appTop ≫ U.topIso.hom) ≫
    H.isoSpec.inv, ?_⟩
  apply (cancel_mono H.isoSpec.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change U.ι ≫ (Spec A).toSpecΓ ≫ Spec.map (inv ρ) ≫
    Spec.map (g.appTop ≫ U.topIso.hom) = g ≫ H.toSpecΓ
  have hρ : U.toSpecΓ ≫ Spec.map ρ = U.ι ≫ (Spec A).toSpecΓ :=
    Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top U
  rw [← reassoc_of% hρ, ← Spec.map_comp_assoc, IsIso.inv_hom_id, Spec.map_id, Category.id_comp,
    Scheme.Opens.toSpecΓ, Spec.map_comp, Category.assoc U.toScheme.toSpecΓ, ← Spec.map_comp_assoc, Iso.hom_inv_id, Spec.map_id,
    Category.id_comp, Scheme.toSpecΓ_naturality]

end Langlands.AlgebraicGeometry.FactorialAffineExtension
