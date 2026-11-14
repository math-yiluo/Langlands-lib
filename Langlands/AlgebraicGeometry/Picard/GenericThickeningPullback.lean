import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Ring pullbacks gluing a generic lift with a square-zero thickening -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.AlgebraicGeometry.Picard.GenericThickening

section Pullback

variable {Λ R A' B' C : Type u} [CommRing Λ] [CommRing R] [CommRing A'] [CommRing B']
  [CommRing C] [Algebra Λ R] [Algebra Λ A'] [Algebra Λ B'] [Algebra Λ C]

/-- A commuting square of algebras is a ring pullback as soon as the induced map to the
set-theoretic fibre product is bijective. -/
theorem isPullback_of_forall (p : R →ₐ[Λ] A') (q : R →ₐ[Λ] B') (a : A' →ₐ[Λ] C)
    (b : B' →ₐ[Λ] C) (hw : ∀ r, a (p r) = b (q r))
    (hinj : ∀ r s, p r = p s → q r = q s → r = s)
    (hsurj : ∀ x y, a x = b y → ∃ r, p r = x ∧ q r = y) :
    IsPullback (CommRingCat.ofHom p.toRingHom) (CommRingCat.ofHom q.toRingHom)
      (CommRingCat.ofHom a.toRingHom) (CommRingCat.ofHom b.toRingHom) := by
  have hw' : CommRingCat.ofHom p.toRingHom ≫ CommRingCat.ofHom a.toRingHom =
      CommRingCat.ofHom q.toRingHom ≫ CommRingCat.ofHom b.toRingHom := by
    ext r
    exact hw r
  let : ReflectsLimit
      (cospan (CommRingCat.ofHom a.toRingHom) (CommRingCat.ofHom b.toRingHom))
      (forget CommRingCat) :=
    reflectsLimit_of_reflectsIsomorphisms _ _
  apply IsPullback.of_map (forget CommRingCat) hw'
  rw [Types.isPullback_iff]
  refine ⟨by rw [← Functor.map_comp, ← Functor.map_comp, hw'], ?_, ?_⟩
  · rintro r s ⟨h₁, h₂⟩
    exact hinj r s h₁ h₂
  · intro x y h
    exact hsurj x y h

end Pullback

section Hypotheses

variable {Λ : Type u} [CommRing Λ]

/-- A nilpotent ideal killed by the nilradical has square zero. -/
theorem mul_self_eq_bot {I : Ideal Λ} (hI : IsNilpotent I) (h : nilradical Λ * I = ⊥) :
    I * I = ⊥ := by
  have hle : I ≤ nilradical Λ := by
    obtain ⟨n, hn⟩ := hI
    intro x hx
    rw [mem_nilradical]
    refine ⟨n, ?_⟩
    have := Ideal.pow_mem_pow hx n
    rwa [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  exact le_bot_iff.mp (h ▸ Ideal.mul_mono_left hle)

/-- If a noetherian ring has a single associated prime, it embeds into its localization at
the generic point of its spectrum. -/
theorem algebraMap_atPrime_injective [IsNoetherianRing Λ]
    (hAss : ∃ p : Ideal Λ, associatedPrimes Λ Λ = {p}) (t : PrimeSpectrum Λ)
    (ht : IsGenericPoint t Set.univ) :
    Function.Injective (algebraMap Λ (Localization.AtPrime t.asIdeal)) := by
  obtain ⟨p, hp⟩ := hAss
  have hmin : t.asIdeal ∈ (Module.annihilator Λ Λ).minimalPrimes := by
    refine ⟨⟨t.isPrime, ?_⟩, ?_⟩
    · intro r hr
      have h1 := Module.mem_annihilator.mp hr 1
      rw [smul_eq_mul, mul_one] at h1
      rw [h1]
      exact zero_mem _
    · intro q hq _
      have hcl : closure ({t} : Set (PrimeSpectrum Λ)) = Set.univ := ht
      have hmem : (⟨q, hq.1⟩ : PrimeSpectrum Λ) ∈ closure ({t} : Set (PrimeSpectrum Λ)) := by
        rw [hcl]
        exact Set.mem_univ _
      exact (PrimeSpectrum.le_iff_mem_closure t ⟨q, hq.1⟩).mpr hmem
  have hq : t.asIdeal ∈ associatedPrimes Λ Λ :=
    Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes Λ Λ hmin
  rw [hp, Set.mem_singleton_iff] at hq
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨s, hs⟩, hsx⟩ := (IsLocalization.map_eq_zero_iff t.asIdeal.primeCompl _ x).mp hx
  by_contra hx0
  have hzd : s ∈ ⋃ p ∈ associatedPrimes Λ Λ, (p : Set Λ) := by
    rw [biUnion_associatedPrimes_eq_zero_divisors]
    exact ⟨x, hx0, hsx⟩
  rw [hp] at hzd
  simp only [Set.mem_singleton_iff, Set.iUnion_iUnion_eq_left, SetLike.mem_coe] at hzd
  exact hs (hq ▸ hzd)

end Hypotheses

variable {Λ : Type u} [CommRing Λ] (Λ' : Type u) [CommRing Λ'] [Algebra Λ Λ'] (I : Ideal Λ)

/-- The map `Λ/I → Λ'/IΛ'` induced by the structure map. -/
abbrev quotMap : Λ ⧸ I →ₐ[Λ] Λ' ⧸ I.map (algebraMap Λ Λ') :=
  Ideal.quotientMapₐ (I.map (algebraMap Λ Λ')) (Algebra.ofId Λ Λ')
    (fun _ hx ↦ Ideal.mem_map_of_mem _ hx)

/-- The fibre product `Λ' ×_{Λ'/IΛ'} Λ/I`, as a subalgebra of the product. -/
def fibreSubalgebra : Subalgebra Λ (Λ' × (Λ ⧸ I)) :=
  AlgHom.equalizer
    ((Ideal.Quotient.mkₐ Λ (I.map (algebraMap Λ Λ'))).comp (AlgHom.fst Λ Λ' (Λ ⧸ I)))
    ((quotMap Λ' I).comp (AlgHom.snd Λ Λ' (Λ ⧸ I)))

/-- The fibre product `Λ' ×_{Λ'/IΛ'} Λ/I`, as a type carrying only the commutative ring
structure of the subalgebra (a type synonym, so that all ring structures on it come from a
single `CommRing` instance). -/
def fibre : Type u :=
  fibreSubalgebra Λ' I

instance : CommRing (fibre Λ' I) :=
  Subalgebra.toCommRing _

instance : Algebra Λ (fibre Λ' I) :=
  Subalgebra.algebra _

/-- The inclusion of the fibre product into the product. -/
def fibreVal : fibre Λ' I →ₐ[Λ] Λ' × (Λ ⧸ I) :=
  (fibreSubalgebra Λ' I).val

/-- The element of the fibre product with given compatible components. -/
def fibreMk (x : Λ') (y : Λ ⧸ I)
    (h : Ideal.Quotient.mk (I.map (algebraMap Λ Λ')) x = quotMap Λ' I y) : fibre Λ' I :=
  (⟨(x, y), h⟩ : ↥(fibreSubalgebra Λ' I))

/-- The projection of the fibre product to `Λ'`. -/
def fibreFst : fibre Λ' I →ₐ[Λ] Λ' :=
  (AlgHom.fst Λ Λ' (Λ ⧸ I)).comp (fibreVal Λ' I)

/-- The projection of the fibre product to `Λ/I`. -/
def fibreSnd : fibre Λ' I →ₐ[Λ] Λ ⧸ I :=
  (AlgHom.snd Λ Λ' (Λ ⧸ I)).comp (fibreVal Λ' I)

lemma fibre_spec (r : fibre Λ' I) :
    Ideal.Quotient.mk (I.map (algebraMap Λ Λ')) (fibreFst Λ' I r) =
      quotMap Λ' I (fibreSnd Λ' I r) :=
  (show ↥(fibreSubalgebra Λ' I) from r).2

lemma fibre_ext {r s : fibre Λ' I} (h₁ : fibreFst Λ' I r = fibreFst Λ' I s)
    (h₂ : fibreSnd Λ' I r = fibreSnd Λ' I s) : r = s :=
  (Subtype.ext (Prod.ext h₁ h₂) :
    (show ↥(fibreSubalgebra Λ' I) from r) = (show ↥(fibreSubalgebra Λ' I) from s))

lemma fibreFst_algebraMap (x : Λ) :
    fibreFst Λ' I (algebraMap Λ (fibre Λ' I) x) = algebraMap Λ Λ' x :=
  AlgHom.commutes _ _

lemma fibreSnd_algebraMap (x : Λ) :
    fibreSnd Λ' I (algebraMap Λ (fibre Λ' I) x) = Ideal.Quotient.mk I x :=
  AlgHom.commutes _ _

/-- The fibre product is the ring pullback of `Λ/I → Λ'/IΛ' ← Λ'`. -/
theorem fibre_isPullback :
    IsPullback (CommRingCat.ofHom (fibreSnd Λ' I).toRingHom)
      (CommRingCat.ofHom (fibreFst Λ' I).toRingHom)
      (CommRingCat.ofHom (quotMap Λ' I).toRingHom)
      (CommRingCat.ofHom (Ideal.Quotient.mkₐ Λ (I.map (algebraMap Λ Λ'))).toRingHom) := by
  refine isPullback_of_forall _ _ _ _ (fun r ↦ (fibre_spec Λ' I r).symm) ?_ ?_
  · intro r s h₁ h₂
    exact fibre_ext Λ' I h₂ h₁
  · intro x y h
    exact ⟨fibreMk Λ' I y x h.symm, rfl, rfl⟩

lemma ker_mkₐ (J : Ideal Λ') :
    RingHom.ker (Ideal.Quotient.mkₐ Λ J).toRingHom = J := by
  ext y
  rw [RingHom.mem_ker]
  exact Ideal.Quotient.eq_zero_iff_mem

variable {I}

/-- The kernel of `Λ' → Λ'/IΛ'` is nilpotent when `I² = 0`. -/
theorem isNilpotent_ker_mkₐ_map (hII : I * I = ⊥) :
    IsNilpotent (RingHom.ker (Ideal.Quotient.mkₐ Λ (I.map (algebraMap Λ Λ'))).toRingHom) := by
  refine ⟨2, ?_⟩
  rw [ker_mkₐ, pow_two, ← Ideal.map_mul, hII, Ideal.map_bot]
  rfl

variable (I)

/-- The image of `I` in the fibre product. -/
abbrev thick : Ideal (fibre Λ' I) :=
  I.map (algebraMap Λ (fibre Λ' I))

/-- The quotient map of the fibre product by the thickening ideal. -/
abbrev thickMk : fibre Λ' I →ₐ[Λ] fibre Λ' I ⧸ thick Λ' I :=
  Ideal.Quotient.mkₐ Λ (thick Λ' I)

variable {I}

/-- When `I² = 0`, every element of the ideal generated by the image of `I` in the fibre
product is the image of an element of `I`. -/
theorem exists_of_mem_thick (hII : I * I = ⊥) {z : fibre Λ' I} (hz : z ∈ thick Λ' I) :
    ∃ x ∈ I, z = algebraMap Λ (fibre Λ' I) x := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, rfl⟩ := hz
    exact ⟨x, hx, rfl⟩
  | zero => exact ⟨0, zero_mem _, (map_zero _).symm⟩
  | add z₁ z₂ _ _ h₁ h₂ =>
    obtain ⟨x₁, hx₁, rfl⟩ := h₁
    obtain ⟨x₂, hx₂, rfl⟩ := h₂
    exact ⟨x₁ + x₂, add_mem hx₁ hx₂, (map_add _ _ _).symm⟩
  | smul r z _ h =>
    obtain ⟨x, hx, rfl⟩ := h
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (fibreSnd Λ' I r)
    refine ⟨b * x, I.mul_mem_left b hx, ?_⟩
    have hy : fibreFst Λ' I r - algebraMap Λ Λ' b ∈ I.map (algebraMap Λ Λ') := by
      rw [← Ideal.Quotient.eq, fibre_spec, ← hb]
      rfl
    have hx' : algebraMap Λ Λ' x ∈ I.map (algebraMap Λ Λ') := Ideal.mem_map_of_mem _ hx
    have h0 : (fibreFst Λ' I r - algebraMap Λ Λ' b) * algebraMap Λ Λ' x = 0 := by
      have h := Ideal.mul_mem_mul hy hx'
      rwa [← Ideal.map_mul, hII, Ideal.map_bot, Ideal.mem_bot] at h
    apply fibre_ext
    · rw [smul_eq_mul, map_mul, fibreFst_algebraMap, fibreFst_algebraMap, map_mul]
      linear_combination h0
    · rw [smul_eq_mul, map_mul, fibreSnd_algebraMap, fibreSnd_algebraMap,
        Ideal.Quotient.eq_zero_iff_mem.mpr hx, mul_zero, eq_comm,
        Ideal.Quotient.eq_zero_iff_mem]
      exact I.mul_mem_left b hx

/-- The thickening ideal has square zero when `I² = 0`. -/
theorem thick_mul_self (hII : I * I = ⊥) : thick Λ' I * thick Λ' I = ⊥ := by
  rw [← Ideal.map_mul, hII, Ideal.map_bot]

/-- The kernel of the fibre product modulo the thickening ideal is nilpotent. -/
theorem isNilpotent_ker_mkₐ_thick (hII : I * I = ⊥) :
    IsNilpotent (RingHom.ker (thickMk Λ' I).toRingHom) := by
  refine ⟨2, ?_⟩
  rw [ker_mkₐ, pow_two, thick_mul_self Λ' hII]
  rfl

variable (I)

/-- The map `Λ/I → fibre/thick` induced by the structure map of the fibre product. -/
abbrev secMap : Λ ⧸ I →ₐ[Λ] fibre Λ' I ⧸ thick Λ' I :=
  Ideal.quotientMapₐ (thick Λ' I) (Algebra.ofId Λ (fibre Λ' I))
    (fun _ hx ↦ Ideal.mem_map_of_mem _ hx)

variable {I}

/-- If `I² = 0` and `Λ → Λ'` is injective on `I`, then `Λ` is the ring pullback of
`Λ/I → fibre/thick ← fibre`. -/
theorem thick_isPullback (hII : I * I = ⊥)
    (hinj : ∀ x ∈ I, algebraMap Λ Λ' x = 0 → x = 0) :
    IsPullback (CommRingCat.ofHom (Ideal.Quotient.mkₐ Λ I).toRingHom)
      (CommRingCat.ofHom (Algebra.ofId Λ (fibre Λ' I)).toRingHom)
      (CommRingCat.ofHom (secMap Λ' I).toRingHom)
      (CommRingCat.ofHom (thickMk Λ' I).toRingHom) := by
  refine isPullback_of_forall _ _ _ _ (fun _ ↦ rfl) ?_ ?_
  · intro r s h₁ h₂
    rw [Ideal.Quotient.mkₐ_eq_mk] at h₁
    have hI : r - s ∈ I := Ideal.Quotient.eq.mp h₁
    have h₃ : algebraMap Λ Λ' (r - s) = 0 := by
      have h := congrArg (fibreFst Λ' I) h₂
      rw [Algebra.ofId_apply, Algebra.ofId_apply, fibreFst_algebraMap,
        fibreFst_algebraMap] at h
      rw [map_sub, h, sub_self]
    exact sub_eq_zero.mp (hinj _ hI h₃)
  · intro c z h
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
    have hz : z - algebraMap Λ (fibre Λ' I) b ∈ thick Λ' I := by
      rw [← Ideal.Quotient.eq]
      exact h.symm
    obtain ⟨x, hx, hxz⟩ := exists_of_mem_thick Λ' hII hz
    refine ⟨b + x, ?_, ?_⟩
    · rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq, add_sub_cancel_left]
      exact hx
    · rw [Algebra.ofId_apply, map_add, ← hxz, add_sub_cancel]

variable (I)

/-- The retraction `fibre/thick → Λ/I` induced by the second projection. -/
def retraction : fibre Λ' I ⧸ thick Λ' I →ₐ[Λ] Λ ⧸ I :=
  Ideal.Quotient.liftₐ (thick Λ' I) (fibreSnd Λ' I) (fun z hz ↦ by
    have h : thick Λ' I ≤ RingHom.ker (fibreSnd Λ' I) := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, RingHom.mem_ker, fibreSnd_algebraMap,
        Ideal.Quotient.eq_zero_iff_mem]
      exact hx
    exact h hz)

lemma retraction_mk (z : fibre Λ' I) :
    retraction Λ' I (Ideal.Quotient.mk (thick Λ' I) z) = fibreSnd Λ' I z :=
  rfl

/-- The retraction composed with the quotient map is the second projection. -/
lemma retraction_comp_mkₐ :
    (retraction Λ' I).comp (thickMk Λ' I) = fibreSnd Λ' I :=
  Ideal.Quotient.liftₐ_comp _ _ _

/-- The retraction is a left inverse of the section `Λ/I → fibre/thick`. -/
lemma retraction_comp_secMap :
    (retraction Λ' I).comp (secMap Λ' I) = AlgHom.id Λ (Λ ⧸ I) := by
  ext c
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
  exact fibreSnd_algebraMap Λ' I b

lemma retraction_surjective : Function.Surjective (retraction Λ' I) := by
  intro c
  refine ⟨secMap Λ' I c, ?_⟩
  have h := congrArg (fun φ : Λ ⧸ I →ₐ[Λ] Λ ⧸ I ↦ φ c) (retraction_comp_secMap Λ' I)
  exact h

variable {I}

/-- An element of the fibre product with vanishing second projection has square zero. -/
lemma mul_self_eq_zero_of_fibreSnd (hII : I * I = ⊥) {r : fibre Λ' I}
    (hr : fibreSnd Λ' I r = 0) : r * r = 0 := by
  have hy : fibreFst Λ' I r ∈ I.map (algebraMap Λ Λ') := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, fibre_spec, hr, map_zero]
  have h0 : fibreFst Λ' I r * fibreFst Λ' I r = 0 := by
    have h := Ideal.mul_mem_mul hy hy
    rwa [← Ideal.map_mul, hII, Ideal.map_bot, Ideal.mem_bot] at h
  apply fibre_ext
  · rw [map_mul, h0, map_zero]
  · rw [map_mul, hr, mul_zero, map_zero]

/-- Over a local ring `Λ` and a proper ideal `I` with `I² = 0`, the ring `fibre/thick` is
local. -/
theorem isLocalRing_quotient_thick [IsLocalRing Λ] (hI : I ≠ ⊤) (hII : I * I = ⊥) :
    IsLocalRing (fibre Λ' I ⧸ thick Λ' I) := by
  have : Nontrivial (Λ ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have : IsLocalRing (Λ ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have : IsLocalHom (retraction Λ' I).toRingHom := by
    refine ⟨fun a ha ↦ ?_⟩
    obtain ⟨u, hu⟩ := ha.exists_right_inv
    obtain ⟨v, rfl⟩ := retraction_surjective Λ' I u
    obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (a * v - 1)
    have hw0 : fibreSnd Λ' I w = 0 := by
      rw [← retraction_mk, hw, map_sub, map_mul, map_one]
      have hu' : retraction Λ' I a * retraction Λ' I v = 1 := hu
      change retraction Λ' I a * retraction Λ' I v - 1 = 0
      rw [hu', sub_self]
    have hnil : IsNilpotent (a * v - 1) := by
      refine ⟨2, ?_⟩
      rw [← hw, pow_two, ← map_mul, mul_self_eq_zero_of_fibreSnd Λ' hII hw0, map_zero]
    have hunit : IsUnit (a * v) := by
      have := hnil.isUnit_one_add
      rwa [add_sub_cancel] at this
    obtain ⟨w', hw'⟩ := hunit
    have h1 : a * (v * ↑w'⁻¹) = 1 := by rw [← mul_assoc, ← hw', Units.mul_inv]
    exact ⟨⟨a, v * ↑w'⁻¹, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  exact (retraction Λ' I).toRingHom.domain_isLocalRing

end Langlands.AlgebraicGeometry.Picard.GenericThickening
