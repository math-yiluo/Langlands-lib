import Langlands.Galois.HeckeInduction.InducedCharacter
import Langlands.Galois.HeckeInduction.LocalCosets
import Langlands.Global.AdelicFunctoriality.FiniteComparisonReduction

/-!
# The induced representation at a base place where everything is unramified

`inducedObject e ψ` is the continuous representation of `Gal(K̄/K)` induced from a continuous
character `ψ` of `Gal(Ē/E)` through the image of restriction along `e`; its rank is `[E : K]`.
At a finite place `v` of `K` unramified in `E` and in the normal closure of `E`, where `ψ` is
unramified at every `w` above `v` with value `c w` at every geometric Frobenius lift,
`hasEulerPolynomialAt_inducedObject` proves that the induced representation is unramified at `v`
with Euler polynomial `∏_w (1 - c w X ^ f(w|v))`. The cycles of geometric Frobenius on the right
cosets are the cosets of `placeConj e v w * σ ^ k` with `k < f(w|v)` (`cycle_bijective`).
-/

noncomputable section

universe uK uE uC

namespace Langlands.GaloisRepresentation.HeckeInduction

open Langlands.FiniteRepresentation Langlands.FiniteRepresentation.Induction
open Langlands.FiniteRepresentation.InducedCharacter
open Langlands.Global.AdelicFunctoriality Langlands.GaloisRepresentation.QuadraticFrobeniusPatching
open Polynomial NumberField
open scoped NumberField Classical

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable {K : Type uK} {E : Type uE} [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E]
variable {C : Type uC} [Field C] [TopologicalSpace C] [IsTopologicalRing C]

/-- The image of the absolute Galois group of `E` in that of `K`. -/
abbrev imageSubgroup (e : AlgebraicClosure K →ₐ[K] AlgebraicClosure E) :
    Subgroup (Field.absoluteGaloisGroup K) :=
  (restrictionAlongClosure e).toMonoidHom.range

instance (e : AlgebraicClosure K →ₐ[K] AlgebraicClosure E) : (imageSubgroup e).FiniteIndex :=
  finiteIndex_range_restrictionAlongClosure e

variable (e : AlgebraicClosure K →ₐ[K] AlgebraicClosure E)
  (ψ : Field.absoluteGaloisGroup E →ₜ* Cˣ)

/-- The character of the image subgroup corresponding to `ψ`. -/
abbrev descended : imageSubgroup e →* Cˣ := descendedCharacter e ψ.toMonoidHom

omit [IsTopologicalRing C] in
theorem descended_apply (s : Field.absoluteGaloisGroup E) :
    descended e ψ ⟨restrictionAlongClosure e s, ⟨s, rfl⟩⟩ = ψ s :=
  descendedCharacter_apply e ψ.toMonoidHom s

/-- **The induced continuous representation.** Finite-index induction of the descended
character, with continuity on the open image subgroup. -/
def inducedObject : Objects.{uK, uC, max uK uC} K C :=
  ⟨induced (imageSubgroup e) (descended e ψ),
    continuous_induced (isOpen_range_restrictionAlongClosure e) _
      (Units.continuous_val.comp (continuous_descendedCharacter e ψ.toMonoidHom ψ.continuous))⟩

theorem inducedObject_rank : (inducedObject e ψ).val.rank = Module.finrank K E := by
  change (induced (imageSubgroup e) (descended e ψ)).rank = _
  rw [rank_induced, index_range_restrictionAlongClosure]

section Place

variable (v : Global.FinitePlace K)

local notation "rv" => Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v)

/-- **Inertia acts trivially.** For a representative `h * placeConj * σ ^ k` of a right coset
and an element `i` of local inertia, the conjugate of the image of `i` lies in the image
subgroup and is killed by the descended character. -/
theorem conj_inertia
    (hM : Algebra.IsUnramifiedAt (𝓞 K) (inducedPlace v (normalClosureField (E := E))).asIdeal)
    (w : FinitePlacesAbove E v)
    (hunr : ∀ a ∈ localInertia w.1,
      ψ (Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding w.1) a) = 1)
    (γ : LocalGroup v) (k : ℕ) (h : Field.absoluteGaloisGroup K) (hh : h ∈ imageSubgroup e)
    (i : LocalGroup v) (hi : i ∈ localInertia v) :
    ∃ hx : (h * placeConj e v w.1 * rv γ ^ k) * rv i * (h * placeConj e v w.1 * rv γ ^ k)⁻¹ ∈
        imageSubgroup e, descended e ψ ⟨_, hx⟩ = 1 := by
  have hi' : γ ^ k * i * (γ ^ k)⁻¹ ∈ localInertia v :=
    (inferInstance : (localInertia v).Normal).conj_mem i hi (γ ^ k)
  obtain ⟨a, ha⟩ := inertia_mem_range e v w.1 (inertia_fixes_conjugates e v hM) _ hi'
  have ha' : Field.absoluteGaloisGroup.map (FiniteExtension.completionMap v w.1) a =
      γ ^ k * i * (γ ^ k)⁻¹ := ha
  have haI : a ∈ localInertia w.1 := by
    rw [← map_mem_inertia_iff (FiniteExtension.completionMap v w.1)
      (completionMap_norm_le_one_iff v w.1) (completionMap_isAlgebraic v w.1), ha']
    exact hi'
  have hrel := conj_placeConj_map e v w.1 a
  have heq : (h * placeConj e v w.1 * rv γ ^ k) * rv i * (h * placeConj e v w.1 * rv γ ^ k)⁻¹ =
      h * restrictionAlongClosure e
        (Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding w.1) a) * h⁻¹ := by
    rw [← hrel, ha', map_mul, map_mul, map_inv, map_pow]
    group
  have hmem : (h * placeConj e v w.1 * rv γ ^ k) * rv i * (h * placeConj e v w.1 * rv γ ^ k)⁻¹ ∈
      imageSubgroup e := by
    rw [heq]
    exact mul_mem (mul_mem hh ⟨_, rfl⟩) (inv_mem hh)
  refine ⟨hmem, ?_⟩
  have hsub : (⟨_, hmem⟩ : imageSubgroup e) = ⟨h, hh⟩ *
      ⟨restrictionAlongClosure e
        (Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding w.1) a), ⟨_, rfl⟩⟩ *
      (⟨h, hh⟩ : imageSubgroup e)⁻¹ := Subtype.ext heq
  rw [hsub, map_mul, map_mul, map_inv, descended_apply, hunr a haI, mul_one, mul_inv_cancel]

/-- **Frobenius values.** On the cycle of `placeConj`, the return element has the value of `ψ`
at a geometric Frobenius lift at `w`. -/
theorem descended_conj_frobenius
    (hM : Algebra.IsUnramifiedAt (𝓞 K) (inducedPlace v (normalClosureField (E := E))).asIdeal)
    (w : FinitePlacesAbove E v)
    (hunr : ∀ a ∈ localInertia w.1,
      ψ (Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding w.1) a) = 1)
    (c : C) (hfrob : ∀ a, IsGeometricFrobeniusLift w.1 a →
      (ψ (Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding w.1) a) : C) = c)
    {γ : LocalGroup v} (hγ : IsGeometricFrobeniusLift v γ)
    (hmem : placeConj e v w.1 * rv γ ^ w.1.asIdeal.inertiaDeg (𝓞 K) * (placeConj e v w.1)⁻¹ ∈
      imageSubgroup e) :
    (descended e ψ ⟨_, hmem⟩ : C) = c := by
  obtain ⟨a, ha⟩ := exists_geometricFrobeniusLift w.1
  have hres := residueAction_map_eq_pow (FiniteExtension.completionMap v w.1)
    (completionMap_norm_le_one_iff v w.1) (completionMap_isAlgebraic v w.1) _
    (residueCardinality_eq_pow v w.1) ha hγ
  have hi : (γ ^ w.1.asIdeal.inertiaDeg (𝓞 K))⁻¹ *
      Field.absoluteGaloisGroup.map (FiniteExtension.completionMap v w.1) a ∈ localInertia v := by
    change localResidueAction v _ = 1
    rw [map_mul, map_inv, hres, inv_mul_cancel]
  obtain ⟨hx, hφ⟩ := conj_inertia e ψ v hM w hunr γ 0 1 (one_mem _) _ hi
  have hrel := conj_placeConj_map e v w.1 a
  have heq : restrictionAlongClosure e
      (Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding w.1) a) =
      (placeConj e v w.1 * rv γ ^ w.1.asIdeal.inertiaDeg (𝓞 K) * (placeConj e v w.1)⁻¹) *
        ((1 * placeConj e v w.1 * rv γ ^ 0) * rv ((γ ^ w.1.asIdeal.inertiaDeg (𝓞 K))⁻¹ *
          Field.absoluteGaloisGroup.map (FiniteExtension.completionMap v w.1) a) *
          (1 * placeConj e v w.1 * rv γ ^ 0)⁻¹) := by
    rw [← hrel, map_mul, map_inv, map_pow]
    group
  have hsub : (⟨restrictionAlongClosure e
      (Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding w.1) a), ⟨_, rfl⟩⟩ :
        imageSubgroup e) = ⟨_, hmem⟩ * ⟨_, hx⟩ := Subtype.ext heq
  have h2 := congrArg (descended e ψ) hsub
  rw [descended_apply, map_mul, hφ, mul_one] at h2
  rw [← h2]
  exact hfrob a ha

/-- Inertia acts trivially, for an arbitrary element of a right coset of `placeConj * σ ^ k`. -/
theorem conj_inertia_of_mem
    (hM : Algebra.IsUnramifiedAt (𝓞 K) (inducedPlace v (normalClosureField (E := E))).asIdeal)
    (w : FinitePlacesAbove E v)
    (hunr : ∀ a ∈ localInertia w.1,
      ψ (Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding w.1) a) = 1)
    (γ : LocalGroup v) (k : ℕ) (y : Field.absoluteGaloisGroup K)
    (hy : y * (placeConj e v w.1 * rv γ ^ k)⁻¹ ∈ imageSubgroup e)
    (i : LocalGroup v) (hi : i ∈ localInertia v) :
    ∃ hx : y * rv i * y⁻¹ ∈ imageSubgroup e, descended e ψ ⟨_, hx⟩ = 1 := by
  have h := conj_inertia e ψ v hM w hunr γ k _ hy i hi
  have hyeq : y * (placeConj e v w.1 * rv γ ^ k)⁻¹ * placeConj e v w.1 * rv γ ^ k = y := by group
  rw [hyeq] at h
  exact h

/-- **The cycles of a geometric Frobenius on the right cosets.** At a base place unramified in
`E` and in its normal closure, the cosets of `placeConj e v w * σ ^ k`, for the places `w` above
`v` and `k < f(w|v)`, are all the right cosets, each exactly once. -/
theorem cycle_bijective
    (hram : ∀ w : FinitePlacesAbove E v, w.1.asIdeal.ramificationIdx (𝓞 K) = 1)
    {γ : LocalGroup v} (hγ : IsGeometricFrobeniusLift v γ) :
    Function.Bijective (fun i : Σ w : FinitePlacesAbove E v, Fin (w.1.asIdeal.inertiaDeg (𝓞 K)) =>
      coset (imageSubgroup e) (placeConj e v i.1.1 * rv γ ^ (i.2 : ℕ))) := by
  have hinj : Function.Injective
      (fun i : Σ w : FinitePlacesAbove E v, Fin (w.1.asIdeal.inertiaDeg (𝓞 K)) =>
        coset (imageSubgroup e) (placeConj e v i.1.1 * rv γ ^ (i.2 : ℕ))) := by
    rintro ⟨w, k⟩ ⟨w', k'⟩ hcos
    have h1 := (coset_eq_iff _ _).mp hcos
    have hp := cosetPrime_eq_of_coset_eq e v (placeConj e v w.1) (placeConj e v w'.1)
      (γ ^ (k : ℕ)) (γ ^ (k' : ℕ)) (by rwa [map_pow, map_pow])
    rw [cosetPrime_placeConj, cosetPrime_placeConj] at hp
    have hw : w' = w := Subtype.ext (IsDedekindDomain.HeightOneSpectrum.ext hp)
    subst hw
    have key : ∀ a b : Fin (w'.1.asIdeal.inertiaDeg (𝓞 K)), (a : ℕ) < b →
        (placeConj e v w'.1 * rv γ ^ (b : ℕ)) * (placeConj e v w'.1 * rv γ ^ (a : ℕ))⁻¹ ∈
          imageSubgroup e → False := by
      intro a b hab hmem
      have hsplit : (b : ℕ) = a + ((b : ℕ) - a) := by omega
      have heq : (placeConj e v w'.1 * rv γ ^ (b : ℕ)) * (placeConj e v w'.1 * rv γ ^ (a : ℕ))⁻¹ =
          placeConj e v w'.1 * rv (γ ^ ((b : ℕ) - a)) * (placeConj e v w'.1)⁻¹ := by
        rw [map_pow, hsplit, pow_add, Nat.add_sub_cancel_left]
        group
      rw [heq, conj_mem_iff_mem_range] at hmem
      exact pow_not_mem_range v w'.1 hγ (by omega) (by omega) hmem
    rcases lt_trichotomy (k : ℕ) k' with hlt | heq | hgt
    · exact (key k k' hlt h1).elim
    · exact congrArg (Sigma.mk w') (Fin.ext heq)
    · have h2 := inv_mem h1
      rw [mul_inv_rev, inv_inv] at h2
      exact (key k' k hgt h2).elim
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, ?_⟩
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  have hsum := finitePlacesAbove_sum_ramification_inertia (L := E) v
  simp only [hram, one_mul] at hsum
  rw [hsum, QuotientGroup.card_quotient_rightRel, ← Nat.card_eq_fintype_card]
  exact (index_range_restrictionAlongClosure e).symm

/-- **The induced representation at a good base place.** If `E/K` and its normal closure are
unramified above `v`, and `ψ` is unramified at every `w` above `v` with value `c w` at every
geometric Frobenius lift, the induced representation is unramified at `v` and its Euler
polynomial is `∏_w (1 - c w X ^ f(w|v))`. -/
theorem hasEulerPolynomialAt_inducedObject
    (hram : ∀ w : FinitePlacesAbove E v, w.1.asIdeal.ramificationIdx (𝓞 K) = 1)
    (hM : Algebra.IsUnramifiedAt (𝓞 K) (inducedPlace v (normalClosureField (E := E))).asIdeal)
    (c : FinitePlacesAbove E v → C)
    (hunr : ∀ w : FinitePlacesAbove E v, ∀ a ∈ localInertia w.1,
      ψ (Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding w.1) a) = 1)
    (hfrob : ∀ w : FinitePlacesAbove E v, ∀ a, IsGeometricFrobeniusLift w.1 a →
      (ψ (Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding w.1) a) : C) = c w) :
    HasEulerPolynomialAt (inducedObject e ψ) v
      (∏ w : FinitePlacesAbove E v, (1 - Polynomial.C (c w) * X ^ w.1.asIdeal.inertiaDeg (𝓞 K))) := by
  obtain ⟨γ, hγ⟩ := exists_geometricFrobeniusLift v
  have hbij := cycle_bijective e v hram hγ
  have hmem : ∀ w : FinitePlacesAbove E v,
      placeConj e v w.1 * rv γ ^ w.1.asIdeal.inertiaDeg (𝓞 K) * (placeConj e v w.1)⁻¹ ∈
        imageSubgroup e := fun w => by
    rw [← map_pow, conj_mem_iff_mem_range]
    exact pow_inertiaDeg_mem_range v w.1
      (inertia_mem_range e v w.1 (inertia_fixes_conjugates e v hM)) hγ
  refine ⟨?_, γ, hγ, ?_⟩
  · intro i
    change (induced (imageSubgroup e) (descended e ψ)).representation (rv i.val) = 1
    apply induced_eq_one
    intro y
    obtain ⟨⟨w, k⟩, hk⟩ := hbij.2 (coset (imageSubgroup e) y)
    exact conj_inertia_of_mem e ψ v hM w (hunr w) γ k y ((coset_eq_iff _ _).mp hk) i.val i.prop
  · have hlen : ∀ w : FinitePlacesAbove E v, 0 < w.1.asIdeal.inertiaDeg (𝓞 K) :=
      fun w => Ideal.inertiaDeg_pos w.1.asIdeal (𝓞 K)
    have hdet := det_one_sub_X_smul_induced (S := imageSubgroup e) (descended e ψ) (rv γ)
      (W := FinitePlacesAbove E v) (fun w => placeConj e v w.1)
      (fun w => w.1.asIdeal.inertiaDeg (𝓞 K)) hlen hmem hbij
    have hE : eulerPolynomial (atFinitePlace v (inducedObject e ψ)) γ =
        Matrix.det (1 - (X : C[X]) • (LinearMap.toMatrix (cosetBasis (descended e ψ))
          (cosetBasis (descended e ψ))
            ((induced (imageSubgroup e) (descended e ψ)).representation (rv γ))).map
              Polynomial.C) :=
      eulerPolynomial_eq_det (atFinitePlace v (inducedObject e ψ)) (cosetBasis (descended e ψ)) γ
    rw [hE, hdet]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [descended_conj_frobenius e ψ v hM w (hunr w) (c w) (hfrob w) hγ (hmem w)]

end Place

end Langlands.GaloisRepresentation.HeckeInduction
