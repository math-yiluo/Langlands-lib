import Langlands.Global.AdelicFunctoriality.Finite
import Langlands.Global.AdelicFunctoriality.FiniteComparisonReduction

/-!
# Places below a common extension along an isomorphism of subfields

Let `K` and `K'` be number fields with algebra maps into a number field `L`, and let
`e : K ≃+* K'` be compatible with them. For every finite place `u` of `L`, the
isomorphism `e` carries the place of `K'` below `u` to the place of `K` below `u`, and the
inertia degrees of `u` over `K` and over `K'` agree. When `[L : K] = 1`, every inertia degree
of `L` over `K` is one.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Global.AdelicFunctoriality

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField

section Transport

variable {K K' L : Type*} [Field K] [Field K'] [Field L]
  [NumberField K] [NumberField K'] [NumberField L] [Algebra K L] [Algebra K' L]

omit [NumberField K] [NumberField K'] [NumberField L] in
/-- `e` carries the place of `K'` below `u` to the place of `K` below `u`. -/
theorem finitePlaceEquiv_under (e : K ≃+* K')
    (he : ∀ x, algebraMap K' L (e x) = algebraMap K L x) (u : HeightOneSpectrum (𝓞 L)) :
    finitePlaceEquiv e (u.under (𝓞 K')) = u.under (𝓞 K) := by
  apply HeightOneSpectrum.ext
  ext x
  rw [finitePlaceEquiv_mem, HeightOneSpectrum.under_asIdeal, HeightOneSpectrum.under_asIdeal,
    Ideal.mem_under, Ideal.mem_under]
  have hx : algebraMap (𝓞 K') (𝓞 L) (RingOfIntegers.mapRingEquiv e x) =
      algebraMap (𝓞 K) (𝓞 L) x :=
    RingOfIntegers.ext (he (x : K))
  rw [hx]

/-- The inertia degrees of `u` over `K` and over `K'` agree. -/
theorem inertiaDeg_eq_of_ringEquiv (e : K ≃+* K')
    (he : ∀ x, algebraMap K' L (e x) = algebraMap K L x) (u : HeightOneSpectrum (𝓞 L)) :
    u.asIdeal.inertiaDeg (𝓞 K) = u.asIdeal.inertiaDeg (𝓞 K') := by
  have hK : u.asIdeal.LiesOver (u.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have hK' : u.asIdeal.LiesOver (u.under (𝓞 K')).asIdeal := ⟨rfl⟩
  have hmK : (u.under (𝓞 K)).asIdeal.IsMaximal := (u.under (𝓞 K)).isMaximal
  have hmK' : (u.under (𝓞 K')).asIdeal.IsMaximal := (u.under (𝓞 K')).isMaximal
  have hmL : u.asIdeal.IsMaximal := u.isMaximal
  rw [Ideal.inertiaDeg_eq_of_isMaximal (u.under (𝓞 K)).asIdeal u.asIdeal,
    Ideal.inertiaDeg_eq_of_isMaximal (u.under (𝓞 K')).asIdeal u.asIdeal]
  let f : 𝓞 K ≃+* 𝓞 K' := RingOfIntegers.mapRingEquiv e
  have hcomap : (u.under (𝓞 K')).asIdeal.comap f.toRingHom = (u.under (𝓞 K)).asIdeal :=
    congrArg HeightOneSpectrum.asIdeal (finitePlaceEquiv_under e he u)
  have hmap : (u.under (𝓞 K')).asIdeal = (u.under (𝓞 K)).asIdeal.map (f : 𝓞 K →+* 𝓞 K') := by
    rw [← hcomap]
    exact (Ideal.map_comap_of_surjective f.toRingHom f.surjective _).symm
  refine Algebra.finrank_eq_of_equiv_equiv
    (Ideal.quotientEquiv _ _ f hmap) (RingEquiv.refl _) ?_
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun x => ?_)
  have hx : algebraMap (𝓞 K') (𝓞 L) (f x) = algebraMap (𝓞 K) (𝓞 L) x :=
    RingOfIntegers.ext (he (x : K))
  change algebraMap (𝓞 K' ⧸ (u.under (𝓞 K')).asIdeal) (𝓞 L ⧸ u.asIdeal)
      (Ideal.Quotient.mk _ (f x)) = algebraMap (𝓞 K ⧸ (u.under (𝓞 K)).asIdeal) (𝓞 L ⧸ u.asIdeal)
      (Ideal.Quotient.mk _ x)
  rw [Ideal.Quotient.algebraMap_mk_of_liesOver,
    Ideal.Quotient.algebraMap_mk_of_liesOver, hx]

end Transport

section Trivial

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-- In an extension of degree one, every inertia degree is one. -/
theorem inertiaDeg_eq_one_of_finrank_eq_one (h : Module.finrank K L = 1)
    (u : HeightOneSpectrum (𝓞 L)) : u.asIdeal.inertiaDeg (𝓞 K) = 1 := by
  classical
  let v := u.under (𝓞 K)
  have hu : u.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  have hsum := finitePlacesAbove_sum_ramification_inertia (L := L) v
  rw [h] at hsum
  have hle := Finset.single_le_sum (f := fun q : FinitePlacesAbove L v =>
      q.1.asIdeal.ramificationIdx (𝓞 K) * q.1.asIdeal.inertiaDeg (𝓞 K))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⟨u, hu⟩ : FinitePlacesAbove L v))
  rw [hsum] at hle
  have he : 0 < u.asIdeal.ramificationIdx (𝓞 K) := Ideal.ramificationIdx_pos (R := 𝓞 K) u.asIdeal
  have hf : 0 < u.asIdeal.inertiaDeg (𝓞 K) := Ideal.inertiaDeg_pos (R := 𝓞 K) u.asIdeal
  have hle' : u.asIdeal.ramificationIdx (𝓞 K) * u.asIdeal.inertiaDeg (𝓞 K) ≤ 1 := hle
  nlinarith

end Trivial

end Langlands.Global.AdelicFunctoriality
