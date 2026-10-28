import Langlands.Algebra.LocalAlgebraApproximationExistence
import Langlands.Algebra.TensorTransitionPrimeLocalization
import Langlands.Algebra.QuotientPushout
import Mathlib.RingTheory.TensorProduct.MvPolynomial

namespace Langlands.Algebra

noncomputable section

/-- A version of the quotient pushout criterion with a propositionally equal later ideal. -/
theorem isPushout_quotient_of_ideal_map_eq
    {A B Q Q' : Type*} [CommRing A] [CommRing B] [CommRing Q] [CommRing Q']
    [Algebra A B] [Algebra A Q] [Algebra A Q'] [Algebra B Q'] [Algebra Q Q']
    [IsScalarTower A B Q'] [IsScalarTower A Q Q']
    [_root_.Algebra.IsPushout A B Q Q']
    (I : Ideal Q) (J : Ideal Q') (hJ : I.map (algebraMap Q Q') = J)
    [Algebra (Q ⧸ I) (Q' ⧸ J)]
    [IsScalarTower A (Q ⧸ I) (Q' ⧸ J)]
    (hmap : (algebraMap (Q ⧸ I) (Q' ⧸ J)).comp (Ideal.Quotient.mk I) =
      (Ideal.Quotient.mk J).comp (algebraMap Q Q')) :
    _root_.Algebra.IsPushout A B (Q ⧸ I) (Q' ⧸ J) := by
  subst J
  exact isPushout_quotient_of_compatible_map I hmap

namespace LocalAlgebraApproximationExistence.Pres

variable {R₀ R S : Type*} [CommRing R₀] [CommRing R] [CommRing S] [Algebra R S]
  {e : R₀ ≃+* R} (P : Pres R₀ R S e)

/-- All relations descend to every base ring, so transition extends the relation ideal. -/
theorem rel_map {i j : Finset R₀} (h : i ≤ j) :
    (P.rel i).map (P.polyMap h) = P.rel j := by
  apply le_antisymm (Ideal.map_le_iff_le_comap.2 (P.rel_le_comap h))
  apply Ideal.span_le.2
  intro g hg
  have hgF : P.toPoly j g ∈ P.F := hg
  obtain ⟨g', hg'⟩ := P.exists_toPoly_eq (P.mem_B_of_mem_F i hgF)
  have he : P.polyMap h g' = g :=
    P.toPoly_injective j (by rw [P.toPoly_polyMap, hg'])
  rw [← he]
  apply Ideal.mem_map_of_mem
  exact P.mem_rel_of_toPoly_mem (hg' ▸ hgF)

theorem AMap_C {i j : Finset R₀} (h : i ≤ j) (b : P.B i) :
    P.AMap h (algebraMap (P.B i) (P.A i) b) =
      algebraMap (P.B j) (P.A j) (P.incl h b) := by
  rw [← P.mkA_C, P.AMap_mkA, P.polyMap_C, P.mkA_C]

/-- Prime localization for the actual base-change map of the constructed system. -/
theorem isPrimeLocalization_system [IsLocalRing S] [IsLocalRing R₀] [IsLocalRing R]
    [IsLocalHom (algebraMap R S)] {i j : Finset R₀} (h : i ≤ j) :
    P.system.IsPrimeLocalization h := by
  let : Algebra (P.B i) (P.B j) := (P.incl h).toAlgebra
  let : Algebra (P.Poly i) (P.Poly j) := MvPolynomial.algebraMvPolynomial
  let : Algebra (P.B i) (P.A j) :=
    inferInstanceAs (Algebra (P.B i) (P.Poly j ⧸ P.rel j))
  let : Algebra (P.A i) (P.A j) := (P.AMap h).toAlgebra
  let : IsScalarTower (P.B i) (P.B j) (P.A j) :=
    inferInstanceAs (IsScalarTower (P.B i) (P.B j) (P.Poly j ⧸ P.rel j))
  let : IsScalarTower (P.B i) (P.A i) (P.A j) :=
    IsScalarTower.of_algebraMap_eq fun b ↦ by
      change algebraMap (P.B j) (P.A j) (P.incl h b) =
        P.AMap h (algebraMap (P.B i) (P.A i) b)
      exact (P.AMap_C h b).symm
  have hpush : _root_.Algebra.IsPushout (P.B i) (P.B j) (P.A i) (P.A j) := by
    let : Algebra (P.Poly i ⧸ P.rel i) (P.Poly j ⧸ P.rel j) := (P.AMap h).toAlgebra
    let : IsScalarTower (P.B i) (P.Poly i ⧸ P.rel i) (P.Poly j ⧸ P.rel j) :=
      inferInstanceAs (IsScalarTower (P.B i) (P.A i) (P.A j))
    change _root_.Algebra.IsPushout (P.B i) (P.B j)
      (P.Poly i ⧸ P.rel i) (P.Poly j ⧸ P.rel j)
    apply isPushout_quotient_of_ideal_map_eq (P.rel i) (P.rel j) (P.rel_map h)
    apply RingHom.ext
    intro g
    exact P.AMap_mkA h g
  let : _root_.Algebra.IsPushout (P.B i) (P.A i) (P.B j) (P.A j) := hpush.symm
  let : Algebra (P.system.base i) (P.system.base j) := (P.system.baseMap i j h).toAlgebra
  let : Algebra (P.system.base i) (P.A i) := inferInstanceAs (Algebra (P.B i) (P.A i))
  let : Algebra (P.system.base i) (P.A j) := inferInstanceAs (Algebra (P.B i) (P.A j))
  let : Algebra (P.system.base j) (P.A j) := inferInstanceAs (Algebra (P.B j) (P.A j))
  let : IsScalarTower (P.system.base i) (P.A i) (P.A j) :=
    inferInstanceAs (IsScalarTower (P.B i) (P.A i) (P.A j))
  let : IsScalarTower (P.system.base i) (P.system.base j) (P.A j) :=
    inferInstanceAs (IsScalarTower (P.B i) (P.B j) (P.A j))
  let : _root_.Algebra.IsPushout (P.system.base i) (P.A i) (P.system.base j) (P.A j) :=
    hpush.symm
  let : Algebra (P.A i) (P.system.alg i) := inferInstanceAs (Algebra (P.A i) (P.Sl i))
  let : Algebra (P.A j) (P.system.alg j) := inferInstanceAs (Algebra (P.A j) (P.Sl j))
  let : IsScalarTower (P.system.base i) (P.A i) (P.system.alg i) :=
    inferInstanceAs (IsScalarTower (P.B i) (P.A i) (P.Sl i))
  let : IsScalarTower (P.system.base j) (P.A j) (P.system.alg j) :=
    inferInstanceAs (IsScalarTower (P.B j) (P.A j) (P.Sl j))
  let : IsLocalization (P.q i).primeCompl (P.system.alg i) :=
    inferInstanceAs (IsLocalization (P.q i).primeCompl (P.Sl i))
  let : IsLocalization (P.q j).primeCompl (P.system.alg j) :=
    inferInstanceAs (IsLocalization (P.q j).primeCompl (P.Sl j))
  apply LocalAlgebraSystem.isPrimeLocalization_of_quotient_pushout P.system h
    (P.q i).primeCompl (P.q j).primeCompl
  apply RingHom.ext
  intro a
  exact P.SlMap_algebraMap h a

end LocalAlgebraApproximationExistence.Pres

end

end Langlands.Algebra
