import Langlands.Geometry.Analytic.ClosedIdealsBanach
import Langlands.Geometry.Analytic.NoetherNormalizationLift
import Langlands.Geometry.Analytic.TateNoetherian
import Langlands.Geometry.Analytic.SpectralMinpoly

/-! # Bounded monic relations modulo actual prime ideals -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedStrictAffinoidAlgebra

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]

/-- For every actual prime quotient, construct a monic polynomial over the
original Tate presentation whose coefficients have norm at most one and
whose evaluation lies in the prime ideal. Closedness, normalization and
the coefficient lift are proved rather than assumed. -/
theorem exists_monic_relation_mem_prime
    (P : PresentedStrictAffinoidAlgebra K) (I : Ideal P) [I.IsPrime]
    (a : P) (ha : ∀ x : BanachSpectrum P, x a ≤ 1) :
    ∃ p : Polynomial (StrictTateAlgebra (Fin P.arity) K),
      p.Monic ∧ (∀ i, ‖p.coeff i‖ ≤ 1) ∧
      p.eval₂ (presentationMap K P).toAlgHom.toRingHom a ∈ I := by
  let _ : IsClosed (I : Set P) :=
    isClosed_ideal_of_noetherian_banach (K := K) I
  let Q := P ⧸ I
  let q : BoundedAlgHom K P Q :=
    { toAlgHom := Ideal.Quotient.mkₐ K I
      bounded := ⟨1, zero_lt_one, fun a => by
        rw [one_mul]
        change ‖Ideal.Quotient.mk I a‖ ≤ ‖a‖
        exact Ideal.Quotient.norm_mk_le I a⟩ }
  let h := q.comp (presentationMap K P)
  have hsurj : Function.Surjective h :=
    (Ideal.Quotient.mkₐ_surjective K I).comp (presentationMap_surjective K P)
  have hfinite : h.toAlgHom.toRingHom.Finite :=
    RingHom.Finite.of_surjective h.toAlgHom.toRingHom hsurj
  obtain ⟨n, _hn, g, hgnorm, hinj, hfin⟩ :=
    StrictTateAlgebra.exists_normalizing_embedding P.arity h hfinite
  let φ := h.comp g
  let T := StrictTateAlgebra (Fin n) K
  let _ : Algebra T Q := φ.toAlgHom.toRingHom.toAlgebra
  let _ : IsScalarTower K T Q :=
    IsScalarTower.of_algebraMap_eq fun c => (φ.toAlgHom.commutes c).symm
  let _ : Module.Finite T Q := hfin
  let _ : Module.IsTorsionFree T Q :=
    (Module.isTorsionFree_iff_algebraMap_injective (R := T) (A := Q)).mpr hinj
  have hcontinuous : Continuous (algebraMap T Q) := by
    obtain ⟨M, _hM, hbound⟩ := φ.bounded
    exact AddMonoidHomClass.continuous_of_bound φ.toAlgHom M hbound
  have hspec : ∀ x : BanachSpectrum Q, x (q a) ≤ 1 :=
    fun x => ha (BanachSpectrum.comap q.toBoundedRingHom x)
  let p := minpoly T (q a)
  have hp : p.Monic := minpoly.monic (IsIntegral.of_finite T (q a))
  have hcoeff : ∀ i, ‖p.coeff i‖ ≤ 1 :=
    StrictTateAlgebra.minpoly_coeff_norm_le_one n hcontinuous (q a) hspec
  refine ⟨p.map g.toAlgHom.toRingHom, hp.map _, ?_, ?_⟩
  · intro i
    rw [Polynomial.coeff_map]
    change ‖g (p.coeff i)‖ ≤ 1
    rw [hgnorm]
    exact hcoeff i
  · apply (Ideal.Quotient.eq_zero_iff_mem).mp
    change q.toAlgHom.toRingHom
      ((p.map g.toAlgHom.toRingHom).eval₂
        (presentationMap K P).toAlgHom.toRingHom a) = 0
    rw [Polynomial.eval₂_map, Polynomial.hom_eval₂]
    exact minpoly.aeval T (q a)

end Langlands.Analytic.PresentedStrictAffinoidAlgebra
