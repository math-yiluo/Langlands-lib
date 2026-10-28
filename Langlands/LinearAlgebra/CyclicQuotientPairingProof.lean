import Langlands.LinearAlgebra.CyclicQuotientPairingStatement
import Mathlib.Algebra.Algebra.Bilinear

/-!
# A balanced nondegenerate pairing on a cyclic polynomial quotient

The pairing extracts the top coefficient of the reduced representative of a
product. We first work with a monic polynomial and then transport along the
algebra equivalence associated with normalization.
-/

namespace Langlands

universe uK

open Polynomial

private theorem cyclicQuotientPairing_monic (K : Type uK) [Field K]
    (q : Polynomial K) (hq : q.Monic) :
    ∃ B : LinearMap.BilinForm K (AdjoinRoot q),
      B.IsSymm ∧ B.Nondegenerate ∧
        ∀ (a u v : AdjoinRoot q), B (a * u) v = B u (a * v) := by
  classical
  let L : AdjoinRoot q →ₗ[K] K :=
    (lcoeff K (q.natDegree - 1)).comp (AdjoinRoot.modByMonicHom hq)
  let B : LinearMap.BilinForm K (AdjoinRoot q) :=
    (LinearMap.mul K (AdjoinRoot q)).compr₂ L
  have hB (u v : AdjoinRoot q) : B u v = L (u * v) := rfl
  have hsym : B.IsSymm := ⟨fun u v => by rw [hB, hB, mul_comm]⟩
  have hsep : ∀ u : AdjoinRoot q, (∀ v, B u v = 0) → u = 0 := by
    intro u hu
    suffices hr : AdjoinRoot.modByMonicHom hq u = 0 by
      rw [← AdjoinRoot.mk_leftInverse hq u, hr, map_zero]
    by_contra hr
    let r := AdjoinRoot.modByMonicHom hq u
    have hr0 : r ≠ 0 := hr
    have hrdeg : r.degree < q.degree := by
      obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective u
      exact degree_modByMonic_lt p hq
    have hnat : r.natDegree < q.natDegree := natDegree_lt_natDegree hr0 hrdeg
    let n := q.natDegree - 1 - r.natDegree
    have hsum : r.natDegree + n = q.natDegree - 1 := by
      dsimp [n]
      omega
    have hprod : (r * X ^ n).degree < q.degree := by
      rw [degree_eq_natDegree (mul_ne_zero hr0 (pow_ne_zero _ X_ne_zero)),
        natDegree_mul_X_pow n hr0, hsum, degree_eq_natDegree hq.ne_zero]
      exact_mod_cast (show q.natDegree - 1 < q.natDegree by omega)
    have hred :
        AdjoinRoot.modByMonicHom hq (u * AdjoinRoot.mk q (X ^ n)) = r * X ^ n := by
      rw [← show AdjoinRoot.mk q r = u from AdjoinRoot.mk_leftInverse hq u,
        ← map_mul, AdjoinRoot.modByMonicHom_mk, (modByMonic_eq_self_iff hq).mpr hprod]
    have hzero : (r * X ^ n).coeff (q.natDegree - 1) = 0 := by
      simpa only [hB, L, LinearMap.comp_apply, lcoeff_apply, hred] using
        hu (AdjoinRoot.mk q (X ^ n))
    rw [← hsum, coeff_mul_X_pow] at hzero
    exact (leadingCoeff_ne_zero.mpr hr0) hzero
  refine ⟨B, hsym, ⟨hsep, ?_⟩, ?_⟩
  · intro v hv
    exact hsep v (fun u => (hsym.eq v u).trans (hv u))
  · intro a u v
    rw [hB, hB]
    congr 1
    ac_rfl

/-- Every nonzero polynomial quotient over a field has a symmetric nondegenerate
bilinear form balanced under multiplication by any quotient element. -/
theorem cyclicQuotientPairing : CyclicQuotientPairingStatement.{uK} := by
  classical
  intro K _ q hq
  obtain ⟨B, hsym, hnon, hbal⟩ :=
    cyclicQuotientPairing_monic K (normalize q) (monic_normalize hq)
  let e : AdjoinRoot q ≃ₐ[K] AdjoinRoot (normalize q) :=
    AdjoinRoot.algEquivOfAssociated K q (normalize q) (normalize_associated q).symm
  let B' : LinearMap.BilinForm K (AdjoinRoot q) :=
    B.comp e.toLinearMap e.toLinearMap
  refine ⟨B', ⟨fun u v => hsym.eq (e u) (e v)⟩, ⟨?_, ?_⟩, ?_⟩
  · intro u hu
    apply e.injective
    have he : e u = 0 := hnon.1 (e u) (fun v => by
      simpa only [B', LinearMap.BilinForm.comp_apply, AlgEquiv.toLinearMap_apply,
        AlgEquiv.apply_symm_apply] using hu (e.symm v))
    simpa only [map_zero] using he
  · intro v hv
    apply e.injective
    have he : e v = 0 := hnon.2 (e v) (fun u => by
      simpa only [B', LinearMap.BilinForm.comp_apply, AlgEquiv.toLinearMap_apply,
        AlgEquiv.apply_symm_apply] using hv (e.symm u))
    simpa only [map_zero] using he
  · intro a u v
    simpa only [B', LinearMap.BilinForm.comp_apply, AlgEquiv.toLinearMap_apply,
      map_mul] using hbal (e a) (e u) (e v)

end Langlands
