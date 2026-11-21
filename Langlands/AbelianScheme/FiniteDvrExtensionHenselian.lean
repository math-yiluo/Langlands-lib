import Langlands.AbelianScheme.PotentialSemistableReductionStatement
import Langlands.ClassFieldTheory.Local.SeparableInertiaNormReduction
import Langlands.FieldTheory.HenselianRealGaloisProlongationProof
import Langlands.FieldTheory.IntegerValuationRealization
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-! # Henselian ascent along a finite local extension of characteristic-zero traits -/

noncomputable section

open IsLocalRing Polynomial
open scoped NNReal WithZero

set_option autoImplicit false

universe u

namespace Langlands.AbelianScheme.FiniteDvrExtension

open Langlands.FieldTheory Langlands.ClassFieldTheory.Local.SeparableInertiaNorm

private theorem henselian_of_ringEquiv {R S : Type u} [CommRing R] [CommRing S]
    [HenselianLocalRing R] [IsLocalRing S] (e : R ≃+* S) : HenselianLocalRing S where
  is_henselian f hf x hx hd := by
    let g := f.map e.symm.toRingHom
    let : IsLocalHom e.toRingHom := isLocalHom_toRingHom e
    let : IsLocalHom e.symm.toRingHom := isLocalHom_toRingHom e.symm
    have heval (p : S[X]) (a : S) :
        (p.map e.symm.toRingHom).eval (e.symm a) = e.symm (p.eval a) := by
      change (p.map e.symm.toRingHom).eval (e.symm.toRingHom a) = e.symm.toRingHom (p.eval a)
      rw [eval_map, eval₂_hom]
    have he : g.eval (e.symm x) ∈ maximalIdeal R := by
      change (f.map e.symm.toRingHom).eval (e.symm x) ∈ _
      rw [heval]
      exact map_nonunit e.symm.toRingHom _ hx
    have hder : IsUnit (g.derivative.eval (e.symm x)) := by
      change IsUnit ((f.map e.symm.toRingHom).derivative.eval (e.symm x))
      rw [derivative_map, heval]
      exact hd.map e.symm
    obtain ⟨y, hy, hsub⟩ :=
      HenselianLocalRing.is_henselian g (hf.map _) (e.symm x) he hder
    refine ⟨e y, ?_, ?_⟩
    · change f.eval (e y) = 0
      apply e.symm.injective
      rw [← heval, e.symm_apply_apply, map_zero]
      exact hy.eq_zero
    · simpa using map_nonunit e.toRingHom _ hsub

private theorem henselian_of_valHensel {K : Type u} [Field K] (v : Valuation K ℝ≥0)
    (h : ValHensel v) : HenselianLocalRing v.valuationSubring where
  is_henselian f hf x hx hd := by
    let F := f.map (algebraMap v.valuationSubring K)
    have hF : IntPoly v F := by
      intro i
      change v ((f.map (algebraMap v.valuationSubring K)).coeff i) ≤ 1
      rw [coeff_map]
      exact (f.coeff i).2
    have hzero : v (F.eval (x : K)) < 1 := by
      rw [show F.eval (x : K) = _ from eval_lift f x]
      exact (Langlands.LocalGalois.Separable.mem_maximalIdeal_iff_lt v _).mp hx
    have hunit : v (F.derivative.eval (x : K)) = 1 := by
      change v ((f.map (algebraMap v.valuationSubring K)).derivative.eval (x : K)) = 1
      rw [derivative_map, eval_lift]
      exact (Langlands.LocalGalois.Separable.isUnit_iff_eq_one v _).mp hd
    obtain ⟨a, ha, hclose⟩ := h F (hf.map _) hF x x.property hzero hunit
    have haV : v a ≤ 1 := by
      rw [show a = (a - x) + x by ring]
      exact v.map_add_le hclose.le x.property
    let y : v.valuationSubring := ⟨a, haV⟩
    refine ⟨y, ?_, (Langlands.LocalGalois.Separable.mem_maximalIdeal_iff_lt v _).mpr hclose⟩
    change f.eval y = 0
    apply Subtype.val_injective
    exact (eval_lift f y).symm.trans ha

variable {V K : Type u} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [Field K] [Algebra V K] [IsFractionRing V K]

private theorem adicSubring_comap (E : FiniteDvrExtension V K) :
    (((IsDiscreteValuationRing.maximalIdeal E.ring).valuation E.fractionField).comap
      (algebraMap K E.fractionField)).valuationSubring =
    ((IsDiscreteValuationRing.maximalIdeal V).valuation K).valuationSubring := by
  let L := E.fractionField
  let u := (IsDiscreteValuationRing.maximalIdeal E.ring).valuation L
  let v := (IsDiscreteValuationRing.maximalIdeal V).valuation K
  let : IsLocalHom (algebraMap V E.ring) := E.localHom
  have hcomm (a : V) : algebraMap E.ring L (algebraMap V E.ring a) =
      algebraMap K L (algebraMap V K a) :=
    DFunLike.congr_fun E.mapsCommute a
  apply ValuationSubring.ext
  intro x
  change u (algebraMap K L x) ≤ 1 ↔ v x ≤ 1
  constructor
  · intro hx
    by_contra h
    have hxinv : v x⁻¹ ≤ 1 := (v.valuationSubring.mem_or_inv_mem x).resolve_left h
    obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hxinv
    obtain ⟨b, hb⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hx
    have hx0 : x ≠ 0 := by rintro rfl; simp at h
    have hab : algebraMap V E.ring a * b = 1 := by
      apply IsFractionRing.injective E.ring L
      rw [map_mul, map_one, hcomm, ha, hb, ← map_mul, inv_mul_cancel₀ hx0, map_one]
    have hua : IsUnit a := isUnit_of_map_unit (algebraMap V E.ring) a
      (isUnit_iff_exists_inv.mpr ⟨b, hab⟩)
    obtain ⟨c, hc⟩ := isUnit_iff_exists_inv.mp hua
    have hcx : algebraMap V K c = x := by
      apply (mul_left_cancel₀ (inv_ne_zero hx0) : x⁻¹ * algebraMap V K c = x⁻¹ * x → _)
      rw [inv_mul_cancel₀ hx0, ← ha, ← map_mul, hc, map_one]
    apply h
    rw [← hcx]
    exact (IsDiscreteValuationRing.maximalIdeal V).valuation_le_one (K := K) c
  · intro hx
    obtain ⟨a, rfl⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hx
    rw [← hcomm]
    exact (IsDiscreteValuationRing.maximalIdeal E.ring).valuation_le_one
      (K := L) (algebraMap V E.ring a)

/-- Henselianity ascends to the supplied local DVR in a finite extension of
characteristic-zero fraction fields. -/
theorem henselian_ring (E : FiniteDvrExtension V K) [HenselianLocalRing V] [CharZero K] :
    HenselianLocalRing E.ring := by
  let L := E.fractionField
  let : Module.Finite K L := E.finite
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  let Ω := AlgebraicClosure L
  let : IsGalois K Ω := {}
  let : IsGalois L Ω := {}
  let v := (IsDiscreteValuationRing.maximalIdeal V).valuation K
  let vL := (IsDiscreteValuationRing.maximalIdeal E.ring).valuation L
  let u := integerValuationToReal vL
  let w := realValuationProlongation (Ω := Ω) u
  have hwL : w.comap (algebraMap L Ω) = u := realValuationProlongation_comap u
  let wK := w.comap (algebraMap K Ω)
  have hwK : wK.valuationSubring = v.valuationSubring := by
    have hcomp : wK = u.comap (algebraMap K L) := by
      change w.comap (algebraMap K Ω) = _
      rw [IsScalarTower.algebraMap_eq K L Ω, Valuation.comap_comp, hwL]
    rw [hcomp, ← E.adicSubring_comap]
    apply ValuationSubring.ext
    intro x
    change (algebraMap K L x) ∈ u.valuationSubring ↔
      (algebraMap K L x) ∈ vL.valuationSubring
    rw [integerValuationToReal_valuationSubring]
  have : HenselianLocalRing wK.valuationSubring := by
    rw [hwK]
    exact henselian_of_ringEquiv (IsDiscreteValuationRing.equivValuationSubring (A := V) (K := K))
  have hnt : wK.IsNontrivial := by
    refine Valuation.isNontrivial_of_isEquiv ((Valuation.isEquiv_iff_valuationSubring _ _).mpr hwK.symm)
      (?_ : v.IsNontrivial)
    obtain ⟨π, hπ⟩ := (IsDiscreteValuationRing.maximalIdeal V).valuation_exists_uniformizer K
    change v π = _ at hπ
    exact ⟨π, by rw [hπ]; simp, by rw [hπ]; decide⟩
  have hinv : ∀ (σ : Ω ≃ₐ[K] Ω) (x : Ω), w (σ x) = w x := by
    apply valuation_invariant_of_finite_galois w
    intro F _ _
    have hF : (w.comap (algebraMap F Ω)).comap (algebraMap K F) = wK := by
      rw [← Valuation.comap_comp, ← IsScalarTower.algebraMap_eq]
    exact realValuation_invariant_of_finiteGalois wK hnt _ hF
  have : HenselianLocalRing w.valuationSubring := Langlands.LocalGalois.Separable.sepClosed_henselian _
  have hH : ValHensel u := hwL ▸ valHensel_comap (valHensel_of_henselian w)
    (fun σ x => hinv (σ.restrictScalars K) x)
    (fun x hx => (InfiniteGalois.mem_range_algebraMap_iff_fixed x).mpr hx)
  have hu : HenselianLocalRing u.valuationSubring := henselian_of_valHensel u hH
  have hsub : HenselianLocalRing vL.valuationSubring :=
    (integerValuationToReal_valuationSubring vL) ▸ hu
  exact henselian_of_ringEquiv
    (IsDiscreteValuationRing.equivValuationSubring (A := E.ring) (K := L)).symm

end Langlands.AbelianScheme.FiniteDvrExtension
