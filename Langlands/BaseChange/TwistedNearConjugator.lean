import Langlands.BaseChange.CyclicAlgebraTopology
import Langlands.BaseChange.FiniteAlgebraUnits
import Langlands.BaseChange.RegularCyclicBasis
import Langlands.BaseChange.SigmaLiftCharacterIdentity.Parameters
import Langlands.TraceFormula.TwistedOrbital

noncomputable section

open Filter Matrix Set Topology

namespace Langlands.BaseChange

open Langlands.TraceFormula

universe u v w

variable {F : Type u} [Field F] {E : Type v} [CommRing E] [Algebra F E] {n : ℕ}

local notation "M" => Matrix (Fin n) (Fin n) E
local notation "G" => GeneralLinear n E

private def twistedIntertwiner (σ : E ≃ₐ[F] E) (s x : G) : M →ₗ[F] M where
  toFun a := s.val * (σ.toRingHom.mapMatrix a) * x⁻¹.val
  map_add' a b := by rw [map_add, mul_add, add_mul]
  map_smul' r a := by
    have hm : σ.toRingHom.mapMatrix (r • a) = r • σ.toRingHom.mapMatrix a := by
      ext i j
      exact σ.toLinearEquiv.map_smul r (a i j)
    rw [hm, mul_smul_comm, smul_mul_assoc, RingHom.id_apply]

private theorem iterate_twistedIntertwiner (σ : E ≃ₐ[F] E) (s x : G) (i : ℕ) (a : M) :
    (twistedIntertwiner σ s x : M → M)^[i] a =
      (cyclicNorm σ i s).val * (σ ^ i).toRingHom.mapMatrix a *
        (cyclicNorm σ i x)⁻¹.val := by
  induction i generalizing a with
  | zero =>
      simp only [Function.iterate_zero_apply, cyclicNorm_zero, Units.val_one, inv_one,
        one_mul, mul_one, pow_zero]
      rfl
  | succ i ih =>
      rw [Function.iterate_succ_apply, ih, cyclicNorm_succ, cyclicNorm_succ, _root_.mul_inv_rev]
      have hm : (σ ^ i).toRingHom.mapMatrix (σ.toRingHom.mapMatrix a) =
          (σ ^ (i + 1)).toRingHom.mapMatrix a := by
        ext j k
        change (σ ^ i) (σ (a j k)) = (σ ^ (i + 1)) (a j k)
        rw [pow_succ, AlgEquiv.mul_apply]
      change _ * (σ ^ i).toRingHom.mapMatrix
        (s.val * σ.toRingHom.mapMatrix a * x⁻¹.val) * _ = _
      rw [map_mul, map_mul, hm]
      have hx : (σ ^ i).toRingHom.mapMatrix x⁻¹.val =
          ((entrywiseAut (σ ^ i) n x)⁻¹).val := by
        rw [← map_inv]
        rfl
      rw [hx]
      simp only [Units.val_mul, mul_assoc]
      rfl

private theorem map_sum_iterate_eq_self {T : M →ₗ[F] M} {l : ℕ} {a : M}
    (h : (T : M → M)^[l] a = a) :
    T (∑ i ∈ Finset.range l, (T : M → M)^[i] a) =
      ∑ i ∈ Finset.range l, (T : M → M)^[i] a := by
  let f i := (T : M → M)^[i] a
  have hstep (i : ℕ) : T (f i) = f (i + 1) := (Function.iterate_succ_apply' ..).symm
  have hsum := Finset.sum_range_succ f l
  rw [Finset.sum_range_succ' f l] at hsum
  change (∑ i ∈ Finset.range l, f (i + 1)) + f 0 =
    (∑ i ∈ Finset.range l, f i) + f l at hsum
  change T (∑ i ∈ Finset.range l, f i) = ∑ i ∈ Finset.range l, f i
  simp only [map_sum, hstep]
  exact add_right_cancel (by simpa only [f, Function.iterate_zero_apply, h] using hsum)

variable [TopologicalSpace F] [TopologicalSpace E] [IsTopologicalRing E] [IsModuleTopology F E]

private theorem continuous_cyclicBasisMatrix (v : Fin n → E) :
    Continuous (fun a : M => cyclicBasisMatrix a v) :=
  continuous_matrix fun i j => (continuous_apply i).comp
    ((continuous_id.pow (j : ℕ)).matrix_mulVec continuous_const)

variable [IsTopologicalDivisionRing F] [T1Space F] [Module.Finite F E]

private theorem exists_tendsto_cyclicIntertwiner {Z : Type w} {L : Filter Z}
    {s x : Z → G} {δ : G} {σ : E ≃ₐ[F] E} {l : ℕ}
    (hs : Tendsto s L (𝓝 δ)) (hx : Tendsto x L (𝓝 δ))
    {v : Fin n → E} (hv : IsUnit (cyclicBasisMatrix (cyclicNorm σ l δ).val v))
    (hp : ∀ᶠ z in L, (cyclicNorm σ l (s z)).val.charpoly = (cyclicNorm σ l (x z)).val.charpoly) :
    ∃ g : Z → G, Tendsto g L (𝓝 1) ∧
      ∀ᶠ z in L, cyclicNorm σ l (s z) * g z = g z * cyclicNorm σ l (x z) := by
  let : IsModuleTopology F M := inferInstanceAs (IsModuleTopology F (Fin n → Fin n → E))
  let c (y : G) := cyclicBasisMatrix (cyclicNorm σ l y).val v
  have hc : Continuous c := (continuous_cyclicBasisMatrix v).comp
    (Units.continuous_val.comp (SigmaLiftCharacterIdentity.continuous_cyclicNorm σ l))
  have hs' : Tendsto (c ∘ s) L (𝓝 (hv.unit : M)) := by
    rw [hv.unit_spec]
    exact hc.continuousAt.tendsto.comp hs
  have hx' : Tendsto (c ∘ x) L (𝓝 (hv.unit : M)) := by
    rw [hv.unit_spec]
    exact hc.continuousAt.tendsto.comp hx
  obtain ⟨a, ha, hea⟩ := finiteAlgebra_exists_tendsto_unit (F := F) hs'
  obtain ⟨b, hb, heb⟩ := finiteAlgebra_exists_tendsto_unit (F := F) hx'
  refine ⟨fun z => a z * (b z)⁻¹, by simpa only [mul_inv_cancel] using ha.mul hb.inv, ?_⟩
  filter_upwards [hea, heb, hp] with z haz hbz hpz
  change (a z : M) = c (s z) at haz
  change (b z : M) = c (x z) at hbz
  have hA : IsUnit (c (s z)) := haz ▸ (a z).isUnit
  have hB : IsUnit (c (x z)) := hbz ▸ (b z).isUnit
  have ea : hA.unit = a z := Units.ext (hA.unit_spec.trans haz.symm)
  have eb : hB.unit = b z := Units.ext (hB.unit_spec.trans hbz.symm)
  apply Units.ext
  simpa only [ea, eb, Units.val_mul] using cyclicBasis_conjugator hA hB hpz

/-- For families tending to the same element, a cyclic basis of the limiting norm and
eventual equality of norm characteristic polynomials give conjugators tending to one. -/
def TwistedNearConjugatorStatement : Prop :=
  ∀ {F : Type u} [Field F] [CharZero F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
    [T1Space F] {E : Type v} [CommRing E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] [Module.Finite F E]
    {n : ℕ} {Z : Type w} {L : Filter Z} {s x : Z → GeneralLinear n E}
    {δ : GeneralLinear n E} {σ : E ≃ₐ[F] E} {l : ℕ},
    σ ^ l = 1 → l ≠ 0 → Tendsto s L (𝓝 δ) → Tendsto x L (𝓝 δ) →
    ∀ {v : Fin n → E}, IsUnit (cyclicBasisMatrix (cyclicNorm σ l δ).val v) →
    (∀ᶠ z in L, (cyclicNorm σ l (s z)).val.charpoly = (cyclicNorm σ l (x z)).val.charpoly) →
    ∃ g : Z → GeneralLinear n E, Tendsto g L (𝓝 1) ∧
      ∀ᶠ z in L, twistedConj (entrywiseAut σ n) (g z) (s z) = x z

private theorem exists_tendsto_twistedConjugator_aux [CharZero F] {Z : Type w} {L : Filter Z}
    {s x : Z → G} {δ : G} {σ : E ≃ₐ[F] E} {l : ℕ} (hσ : σ ^ l = 1) (hl : l ≠ 0)
    (hs : Tendsto s L (𝓝 δ)) (hx : Tendsto x L (𝓝 δ))
    {v : Fin n → E} (hv : IsUnit (cyclicBasisMatrix (cyclicNorm σ l δ).val v))
    (hp : ∀ᶠ z in L, (cyclicNorm σ l (s z)).val.charpoly = (cyclicNorm σ l (x z)).val.charpoly) :
    ∃ g : Z → G, Tendsto g L (𝓝 1) ∧
      ∀ᶠ z in L, twistedConj (entrywiseAut σ n) (g z) (s z) = x z := by
  let : IsModuleTopology F M := inferInstanceAs (IsModuleTopology F (Fin n → Fin n → E))
  obtain ⟨c, hc, hconj⟩ := exists_tendsto_cyclicIntertwiner hs hx hv hp
  let T (z : Z) := twistedIntertwiner σ (s z) (x z)
  let a (z : Z) : M := (l : F)⁻¹ • ∑ i ∈ Finset.range l, (T z : M → M)^[i] (c z).val
  have hmap : Continuous (σ.toRingHom.mapMatrix : M → M) :=
    continuous_id.matrix_map (IsModuleTopology.continuous_of_linearMap σ.toLinearEquiv.toLinearMap)
  have htendsto (i : ℕ) :
      Tendsto (fun z => (T z : M → M)^[i] (c z).val) L (𝓝 (1 : M)) := by
    induction i with
    | zero => exact Units.continuous_val.continuousAt.tendsto.comp hc
    | succ i ih =>
        have hs' := Units.continuous_val.continuousAt.tendsto.comp hs
        have hx' := Units.continuous_val.continuousAt.tendsto.comp hx.inv
        have hi := (hs'.mul (hmap.continuousAt.tendsto.comp ih)).mul hx'
        simpa only [T, Function.comp_apply, Function.iterate_succ_apply', twistedIntertwiner, LinearMap.coe_mk,
          AddHom.coe_mk, map_one, mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one] using hi
  have ha : Tendsto a L (𝓝 (1 : M)) := by
    have h := (tendsto_finsetSum (Finset.range l) (fun i _ => htendsto i)).const_smul ((l : F)⁻¹)
    simpa only [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul F, smul_smul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hl : (l : F) ≠ 0), one_smul] using h
  obtain ⟨g, hg, hge⟩ := finiteAlgebra_exists_tendsto_unit (F := F) (a := (1 : G)) ha
  refine ⟨g, hg, ?_⟩
  filter_upwards [hconj, hge] with z hcz hgz
  have hN : (T z : M → M)^[l] (c z).val = (c z).val := by
    rw [iterate_twistedIntertwiner, hσ]
    change (cyclicNorm σ l (s z)).val * (c z).val * (cyclicNorm σ l (x z))⁻¹.val = _
    rw [← Units.val_mul, ← Units.val_mul, hcz, mul_assoc, mul_inv_cancel, mul_one]
  have hfixed : T z (a z) = a z := by
    rw [show a z = (l : F)⁻¹ • ∑ i ∈ Finset.range l, (T z : M → M)^[i] (c z).val from rfl,
      map_smul, map_sum_iterate_eq_self hN]
  rw [← hgz] at hfixed
  change ((s z * entrywiseAut σ n (g z) * (x z)⁻¹ : G) : M) = (g z).val at hfixed
  have he := Units.ext hfixed
  change (g z)⁻¹ * s z * entrywiseAut σ n (g z) = x z
  calc
    _ = (g z)⁻¹ * (s z * entrywiseAut σ n (g z) * (x z)⁻¹) * x z := by group
    _ = x z := by rw [he, inv_mul_cancel, one_mul]

theorem exists_tendsto_twistedConjugator : TwistedNearConjugatorStatement.{u, v, w} := by
  intro F _ _ _ _ _ E _ _ _ _ _ _ n Z L s x δ σ l hσ hl hs hx v hv hp
  exact exists_tendsto_twistedConjugator_aux hσ hl hs hx hv hp

end Langlands.BaseChange
