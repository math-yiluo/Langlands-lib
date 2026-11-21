import Langlands.BushnellKutzko.CompactLevelBound
import Langlands.BushnellKutzko.RefinementProof
import Langlands.BushnellKutzko.LatticeChainLayerCommutation
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-! # Normalized shift and integrality for candidate approximations -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.PureApproximation

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  (A : LatticeChain 𝒪[F] F V) {π : 𝒪[F]} (hπ : Irreducible π)

/-- A depth-zero endomorphism is integral over the base integer ring. -/
theorem isIntegral_of_mem_endFiltration_zero {x : Module.End F V} (hx : x ∈ A.endFiltration 0) :
    IsIntegral 𝒪[F] x :=
  IsIntegral.of_mem_of_fg A.order (A.toSubmodule_order.symm ▸ A.endFiltration_zero_fg) x hx

include hπ in
/-- Multiplication by an integral or negative uniformizer power translates endomorphism depths. -/
theorem zpow_smul_mem_endFiltration_iff (t j : ℤ) (x : Module.End F V) :
    ((π : F) ^ t) • x ∈ A.endFiltration (j + A.period * t) ↔ x ∈ A.endFiltration j := by
  simp only [LatticeChain.mem_endFiltration, LinearMap.smul_apply, A.zpow_smul_mem_iff hπ t,
    ← add_assoc, add_sub_cancel_right]

/-- An order endomorphism has integral determinant, computed in a basis extending a lattice basis. -/
theorem det_mem_integer_of_endFiltration_zero {x : Module.End F V}
    (hx : x ∈ A.endFiltration 0) : LinearMap.det x ∈ 𝒪[F] := by
  classical
  let b := Module.finBasis 𝒪[F] (A.lattice 0)
  let bF := b.extendOfIsLattice F
  have hbF : ∀ k, bF k ∈ A.lattice 0 := fun k => by
    simp only [bF, Module.Basis.extendOfIsLattice_apply]
    exact (b k).2
  have hent : ∀ k l, LinearMap.toMatrix bF bF x k l ∈ 𝒪[F] := by
    intro k l
    rw [LinearMap.toMatrix_apply]
    exact A.repr_extendOfIsLattice_mem b (by simpa using hx 0 _ (hbF l)) k
  let M : Matrix (Fin (Module.finrank 𝒪[F] (A.lattice 0)))
      (Fin (Module.finrank 𝒪[F] (A.lattice 0))) 𝒪[F] := fun k l => ⟨_, hent k l⟩
  have hM : (𝒪[F].subtype).mapMatrix M = LinearMap.toMatrix bF bF x := by
    ext k l
    rfl
  rw [← LinearMap.det_toMatrix bF, ← hM, ← RingHom.map_det]
  exact (M.det).2

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A natural power multiplies a filtration bound by its exponent. -/
theorem pow_mem_endFiltration_intMul {x : Module.End F V} {j : ℤ} (hx : x ∈ A.endFiltration j)
    (k : ℕ) : x ^ k ∈ A.endFiltration (k * j) := by
  induction k with
  | zero => simpa using (A.mem_order_iff_mem_endFiltration.mp (one_mem A.order))
  | succ k ih =>
    rw [pow_succ, Nat.cast_succ, add_mul, one_mul]
    exact A.mul_mem_endFiltration ih hx

include hπ in
/-- The determinant bound on the actual finite-dimensional vector space. -/
theorem finrank_mul_le_period_mul_ordOf_det {j : ℤ} {x : Module.End F V}
    (hx : x ∈ A.endFiltration j) (hdet : LinearMap.det x ≠ 0) :
    (Module.finrank F V : ℤ) * j ≤ A.period * ordOf hπ (LinearMap.det x) := by
  have hπ0 : (π : F) ^ (-j) ≠ 0 := zpow_ne_zero _ (coe_uniformizer_ne_zero hπ)
  have hp := pow_mem_endFiltration_intMul A hx A.period
  have h0 := (zpow_smul_mem_endFiltration_iff A hπ (-j) ((A.period : ℤ) * j) _).mpr hp
  rw [show (A.period : ℤ) * j + A.period * -j = 0 by ring] at h0
  have ht := det_mem_integer_of_endFiltration_zero A h0
  rw [LinearMap.det_smul, map_pow] at ht
  have h := ordOf_nonneg hπ (mul_ne_zero (pow_ne_zero _ hπ0) (pow_ne_zero _ hdet)) ht
  rw [ordOf_mul hπ (pow_ne_zero _ hπ0) (pow_ne_zero _ hdet), ordOf_pow hπ hπ0,
    ordOf_pow hπ hdet, ordOf_zpow] at h
  linarith

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem stabilizer_mem_endFiltration (g : A.stabilizer) :
    ((g.val : (Module.End F V)ˣ) : Module.End F V) ∈
      A.endFiltration (A.stabilizerValuation g) := by
  intro i v hv
  have h := Submodule.mem_map_of_mem
    (f := ((g.val : Module.End F V)).restrictScalars 𝒪[F]) hv
  rwa [A.map_lattice_stabilizer g i] at h

include hπ in
/-- The determinant of a unit shifting a chain computes the normalized shift. -/
theorem finrank_mul_stabilizerValuation (g : A.stabilizer) :
    (Module.finrank F V : ℤ) * A.stabilizerValuation g =
      A.period * ordOf hπ (LinearMap.det (g.val : Module.End F V)) := by
  let u : Fˣ := Units.map LinearMap.det g.val
  have hdet : LinearMap.det (g.val : Module.End F V) ≠ 0 := u.ne_zero
  have hdi : LinearMap.det ((g⁻¹).val : Module.End F V) =
      (LinearMap.det (g.val : Module.End F V))⁻¹ := by
    change ((Units.map LinearMap.det g.val⁻¹ : Fˣ) : F) = _
    rw [map_inv, Units.val_inv_eq_inv_val]
    rfl
  have hlo := finrank_mul_le_period_mul_ordOf_det A hπ (stabilizer_mem_endFiltration A g) hdet
  have hhi := finrank_mul_le_period_mul_ordOf_det A hπ (stabilizer_mem_endFiltration A g⁻¹)
    (by rw [hdi]; exact inv_ne_zero hdet)
  rw [A.stabilizerValuation_inv, hdi, ordOf_inv hπ hdet] at hhi
  linarith

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A perturbation at strictly greater depth than the shift still realizes that shift. -/
theorem stabilizer_of_sub_mem {g : A.stabilizer} {x : Module.End F V}
    (hx : x - (g.val : Module.End F V) ∈ A.endFiltration (A.stabilizerValuation g + 1)) :
    ∃ G : A.stabilizer, (G.val : Module.End F V) = x ∧
      A.stabilizerValuation G = A.stabilizerValuation g := by
  let f : Module.End F V := ((g⁻¹).val : Module.End F V) * x - 1
  have h₁ : f ∈ A.endFiltration (1 : ℤ) := by
    have h := A.mul_mem_endFiltration (stabilizer_mem_endFiltration A g⁻¹) hx
    rw [A.stabilizerValuation_inv, show -A.stabilizerValuation g +
      (A.stabilizerValuation g + 1) = 1 by ring, mul_sub] at h
    change ((g.val⁻¹ : (Module.End F V)ˣ) : Module.End F V) * x -
      ((g.val⁻¹ : (Module.End F V)ˣ) : Module.End F V) * (g.val : Module.End F V) ∈ _ at h
    rwa [Units.inv_mul] at h
  obtain ⟨h, hh, hval⟩ := A.exists_mem_unitFiltration (n := 1) le_rfl h₁
  let H : A.stabilizer := ⟨h, mem_stabilizer_of_mem_unitFiltration A hh⟩
  have hH : A.stabilizerValuation H = 0 := by
    symm
    apply A.stabilizerValuation_unique H 0
    change (A.lattice 0).map ((h : Module.End F V).restrictScalars 𝒪[F]) = A.lattice (0 + 0)
    rw [hval, add_zero]
    exact A.map_one_add_eq le_rfl h₁ 0
  refine ⟨g * H, ?_, by rw [A.stabilizerValuation_mul, hH, add_zero]⟩
  change (g.val : Module.End F V) * (h : Module.End F V) = x
  rw [hval, show 1 + f = ((g⁻¹).val : Module.End F V) * x by dsimp [f]; abel, ← mul_assoc]
  change (g.val : Module.End F V) * ((g.val⁻¹ : (Module.End F V)ˣ) : Module.End F V) * x = x
  rw [Units.mul_inv, one_mul]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- An element in the coset of a pure stratum shifts its chain by the negative initial level. -/
theorem exists_stabilizer_of_mem_pure_coset (S : Stratum 𝒪[F] F V) (hS : S.IsPure)
    {x : Module.End F V} (hx : x ∈ S.coset) :
    ∃ g : S.chain.stabilizer, (g.val : Module.End F V) = x ∧
      S.chain.stabilizerValuation g = -S.n := by
  obtain ⟨⟨hF, hN⟩, hval⟩ := hS
  have hS0 : S.b ≠ 0 := by
    intro h
    simp [h, LatticeChain.valuation] at hval
    exact WithTop.top_ne_coe hval
  obtain ⟨G, hGb, hGs⟩ := normalizingUnits_of_isField S.chain hF hN _
    (Algebra.self_mem_adjoin_singleton F S.b) hS0
  let g : S.chain.stabilizer := ⟨G, hGs⟩
  have hg : S.chain.stabilizerValuation g = -S.n := by
    have h := S.chain.valuation_eq_shift g
    change S.chain.valuation (G : Module.End F V) = _ at h
    rw [hGb] at h
    exact WithTop.coe_injective (h.symm.trans hval)
  have hd : x - (g.val : Module.End F V) ∈
      S.chain.endFiltration (S.chain.stabilizerValuation g + 1) := by
    change x - (G : Module.End F V) ∈ _
    rw [hGb, hg]
    have hlt := S.r_lt_n
    exact S.chain.endFiltration_antitone (show -S.n + 1 ≤ -S.r by omega) hx
  obtain ⟨g', hg', hshift⟩ := stabilizer_of_sub_mem S.chain hd
  exact ⟨g', hg', hshift.trans hg⟩

/-- For two pure strata having a common coset element, the normalized initial levels agree. -/
def PureCosetSlopeStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (V : Type uV) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (S T : Stratum 𝒪[F] F V), S.IsPure → T.IsPure →
    ∀ x ∈ S.coset, x ∈ T.coset → S.n * T.chain.period = T.n * S.chain.period

/-- Both shifts are read from the determinant of the same coset element. -/
theorem pureCosetSlope : PureCosetSlopeStatement.{uF, uV} := by
  intro F _ _ _ _ V _ _ _ S T hS hT x hx hx'
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨g, hgb, hgs⟩ := exists_stabilizer_of_mem_pure_coset S hS hx
  obtain ⟨h, hhb, hhs⟩ := exists_stabilizer_of_mem_pure_coset T hT hx'
  have h₁ := finrank_mul_stabilizerValuation S.chain hπ g
  have h₂ := finrank_mul_stabilizerValuation T.chain hπ h
  rw [hgs, hgb] at h₁
  rw [hhs, hhb] at h₂
  let : Nontrivial V := S.chain.nontrivialSpace
  have hN : (Module.finrank F V : ℤ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := F) (M := V)).ne'
  apply mul_left_cancel₀ hN
  calc
    (Module.finrank F V : ℤ) * (S.n * T.chain.period) =
        -((Module.finrank F V : ℤ) * -S.n) * T.chain.period := by ring
    _ = -((Module.finrank F V : ℤ) * -T.n) * S.chain.period := by rw [h₁, h₂]; ring
    _ = (Module.finrank F V : ℤ) * (T.n * S.chain.period) := by ring

end Langlands.BushnellKutzko.PureApproximation
