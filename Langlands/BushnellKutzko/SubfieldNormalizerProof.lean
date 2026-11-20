import Langlands.BushnellKutzko.SubfieldNormalizerStatement
import Langlands.BushnellKutzko.SubfieldValuationShifts

/-! # The normalizing subfield criterion -/

noncomputable section

open ValuativeRel IsDiscreteValuationRing

namespace Langlands.BushnellKutzko

universe u v w

private theorem span_maximalIdeal_smul_eq_map
    {F : Type u} [Field F] [ValuativeRel F]
    {V : Type v} [AddCommGroup V] [Module F V]
    {E : Type w} [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]
    [IsDiscreteValuationRing (subfieldIntegers F E)]
    (L : Submodule 𝒪[F] V)
    (hL : ∀ (a : subfieldIntegers F E) (v : V), v ∈ L → (a : E) • v ∈ L)
    {π : subfieldIntegers F E} (hπ : Irreducible π) :
    Submodule.span 𝒪[F]
        (Set.image2 (fun (a : subfieldIntegers F E) (v : V) => (a : E) • v)
          (subfieldMaximalIdeal F E : Set (subfieldIntegers F E)) (L : Set V)) =
      L.map ((subfieldEmbedding F E V (π : E)).restrictScalars 𝒪[F]) := by
  rw [subfieldMaximalIdeal_eq F E, hπ.maximalIdeal_eq]
  refine le_antisymm (Submodule.span_le.mpr ?_) ?_
  · rintro _ ⟨a, ha, x, hx, rfl⟩
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp ha
    refine ⟨(b : E) • x, hL b x hx, ?_⟩
    change (π : E) • ((b : E) • x) = (a : E) • x
    rw [hb, Subalgebra.coe_mul, mul_smul]
  · rintro _ ⟨x, hx, rfl⟩
    exact Submodule.subset_span ⟨π, Ideal.mem_span_singleton_self π, x, hx, rfl⟩

/-- The normalizing subfield criterion of Bushnell–Kutzko (1.2.1). -/
theorem subfieldNormalizer : SubfieldNormalizerStatement.{u, v, w} := by
  intro F _ _ _ _ V _ _ E _ _ _ _ 𝓛
  let := 𝓛.finiteDimensional_subfield E
  let := subfieldIntegers_isDiscreteValuationRing F E
  let := subfieldIntegers_isFractionRing F E
  obtain ⟨π, hπ⟩ := exists_irreducible (subfieldIntegers F E)
  let p := subfieldIntegerUnit E hπ.ne_zero
  constructor
  · intro hE
    refine ⟨fun i a ha x hx => 𝓛.subfieldInteger_smul_mem E hE i ⟨a, ha⟩ hx, ?_⟩
    obtain ⟨d, hd⟩ := 𝓛.exists_shift (hE p)
    refine ⟨d, fun i => ?_⟩
    exact (span_maximalIdeal_smul_eq_map (𝓛.lattice i)
      (fun a _ hx => 𝓛.subfieldInteger_smul_mem E hE i a hx) hπ).trans (hd i)
  · rintro ⟨hL, d, hd⟩ a
    have hmem (i : ℤ) (b : subfieldIntegers F E) (x : V) (hx : x ∈ 𝓛.lattice i) :
        (b : E) • x ∈ 𝓛.lattice i := hL i b b.property x hx
    have hp : subfieldUnits F E V p ∈ 𝓛.stabilizer := by
      intro i
      exact ⟨i + d, (span_maximalIdeal_smul_eq_map (𝓛.lattice i) (hmem i) hπ).symm.trans
        (hd i)⟩
    obtain ⟨n, u, rfl⟩ := subfieldUnit_factorization E hπ a
    rw [map_mul, map_zpow]
    refine 𝓛.stabilizer.mul_mem ?_ (𝓛.stabilizer.zpow_mem hp n)
    intro i
    refine ⟨i, le_antisymm ?_ ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hmem i u.val x hx
    · intro x hx
      let b := subfieldIntegerUnits E u
      refine ⟨((b⁻¹ : Eˣ) : E) • x, hmem i (u⁻¹ : (subfieldIntegers F E)ˣ).val x hx, ?_⟩
      change (b : E) • (((b⁻¹ : Eˣ) : E) • x) = x
      rw [smul_smul, Units.mul_inv, one_smul]

end Langlands.BushnellKutzko
