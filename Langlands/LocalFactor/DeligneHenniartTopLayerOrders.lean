import Langlands.LocalFactor.DeligneHenniartNormTrace
import Langlands.LocalFactor.Ramification.Herbrand.Finite
import Langlands.LocalField.RelativeIntegers
import Langlands.ClassFieldTheory.Local.NYLL.RelativeIntegerStructureProof
import Langlands.ClassFieldTheory.Local.PrimeRamifiedDifferentProof
import Langlands.LocalFactor.Ramification.UniformizerCriterionProof
import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# Orders in a finite extension of p-adic fields

For a finite extension `M/K` of p-adic fields with arbitrary topological data, the order of
`M` restricted to `K` is the order of `K` times `e_M / e_K`; automorphisms of `M` over `K`
preserve the order of `M`; and when `M/K` is Galois, the relative ramification index
`e_M / e_K` is the order of the inertia group `G_0`.
-/

noncomputable section

namespace Langlands.LocalFactor.NonabelianSystem.DeligneHenniart.TopLayer

open IsLocalRing

universe u w

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{u} p} {M : PadicField.{w} p}
  [Algebra K.Carrier M.Carrier] [IsScalarTower (Padic p) K.Carrier M.Carrier]
  (TK : K.TopologicalData) (TM : M.TopologicalData)

/-- `e_K ord_M(x) = e_M ord_K(x)` for `x ∈ K`, with absolute ramification indices. -/
theorem ramificationIndex_mul_ord_algebraMap (x : K.Carrier) :
    (TK.ramificationIndex : ℤ) * TM.ord (algebraMap K.Carrier M.Carrier x) =
      TM.ramificationIndex * TK.ord x := by
  by_cases hx : x = 0
  · simp [hx, PadicField.TopologicalData.ord_zero]
  have hy : algebraMap K.Carrier M.Carrier x ≠ 0 := (map_ne_zero _).mpr hx
  have hn : M.canonicalNorm (algebraMap K.Carrier M.Carrier x) = K.canonicalNorm x :=
    Weil.Local.canonicalNorm_map K M (IsScalarTower.toAlgHom (Padic p) K.Carrier M.Carrier) x
  have h1 := ord_mul_le_of_canonicalNorm_le K M TK TM hx hy 1 (by rw [pow_one, hn])
  have h2 := ord_mul_le_of_canonicalNorm_le M K TM TK hy hx 1 (by rw [pow_one, hn])
  push_cast at h1 h2
  linarith

/-- Automorphisms of `M` over `K` preserve the order of `M`. -/
theorem ord_algEquiv_apply (σ : M.Carrier ≃ₐ[K.Carrier] M.Carrier) (x : M.Carrier) :
    TM.ord (σ x) = TM.ord x := by
  by_cases hx : x = 0
  · simp [hx]
  have hy : σ x ≠ 0 := (map_ne_zero _).mpr hx
  have hn : M.canonicalNorm (σ x) = M.canonicalNorm x :=
    Weil.Local.canonicalNorm_map M M (σ.restrictScalars (Padic p)).toAlgHom x
  have h1 := ord_mul_le_of_canonicalNorm_le M M TM TM hx hy 1 (by rw [pow_one, hn])
  have h2 := ord_mul_le_of_canonicalNorm_le M M TM TM hy hx 1 (by rw [pow_one, hn])
  have he : (0 : ℤ) < TM.ramificationIndex := by exact_mod_cast TM.ramificationIndex_pos
  push_cast at h1 h2
  nlinarith

section Galois

open Ramification.Padic PadicField.TopologicalData

/-- The integer action makes `Gal(M/K)` a Galois group of `O_M` over `O_K`. -/
theorem isGaloisGroup_integers [IsGalois K.Carrier M.Carrier] :
    letI := TK.valuativeRel
    letI := TM.valuativeRel
    letI := relativeIntegerAlgebra TK TM
    letI := integerAction TM K.Carrier
    IsGaloisGroup (M.Carrier ≃ₐ[K.Carrier] M.Carrier) TK.Integers TM.Integers := by
  let := TK.valuativeRel
  let := TM.valuativeRel
  let := relativeIntegerAlgebra TK TM
  let := integerAction TM K.Carrier
  have : FiniteDimensional K.Carrier M.Carrier :=
    Module.Finite.of_restrictScalars_finite (Padic p) K.Carrier M.Carrier
  refine ⟨⟨fun {σ τ} h => ?_⟩, ⟨fun σ a b => ?_⟩, ⟨fun b hb => ?_⟩⟩
  · have : IsFractionRing TM.Integers M.Carrier :=
      inferInstanceAs (IsFractionRing
        (ValuativeRel.valuation M.Carrier).valuationSubring M.Carrier)
    have heq : σ.toRingHom = τ.toRingHom :=
      IsFractionRing.ringHom_ext (A := TM.Integers) (fun x =>
        congrArg (fun y : TM.Integers => (y : M.Carrier)) (h x))
    exact AlgEquiv.ext fun x => RingHom.congr_fun heq x
  · apply Subtype.ext
    change σ ((relativeIntegerMap TK TM a : M.Carrier) * (b : M.Carrier)) =
      (relativeIntegerMap TK TM a : M.Carrier) * σ (b : M.Carrier)
    rw [map_mul, relativeIntegerMap_coe, AlgEquiv.commutes]
  · have hfix : ∀ f : M.Carrier ≃ₐ[K.Carrier] M.Carrier, f (b : M.Carrier) = b :=
      fun f => congrArg Subtype.val (hb f)
    obtain ⟨k, hk⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (b : M.Carrier)).mpr hfix
    have hkint : k ∈ TK.Integers :=
      (relative_mem_integers_iff TK TM k).mp (by rw [hk]; exact b.property)
    exact ⟨⟨k, hkint⟩, Subtype.ext hk⟩

/-- The zeroth lower group is the inertia group of the maximal ideal of `O_M`. -/
theorem lowerRamificationGroup_zero_eq_inertia :
    letI := TM.valuativeRel
    letI := integerAction TM K.Carrier
    lowerRamificationGroup TM K.Carrier 0 =
      (maximalIdeal TM.Integers).inertia (M.Carrier ≃ₐ[K.Carrier] M.Carrier) := by
  let := TM.valuativeRel
  let := integerAction TM K.Carrier
  ext σ
  rw [mem_lowerRamificationGroup, Ideal.mem_inertia, zero_add, pow_one]
  rfl

/-- The order `ord_M(π_K)` of a uniformizer of `K` is the ramification index of the maximal
ideal of `O_M` over that of `O_K`. -/
theorem ramificationIdx_eq_ord_uniformizer :
    letI := TK.valuativeRel
    letI := TM.valuativeRel
    letI := relativeIntegerAlgebra TK TM
    ((maximalIdeal TM.Integers).ramificationIdx TK.Integers : ℤ) =
      TM.ord (algebraMap K.Carrier M.Carrier TK.uniformizer) := by
  let := TK.topology
  let := TK.valuativeRel
  let := TK.localField
  let := TM.topology
  let := TM.valuativeRel
  let := TM.localField
  let := relativeIntegerAlgebra TK TM
  have : Module.IsTorsionFree TK.Integers TM.Integers :=
    relativeIntegerAlgebra_isTorsionFree TK TM
  have : IsLocalHom (algebraMap TK.Integers TM.Integers) := relativeIntegerMap_isLocalHom TK TM
  set ϖ := TK.coordinateUniformizer TK.uniformizer TK.ord_uniformizer
  have hπ0 : TK.uniformizer ≠ 0 := TK.coordinateUniformizer_ne_zero _ TK.ord_uniformizer
  have hy0 : algebraMap K.Carrier M.Carrier TK.uniformizer ≠ 0 := (map_ne_zero _).mpr hπ0
  have hpos : 0 ≤ TM.ord (algebraMap K.Carrier M.Carrier TK.uniformizer) := by
    have hm : algebraMap K.Carrier M.Carrier TK.uniformizer ∈ TM.Integers :=
      (relative_mem_integers_iff TK TM _).mpr (by
        rw [← TK.coordinateUniformizer_coe TK.uniformizer TK.ord_uniformizer]
        exact (TK.coordinateUniformizer TK.uniformizer TK.ord_uniformizer).property)
    exact (TM.mem_integers_iff_zero_le_ord hy0).mp hm
  obtain ⟨E, hE⟩ : ∃ E : ℕ, (E : ℤ) = TM.ord (algebraMap K.Carrier M.Carrier TK.uniformizer) :=
    ⟨_, Int.toNat_of_nonneg hpos⟩
  have hmap : (maximalIdeal TK.Integers).map (algebraMap TK.Integers TM.Integers) =
      Ideal.span {algebraMap TK.Integers TM.Integers ϖ} := by
    rw [TK.maximalIdeal_eq_span_coordinateUniformizer TK.uniformizer TK.ord_uniformizer,
      Ideal.map_span, Set.image_singleton]
  have hcoe : ((algebraMap TK.Integers TM.Integers ϖ : TM.Integers) : M.Carrier) =
      algebraMap K.Carrier M.Carrier TK.uniformizer := by
    change algebraMap K.Carrier M.Carrier (ϖ : K.Carrier) = _
    rw [TK.coordinateUniformizer_coe]
  have hA : maximalIdeal TK.Integers ≠ ⊥ := by
    rw [TK.maximalIdeal_eq_span_coordinateUniformizer TK.uniformizer TK.ord_uniformizer]
    intro h
    rw [Ideal.span_singleton_eq_bot] at h
    apply hπ0
    rw [← TK.coordinateUniformizer_coe TK.uniformizer TK.ord_uniformizer]
    exact congrArg Subtype.val h
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (maximalIdeal TK.Integers)
    (maximalIdeal TM.Integers) hA, ← hE]
  congr 1
  apply Ideal.ramificationIdx'_spec
  · rw [hmap, Ideal.span_singleton_le_iff_mem,
      TM.mem_maximalIdeal_pow_iff_ord TM.uniformizer TM.ord_uniformizer, hcoe]
    exact Or.inr hE.le
  · rw [hmap, Ideal.span_singleton_le_iff_mem,
      TM.mem_maximalIdeal_pow_iff_ord TM.uniformizer TM.ord_uniformizer, hcoe]
    rintro (h | h)
    · exact hy0 h
    · push_cast at h
      omega

/-- For `M/K` Galois, `|G_0| e_K = e_M`: the inertia order is the relative ramification index. -/
theorem lowerGroupOrder_zero_mul_ramificationIndex [IsGalois K.Carrier M.Carrier] :
    lowerGroupOrder TM K.Carrier 0 * TK.ramificationIndex = TM.ramificationIndex := by
  let := TK.topology
  let := TK.valuativeRel
  let := TK.localField
  let := TM.topology
  let := TM.valuativeRel
  let := TM.localField
  let := relativeIntegerAlgebra TK TM
  let := integerAction TM K.Carrier
  have : FiniteDimensional K.Carrier M.Carrier :=
    Module.Finite.of_restrictScalars_finite (Padic p) K.Carrier M.Carrier
  have hG := isGaloisGroup_integers TK TM
  have : Module.IsTorsionFree TK.Integers TM.Integers :=
    relativeIntegerAlgebra_isTorsionFree TK TM
  have : IsLocalHom (algebraMap TK.Integers TM.Integers) := relativeIntegerMap_isLocalHom TK TM
  let := relativeIntegerFieldAlgebra (E := M) TK
  have := (LocalClassField.NYLL.relativeIntegerStructure p K M TK TM).2
  have : Algebra.IsIntegral TK.Integers TM.Integers := Algebra.IsIntegral.of_finite _ _
  have : Finite (maximalIdeal TK.Integers).ResidueField := by
    have : Finite (TK.Integers ⧸ maximalIdeal TK.Integers) := TK.finite_residueField
    exact Finite.of_surjective _
      (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal TK.Integers)).2
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := M.Carrier ≃ₐ[K.Carrier] M.Carrier)
    (maximalIdeal TK.Integers) (maximalIdeal TM.Integers)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ (maximalIdeal TM.Integers)
    (M.Carrier ≃ₐ[K.Carrier] M.Carrier)] at hcard
  have hidx := ramificationIdx_eq_ord_uniformizer TK TM
  have hord := ramificationIndex_mul_ord_algebraMap TK TM TK.uniformizer
  rw [TK.ord_uniformizer, mul_one, ← hidx, ← hcard,
    ← lowerRamificationGroup_zero_eq_inertia] at hord
  unfold lowerGroupOrder
  have h : ((Nat.card (lowerRamificationGroup TM K.Carrier 0) * TK.ramificationIndex : ℕ) : ℤ) =
      (TM.ramificationIndex : ℤ) := by
    push_cast
    linarith
  exact_mod_cast h

/-- For `M/K` Galois and `x ∈ K`, `ord_M(x) = |G_0| ord_K(x)`. -/
theorem ord_algebraMap_eq [IsGalois K.Carrier M.Carrier] (x : K.Carrier) :
    TM.ord (algebraMap K.Carrier M.Carrier x) =
      (lowerGroupOrder TM K.Carrier 0 : ℤ) * TK.ord x := by
  have h1 := ramificationIndex_mul_ord_algebraMap TK TM x
  have h2 := lowerGroupOrder_zero_mul_ramificationIndex TK TM
  have he : (0 : ℤ) < TK.ramificationIndex := by exact_mod_cast TK.ramificationIndex_pos
  rw [← h2] at h1
  push_cast at h1
  have h3 : (TK.ramificationIndex : ℤ) * (TM.ord (algebraMap K.Carrier M.Carrier x) -
      (lowerGroupOrder TM K.Carrier 0 : ℤ) * TK.ord x) = 0 := by linarith
  rcases mul_eq_zero.mp h3 with h | h
  · omega
  · linarith

end Galois

end Langlands.LocalFactor.NonabelianSystem.DeligneHenniart.TopLayer
