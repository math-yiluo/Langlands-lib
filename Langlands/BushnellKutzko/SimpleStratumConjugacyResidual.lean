import Langlands.BushnellKutzko.SimpleStratumConjugacyUnits
import Langlands.BushnellKutzko.PureStratumApproximationConjugation

/-! # The residual polynomial of a normalizing unit of degree zero

Let `z` be a unit of `𝔄` lying in a subalgebra `R ⊆ A` every nonzero element of which is a
unit normalizing the chain. The image of `𝔬_F[z]` in the endomorphisms of a layer
`L_0/L_1` is a field, so the minimal polynomial of the image of `z` is irreducible. A monic
lift `P` of it to `𝔬_F[X]` satisfies `P(z) ∈ 𝔓`. If a second such unit is congruent modulo
`𝔓` to a conjugate of an element congruent to `z`, then the same polynomial `P` kills it
modulo `𝔓`.
-/

noncomputable section

open ValuativeRel IsLocalRing Polynomial

namespace Langlands.BushnellKutzko.SimpleConjugacy

open CriticalDerived

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  (𝓛 : LatticeChain 𝒪[F] F V)

local notation "P" => 𝓛.endFiltration
local notation "A" => Module.End F V
local notation "k" => ResidueField 𝒪[F]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- An integral polynomial respects congruence modulo `𝔓` in `𝔄`. -/
theorem aeval_symbolEq {x y : A} (h : SymbolEq 𝓛 0 x y) (Q : (𝒪[F])[X]) :
    SymbolEq 𝓛 0 (aeval x (Q.map (algebraMap 𝒪[F] F))) (aeval y (Q.map (algebraMap 𝒪[F] F))) := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range, natDegree_map_eq_of_injective
    (FaithfulSMul.algebraMap_injective 𝒪[F] F)]
  apply SymbolEq.sum
  intro i _
  rw [coeff_map]
  have hc : algebraMap F A (algebraMap 𝒪[F] F (Q.coeff i)) ∈ P 0 := by
    rw [← IsScalarTower.algebraMap_apply]
    exact (𝓛.mem_order_iff_mem_endFiltration).mp (𝓛.order.algebraMap_mem (Q.coeff i))
  have h' := (SymbolEq.refl hc).mul (h.pow i)
  simpa only [Algebra.smul_def, mul_zero, add_zero] using h'

/-- The layer action of a unit of `𝔄` is injective. -/
theorem residueLayerHom_injective {x : 𝓛.order} {u : Aˣ} (hu : (u : A) = x.val)
    (hs : Shifts 𝓛 0 u) (i : ℤ) : Function.Injective (residueLayerHom 𝓛 i x) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  obtain ⟨v, hv, rfl⟩ := 𝓛.intervalMk_surjective i (i + 1) q
  rw [residueLayerHom_mk, 𝓛.intervalMk_eq_zero_iff] at hq
  rw [𝓛.intervalMk_eq_zero_iff]
  apply (hs.mem_lattice_iff (i + 1) v).mp
  rw [hu, add_zero]
  exact hq

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The order element obtained from an element of `𝔓^0`. -/
abbrev orderElement {x : A} (hx : x ∈ P 0) : 𝓛.order :=
  ⟨x, 𝓛.mem_order_iff_mem_endFiltration.mpr hx⟩

/-- Let every nonzero element of the subalgebra `R` be a unit normalizing the chain. A
polynomial in an element of `R ∩ 𝔄` acts on a layer by zero or injectively. -/
theorem residueLayerHom_aeval_eq_zero_or_injective {R : Subalgebra F A}
    (hN : NormalizingUnits 𝓛 R) {z : A} (hz : z ∈ P 0) (hzR : z ∈ R) (Q : (𝒪[F])[X]) (i : ℤ) :
    aeval (residueLayerHom 𝓛 i (orderElement 𝓛 hz)) (Q.map (residue 𝒪[F])) = 0 ∨
      Function.Injective
        (aeval (residueLayerHom 𝓛 i (orderElement 𝓛 hz)) (Q.map (residue 𝒪[F]))) := by
  let z₀ := orderElement 𝓛 hz
  have heval : aeval (residueLayerHom 𝓛 i z₀) (Q.map (residue 𝒪[F])) =
      residueLayerHom 𝓛 i (aeval z₀ Q) :=
    (map_aeval_eq_aeval_map (φ := residue 𝒪[F]) (ψ := (residueLayerHom 𝓛 i).toRingHom)
      (RingHom.ext fun r => ((residueLayerHom 𝓛 i).commutes r).symm) Q z₀).symm
  have hval : ((aeval z₀ Q : 𝓛.order) : A) = aeval z (Q.map (algebraMap 𝒪[F] F)) := by
    rw [aeval_subalgebra_coe, aeval_map_algebraMap]
  have hR : ((aeval z₀ Q : 𝓛.order) : A) ∈ R := by
    rw [hval, ← aeval_subalgebra_coe (Q.map (algebraMap 𝒪[F] F)) R ⟨z, hzR⟩]
    exact (aeval (⟨z, hzR⟩ : R) (Q.map (algebraMap 𝒪[F] F))).2
  rw [heval]
  rcases mem_one_or_shifts_zero 𝓛 hN hR (aeval z₀ Q).2 with h | ⟨u, hu, hs⟩
  · exact Or.inl (residueLayerHom_eq_zero 𝓛 i h)
  · exact Or.inr (residueLayerHom_injective 𝓛 hu hs i)

/-- The layer action of a polynomial in `z`, computed in `𝔄`. -/
theorem residueLayerHom_aeval {z : A} (hz : z ∈ P 0) (Q : (𝒪[F])[X]) (i : ℤ) :
    aeval (residueLayerHom 𝓛 i (orderElement 𝓛 hz)) (Q.map (residue 𝒪[F])) =
      residueLayerHom 𝓛 i (orderElement 𝓛 (NonsplitRefinement.aeval_map_mem_order 𝓛 hz Q)) := by
  have h := (map_aeval_eq_aeval_map (φ := residue 𝒪[F]) (ψ := (residueLayerHom 𝓛 i).toRingHom)
      (RingHom.ext fun r => ((residueLayerHom 𝓛 i).commutes r).symm) Q (orderElement 𝓛 hz)).symm
  have he : orderElement 𝓛 (NonsplitRefinement.aeval_map_mem_order 𝓛 hz Q) =
      aeval (orderElement 𝓛 hz) Q := by
    apply Subtype.ext
    show aeval z (Q.map (algebraMap 𝒪[F] F)) = ((aeval (orderElement 𝓛 hz) Q : 𝓛.order) : A)
    rw [aeval_subalgebra_coe, aeval_map_algebraMap]
  rw [he]
  exact h

/-- **Residual polynomial of a normalizing unit.** Let `z` be a unit of `𝔄` in a subalgebra
`R` every nonzero element of which is a unit normalizing the chain. There is a monic
`Q ∈ 𝔬_F[X]` with unit constant term and irreducible reduction such that `Q(z) ∈ 𝔓`. -/
theorem exists_residual_polynomial_of_normalizing {R : Subalgebra F A}
    (hN : NormalizingUnits 𝓛 R) {z : Aˣ} (hz : Shifts 𝓛 0 z) (hzR : (z : A) ∈ R) :
    ∃ Q : (𝒪[F])[X], Q.Monic ∧ IsUnit (Q.coeff 0) ∧ Irreducible (Q.map (residue 𝒪[F])) ∧
      aeval (z : A) (Q.map (algebraMap 𝒪[F] F)) ∈ P 1 := by
  classical
  let z₀ := orderElement 𝓛 hz.1
  let y := residueLayerHom 𝓛 0 z₀
  have : Nontrivial (𝓛.Layer 0) := 𝓛.layer_nontrivial 0
  have hyinj : Function.Injective y := residueLayerHom_injective 𝓛 rfl hz 0
  let S := Algebra.adjoin k ({y} : Set (Module.End k (𝓛.Layer 0)))
  have hmemS : ∀ s ∈ S, s = 0 ∨ Function.Injective s := by
    intro s hs
    change s ∈ Algebra.adjoin k {y} at hs
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hs
    obtain ⟨q, rfl⟩ := hs
    obtain ⟨Q, rfl⟩ := Polynomial.map_surjective (residue 𝒪[F]) residue_surjective q
    exact residueLayerHom_aeval_eq_zero_or_injective 𝓛 hN hz.1 hzR Q 0
  obtain ⟨q₀, hq₀⟩ := exists_ne (0 : 𝓛.Layer 0)
  have hinj_ne {s : Module.End k (𝓛.Layer 0)} (hs : Function.Injective s) : s ≠ 0 := by
    intro h0
    apply hq₀
    apply hs
    rw [h0, map_zero, LinearMap.zero_apply]
  have : NoZeroDivisors S := ⟨fun {a b} hab => by
    by_contra h
    push Not at h
    rcases hmemS a a.2 with ha | ha
    · exact h.1 (Subtype.ext ha)
    rcases hmemS b b.2 with hb | hb
    · exact h.2 (Subtype.ext hb)
    have hab' : (a : Module.End k (𝓛.Layer 0)) * (b : Module.End k (𝓛.Layer 0)) = 0 :=
      congrArg Subtype.val hab
    have hcomp : Function.Injective
        ((a : Module.End k (𝓛.Layer 0)) * (b : Module.End k (𝓛.Layer 0))) :=
      fun p q hpq => hb (ha hpq)
    exact hinj_ne hcomp hab'⟩
  have : Nontrivial S := ⟨⟨0, 1, fun h => hinj_ne
    (show Function.Injective (1 : Module.End k (𝓛.Layer 0)) from fun _ _ h => h)
    (congrArg Subtype.val h).symm⟩⟩
  have : IsDomain S := NoZeroDivisors.to_isDomain S
  have : Module.Finite 𝒪[F] (𝓛.lattice 0) := Module.Finite.of_fg (𝓛.fg_lattice 0)
  have : Module.Finite k (𝓛.Layer 0) := Module.Finite.of_restrictScalars_finite 𝒪[F] k _
  let y' : S := ⟨y, Algebra.self_mem_adjoin_singleton k y⟩
  have hyint : IsIntegral k y' :=
    (isIntegral_algHom_iff S.val Subtype.val_injective).mp (IsIntegral.of_finite k y)
  let p := minpoly k y'
  have hp : p.Monic := minpoly.monic hyint
  obtain ⟨Q, hQ, -, hQm⟩ := lifts_and_natDegree_eq_and_monic
    ((lifts_iff_coeff_lifts p).mpr fun i => residue_surjective (p.coeff i)) hp
  have hy0 : y' ≠ 0 := fun h => hinj_ne hyinj (congrArg Subtype.val h)
  refine ⟨Q, hQm, ?_, hQ ▸ minpoly.irreducible hyint, ?_⟩
  · apply (residue_ne_zero_iff_isUnit _).mp
    rw [← coeff_map, hQ]
    exact minpoly.coeff_zero_ne_zero hyint hy0
  · have hw0 := NonsplitRefinement.aeval_map_mem_order 𝓛 hz.1 Q
    have hlayer : residueLayerHom 𝓛 0 (orderElement 𝓛 hw0) = 0 := by
      rw [← residueLayerHom_aeval, hQ]
      have h := congrArg S.val (minpoly.aeval k y')
      rwa [← aeval_algHom_apply, map_zero] at h
    have hwR : aeval (z : A) (Q.map (algebraMap 𝒪[F] F)) ∈ R := by
      rw [← aeval_subalgebra_coe (Q.map (algebraMap 𝒪[F] F)) R ⟨z, hzR⟩]
      exact (aeval (⟨z, hzR⟩ : R) (Q.map (algebraMap 𝒪[F] F))).2
    rcases mem_one_or_shifts_zero 𝓛 hN hwR hw0 with h | ⟨u, hu, hs⟩
    · exact h
    · exact absurd hlayer (hinj_ne (residueLayerHom_injective 𝓛 hu hs 0))

/-- **Transfer of the residual polynomial along an intertwining.** Let `z₂` lie in `𝔄` and in
a subalgebra `R` every nonzero element of which is a unit normalizing the chain. Suppose
`Z ≡ z₂` and `g⁻¹ Z g ≡ z₁` modulo `𝔓`, and `Q(z₁) ∈ 𝔓`. Then `Q(z₂) ∈ 𝔓`. -/
theorem aeval_mem_one_of_conj {R : Subalgebra F A} (hN : NormalizingUnits 𝓛 R)
    (Q : (𝒪[F])[X]) {z₁ z₂ Z : A} {g : Aˣ} (hz₂R : z₂ ∈ R) (hz₂ : z₂ ∈ P 0)
    (hZ : SymbolEq 𝓛 0 Z z₂) (hgZ : SymbolEq 𝓛 0 (((g⁻¹ : Aˣ) : A) * Z * g) z₁)
    (h₁ : aeval z₁ (Q.map (algebraMap 𝒪[F] F)) ∈ P 1) :
    aeval z₂ (Q.map (algebraMap 𝒪[F] F)) ∈ P 1 := by
  have hwR : aeval z₂ (Q.map (algebraMap 𝒪[F] F)) ∈ R := by
    rw [← aeval_subalgebra_coe (Q.map (algebraMap 𝒪[F] F)) R ⟨z₂, hz₂R⟩]
    exact (aeval (⟨z₂, hz₂R⟩ : R) (Q.map (algebraMap 𝒪[F] F))).2
  rcases mem_one_or_shifts_zero 𝓛 hN hwR (NonsplitRefinement.aeval_map_mem_order 𝓛 hz₂ Q) with
    h | ⟨W₀, hW₀, hW₀s⟩
  · exact h
  exfalso
  have hsym : SymbolEq 𝓛 0 (aeval Z (Q.map (algebraMap 𝒪[F] F))) W₀ := by
    rw [hW₀]
    exact aeval_symbolEq 𝓛 hZ Q
  obtain ⟨W, hW, hWs⟩ := exists_unit_of_symbolEq_self 𝓛 hW₀s hsym
  apply conj_not_mem_one 𝓛 hWs g
  have hconj : ((g⁻¹ : Aˣ) : A) * W * g =
      aeval (((g⁻¹ : Aˣ) : A) * Z * g) (Q.map (algebraMap 𝒪[F] F)) := by
    rw [hW]
    have h := aeval_algHom_apply (PureApproximation.conjAlgHom g) Z (Q.map (algebraMap 𝒪[F] F))
    simpa only [PureApproximation.conjAlgHom_apply] using h.symm
  rw [hconj]
  have h2 := (aeval_symbolEq 𝓛 hgZ Q).2.2
  have h3 := add_mem h2 h₁
  simpa only [zero_add, sub_add_cancel] using h3

end Langlands.BushnellKutzko.SimpleConjugacy
