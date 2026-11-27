import Langlands.GaloisCohomology.Local.Arithmetic.Ramification
import Langlands.LocalFactor.Ramification.InertiaPresentation
import Mathlib.FieldTheory.Galois.Profinite

/-!
# Frobenius acts on tame inertia by the `q`-th power

For a finite Galois extension `L/K` of nonarchimedean local fields, an automorphism acting on
the residue field of `L` by `x ↦ x ^ q` conjugates the tame character `G₀ → 𝓀[L]ˣ` into its
`q`-th power (`inertiaToResidueUnits_conj`; the computation of Serre, *Local Fields*, IV §2,
proof of Proposition 9, at index zero). For a separable closure `Ω` of a nonarchimedean local
field `K`, `exists_tameFrobenius` combines a Frobenius lift with this character at every
finite Galois level: absolute inertia is abelian and Frobenius acts on it by the `q`-th power
modulo elements of `p`-power order at each finite level (Serre, IV §2, Proposition 7 and
Corollaries 1 and 3; Tate, *Number theoretic background*, (4.2)).
-/

noncomputable section

namespace Langlands.GaloisCohomology.Local

open ValuativeRel IsLocalRing

section FiniteLevel

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

/-- Residues of images under an automorphism depend only on residues. -/
theorem residue_integerAlgEquiv_congr (σ : L ≃ₐ[K] L) {x y : 𝒪[L]}
    (h : residue 𝒪[L] x = residue 𝒪[L] y) :
    residue 𝒪[L] (integerAlgEquiv K L σ x) = residue 𝒪[L] (integerAlgEquiv K L σ y) := by
  rw [← residueAlgEquiv_residue, ← residueAlgEquiv_residue, h]

/-- If `σ` acts on the residue field of `L` by `x ↦ x ^ q`, then conjugation by `σ` acts on
the tame character `G₀ → 𝓀[L]ˣ` by the `q`-th power. -/
theorem inertiaToResidueUnits_conj {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ) {q : ℕ} {σ : L ≃ₐ[K] L}
    (hσ : ∀ z : 𝒪[L], integerAlgEquiv K L σ z - z ^ q ∈ 𝓂[L])
    (s : lowerRamificationGroup K L 0) :
    inertiaToResidueUnits hϖ ⟨σ * s.1 * σ⁻¹,
      (lowerRamificationGroup_normal K L 0).conj_mem _ s.2 σ⟩ =
      inertiaToResidueUnits hϖ s ^ q := by
  set A := integerAlgEquiv K L
  set u := uniformizerRatio (K := K) hϖ
  have hmul : ∀ τ τ' : L ≃ₐ[K] L, (u (τ * τ') : 𝒪[L]) = u τ * A τ (u τ') := by
    intro τ τ'
    have h := congrArg Units.val (uniformizerRatio_mul hϖ τ τ')
    simpa [Units.val_mul, Units.coe_map] using h
  have h1 : (u (σ * s.1 * σ⁻¹) : 𝒪[L]) = u σ * A σ (u s.1) * A σ (A s.1 (u σ⁻¹)) := by
    rw [hmul, hmul, map_mul, AlgEquiv.mul_apply]
  have h2 : (u σ : 𝒪[L]) * A σ (u σ⁻¹) = 1 := by
    have hu1 : u 1 = 1 := uniformizerRatio_one hϖ
    rw [← hmul, mul_inv_cancel, hu1, Units.val_one]
  have h3 : residue 𝒪[L] (A σ (A s.1 (u σ⁻¹))) = residue 𝒪[L] (A σ (u σ⁻¹)) :=
    residue_integerAlgEquiv_congr σ (residue_integerAlgEquiv_of_mem_zero K L s.2 _)
  have h4 : residue 𝒪[L] (A σ (u s.1)) = residue 𝒪[L] (u s.1) ^ q := by
    rw [← map_pow, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact hσ _
  apply Units.ext
  change residue 𝒪[L] (u (σ * s.1 * σ⁻¹) : 𝒪[L]) = (residue 𝒪[L] (u s.1 : 𝒪[L])) ^ q
  rw [h1, map_mul, map_mul, h3, h4, mul_right_comm, ← map_mul, h2, map_one, one_mul]

end FiniteLevel

end Langlands.GaloisCohomology.Local

namespace Langlands.LocalGalois.SepClosed

open ValuativeRel IsLocalRing Topology

section Krull

variable (K : Type*) (Ω : Type*) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

/-- Every neighbourhood of `1` in the Krull topology contains a normal subgroup of finite
index, namely the fixing subgroup of a finite Galois subextension. -/
theorem exists_normal_finiteIndex_subset (U : Set (Ω ≃ₐ[K] Ω)) (hU : U ∈ 𝓝 (1 : Ω ≃ₐ[K] Ω)) :
    ∃ N : Subgroup (Ω ≃ₐ[K] Ω), N.Normal ∧ N.FiniteIndex ∧ (N : Set (Ω ≃ₐ[K] Ω)) ⊆ U := by
  obtain ⟨M, hM⟩ := (InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois U).mp hU
  have hker := IntermediateField.restrictNormalHom_ker M.toIntermediateField
  refine ⟨M.fixingSubgroup, ?_, ?_, hM⟩
  · rw [← hker]
    exact MonoidHom.normal_ker _
  · rw [← hker]
    infer_instance

end Krull

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (Ω : Type*) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

local instance : NontriviallyNormedField K := localNormedField K
local instance : IsUltrametricDist K := localNormedField_ultrametric K
local instance : CompleteSpace K := localNormedField_complete K

/-- A Frobenius lift: an automorphism of the separable closure acting on the residue field of
its integers by `x ↦ x ^ q`, where `q` is the cardinality of the residue field of `K`. -/
theorem exists_frobenius_lift :
    ∃ φ : Ω ≃ₐ[K] Ω, ∀ y : closureIntegers K Ω,
      residue (closureIntegers K Ω) (integerAut K Ω φ y) =
        residue (closureIntegers K Ω) y ^ Nat.card 𝓀[K] := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  let _ : Fintype 𝓀[K] := Fintype.ofFinite _
  obtain ⟨φ, hφ⟩ := absoluteResidueHom_surjective K Ω
    (FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[K] (AlgebraicClosure 𝓀[K]))
  refine ⟨φ, fun y => ?_⟩
  apply (residueClosureEquiv K Ω).injective
  let F : AlgebraicClosure 𝓀[K] ≃ₐ[𝓀[K]] AlgebraicClosure 𝓀[K] := absoluteResidueHom K Ω φ
  have hF : F = FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[K] (AlgebraicClosure 𝓀[K]) := hφ
  have h1 : residueClosureEquiv K Ω (residue _ (integerAut K Ω φ y)) =
      F (residueClosureEquiv K Ω (residue _ y)) := by
    change _ = residueClosureEquiv K Ω (residueHom K Ω φ ((residueClosureEquiv K Ω).symm
      (residueClosureEquiv K Ω (residue _ y))))
    rw [RingEquiv.symm_apply_apply]
    rfl
  rw [h1, hF, map_pow, FiniteField.frobeniusAlgEquivOfAlgebraic_apply, Fintype.card_eq_nat_card]

/-- **Frobenius acts on tame inertia by the `q`-th power.** There is `φ` in the Galois group
of the separable closure such that, for every neighbourhood `U` of `1`, some set `P` contains
all commutators of absolute inertia and all elements `φ x φ⁻¹ x⁻ᑫ` with `x` in absolute
inertia, while every element of `P` has a `p`-power power in `U`. Here `p` is the residue
characteristic and `q` the residue cardinality of `K`. -/
theorem exists_tameFrobenius :
    ∃ φ : Ω ≃ₐ[K] Ω, ∀ U ∈ 𝓝 (1 : Ω ≃ₐ[K] Ω), ∃ P : Set (Ω ≃ₐ[K] Ω),
      (∀ x ∈ P, ∃ a : ℕ, x ^ ringChar 𝓀[K] ^ a ∈ U) ∧
      (∀ x ∈ absoluteInertia K Ω, ∀ y ∈ absoluteInertia K Ω, x * y * x⁻¹ * y⁻¹ ∈ P) ∧
      (∀ x ∈ absoluteInertia K Ω, φ * x * φ⁻¹ * (x ^ Nat.card 𝓀[K])⁻¹ ∈ P) := by
  obtain ⟨φ, hφ⟩ := exists_frobenius_lift K Ω
  refine ⟨φ, fun U hU => ?_⟩
  obtain ⟨M, hM⟩ := (InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois U).mp hU
  let T := Ramification.Local.SepClosed.finiteTopologicalData K Ω M
  let _ : TopologicalSpace M := T.topology
  let _ : ValuativeRel M := T.valuativeRel
  have _ : IsNonarchimedeanLocalField M := T.localField
  have _ : ValuativeExtension K M := T.valuativeExtension
  let f : 𝒪[M] →+* closureIntegers K Ω :=
    Ramification.Local.SepClosed.finiteClosureIntegerMap K Ω M
  let r : (Ω ≃ₐ[K] Ω) →* (M ≃ₐ[K] M) := AlgEquiv.restrictNormalHom M
  have hfr : ∀ (g : Ω ≃ₐ[K] Ω) (z : 𝒪[M]),
      f (GaloisCohomology.Local.integerAlgEquiv K M (r g) z) = integerAut K Ω g (f z) := by
    intro g z
    apply Subtype.ext
    exact AlgEquiv.restrictNormal_commutes g M (z : M)
  have hrefl : ∀ z : 𝒪[M], f z ∈ maximalIdeal (closureIntegers K Ω) → z ∈ 𝓂[M] := by
    intro z hz
    rw [mem_maximalIdeal, mem_nonunits_iff] at hz ⊢
    exact fun hu => hz (hu.map f)
  have hmem0 : ∀ x ∈ absoluteInertia K Ω,
      r x ∈ GaloisCohomology.Local.lowerRamificationGroup K M 0 := by
    intro x hx
    rw [GaloisCohomology.Local.mem_lowerRamificationGroup_iff]
    intro z
    rw [zero_add, pow_one]
    apply hrefl
    rw [map_sub, hfr, ← residue_eq_zero_iff, map_sub, sub_eq_zero]
    exact DFunLike.congr_fun (MonoidHom.mem_ker.mp hx) (residue _ (f z))
  have hfrobM : ∀ z : 𝒪[M],
      GaloisCohomology.Local.integerAlgEquiv K M (r φ) z - z ^ Nat.card 𝓀[K] ∈ 𝓂[M] := by
    intro z
    apply hrefl
    rw [map_sub, map_pow, hfr, ← residue_eq_zero_iff, map_sub, map_pow, sub_eq_zero]
    exact hφ (f z)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[M]
  let θ := GaloisCohomology.Local.inertiaToResidueUnits (K := K) hϖ
  let res0 : absoluteInertia K Ω →* GaloisCohomology.Local.lowerRamificationGroup K M 0 :=
    (r.comp (absoluteInertia K Ω).subtype).codRestrict _ fun x => hmem0 x.1 x.2
  let Θ := θ.comp res0
  refine ⟨{x | ∃ hx : x ∈ absoluteInertia K Ω, Θ ⟨x, hx⟩ = 1}, ?_, ?_, ?_⟩
  · rintro x ⟨hx, hΘ⟩
    have hker : res0 ⟨x, hx⟩ ∈ θ.ker := hΘ
    rw [GaloisCohomology.Local.ker_inertiaToResidueUnits, Subgroup.mem_subgroupOf] at hker
    obtain ⟨a, ha⟩ :=
      GaloisCohomology.Local.isPGroup_lowerRamificationGroup_one K M ⟨r x, hker⟩
    have hk : x ^ ringChar 𝓀[K] ^ a ∈ (AlgEquiv.restrictNormalHom M.toIntermediateField).ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact congrArg Subtype.val ha
    rw [IntermediateField.restrictNormalHom_ker] at hk
    exact ⟨a, hM hk⟩
  · intro x hx y hy
    let a : absoluteInertia K Ω := ⟨x, hx⟩
    let b : absoluteInertia K Ω := ⟨y, hy⟩
    refine ⟨(a * b * a⁻¹ * b⁻¹).2, ?_⟩
    change Θ (a * b * a⁻¹ * b⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_right_comm (Θ a), mul_inv_cancel,
      one_mul, mul_inv_cancel]
  · intro x hx
    have hc : φ * x * φ⁻¹ ∈ absoluteInertia K Ω :=
      (absoluteInertia_normal K Ω).conj_mem x hx φ
    let a : absoluteInertia K Ω := ⟨x, hx⟩
    let c : absoluteInertia K Ω := ⟨φ * x * φ⁻¹, hc⟩
    refine ⟨(c * (a ^ Nat.card 𝓀[K])⁻¹).2, ?_⟩
    change Θ (c * (a ^ Nat.card 𝓀[K])⁻¹) = 1
    have hres : res0 c = ⟨r φ * (res0 a).1 * (r φ)⁻¹,
        (GaloisCohomology.Local.lowerRamificationGroup_normal K M 0).conj_mem _
          (res0 a).2 (r φ)⟩ := by
      apply Subtype.ext
      change r (φ * x * φ⁻¹) = r φ * r x * (r φ)⁻¹
      rw [map_mul, map_mul, map_inv]
    have hΘc : Θ c = Θ a ^ Nat.card 𝓀[K] := by
      change θ (res0 c) = θ (res0 a) ^ Nat.card 𝓀[K]
      rw [hres]
      exact GaloisCohomology.Local.inertiaToResidueUnits_conj hϖ hfrobM (res0 a)
    rw [map_mul, map_inv, map_pow, hΘc, mul_inv_cancel]

end Langlands.LocalGalois.SepClosed
