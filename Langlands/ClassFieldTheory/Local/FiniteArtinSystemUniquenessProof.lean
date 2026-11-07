import Langlands.ClassFieldTheory.Local.FiniteArtinSystemUniquenessStatement
import Langlands.ClassFieldTheory.Local.ProfiniteReciprocityReconstruction
import Langlands.ClassFieldTheory.Local.WeilReciprocityUniquenessProof
import Langlands.ClassFieldTheory.Local.UnramifiedArithmeticProof
import Langlands.ClassFieldTheory.Local.NYLL.SuppliedResidueProof

noncomputable section

namespace Langlands.LocalClassField

open IsLocalRing
open Langlands.ClassFieldTheory.Local

universe u v

namespace FiniteArtinSystemUniqueness

variable {p : ℕ} [Fact p.Prime]

/-- The residue cardinality is independent of the supplied topological datum. -/
theorem residueCardinality_eq_canonical (F : PadicField.{u} p)
    (T : F.TopologicalData) :
    T.residueCardinality = F.canonicalTopologicalData.residueCardinality := by
  have h : T.Integers = F.canonicalTopologicalData.Integers := by
    ext x
    rw [← T.canonicalNorm_le_one_iff_mem_integers,
      ← F.canonicalTopologicalData.canonicalNorm_le_one_iff_mem_integers]
  exact Nat.card_congr (ResidueField.mapEquiv (RingEquiv.subringCongr h)).toEquiv

/-- Membership in the supplied integer ring bounds its discrete valuation. -/
theorem discreteValuation_le_one (F : PadicField.{u} p)
    (T : F.TopologicalData) (x : T.Integers) :
    T.discreteValuation (x : F.Carrier) ≤ 1 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier
  change e (ValuativeRel.valuation F.Carrier (x : F.Carrier)) ≤ 1
  rw [← map_one e]
  exact e.strictMono.monotone x.property

section Residue

variable (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier E.Carrier]

local instance : NontriviallyNormedField F.Carrier := F.canonicalNormedField
local instance : NormedAlgebra (Padic p) F.Carrier := F.canonicalNormedAlgebra
local instance : IsUltrametricDist F.Carrier :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (isNonarchimedean_spectralNorm (K := Padic p) (L := F.Carrier))
local instance : ProperSpace F.Carrier := FiniteDimensional.proper (Padic p) F.Carrier

/-- A canonical discrete-valuation congruence gives the actual relative
spectral residue action, with the same exponent. -/
theorem residueHom_inverse_power (σ : Gal(E.Carrier/F.Carrier)) (q : ℕ)
    (h : ∀ x : E.Carrier, E.canonicalTopologicalData.discreteValuation x ≤ 1 →
      E.canonicalTopologicalData.discreteValuation (σ.symm x - x ^ q) < 1)
    (x : ResidueField (LocalGalois.extensionIntegers F.Carrier E.Carrier)) :
    LocalGalois.residueHom F.Carrier E.Carrier σ⁻¹ x = x ^ q := by
  obtain ⟨x, rfl⟩ := residue_surjective x
  change residue _ (LocalGalois.integerAut F.Carrier E.Carrier σ⁻¹ x) =
    (residue _ x) ^ q
  rw [← map_pow]
  apply (ArithmeticCoordinate.extensionResidueEquiv F E).injective
  change E.canonicalTopologicalData.residue
      (ArithmeticCoordinate.extensionIntegerEquiv F E
        (LocalGalois.integerAut F.Carrier E.Carrier σ⁻¹ x)) =
    E.canonicalTopologicalData.residue
      (ArithmeticCoordinate.extensionIntegerEquiv F E (x ^ q))
  apply (NYLL.suppliedResidueCongruence E E.canonicalTopologicalData _ _).mpr
  exact h (x : E.Carrier)
    (discreteValuation_le_one E E.canonicalTopologicalData
      (ArithmeticCoordinate.extensionIntegerEquiv F E x))

/-- An inverse residue-power congruence identifies the geometric cyclic
coordinate of an automorphism of an unramified extension. -/
theorem inverse_coordinate_eq_one (T : F.TopologicalData)
    {n : ℕ} [NeZero n]
    (χ : Gal(E.Carrier/F.Carrier) ≃* Multiplicative (ZMod n))
    (hχ : IsArithmeticUnramifiedCoordinate F E.Carrier χ)
    (σ : Gal(E.Carrier/F.Carrier))
    (h : ∀ x : E.Carrier, E.canonicalTopologicalData.discreteValuation x ≤ 1 →
      E.canonicalTopologicalData.discreteValuation
        (σ.symm x - x ^ T.residueCardinality) < 1) :
    (χ σ)⁻¹ = Multiplicative.ofAdd 1 := by
  have hcard : T.residueCardinality =
      Nat.card (ResidueField (LocalGalois.baseIntegers F.Carrier)) :=
    (residueCardinality_eq_canonical F T).trans
      (Nat.card_congr (ArithmeticCoordinate.baseResidueEquiv F).toEquiv).symm
  have hσ : σ⁻¹ = χ.symm (Multiplicative.ofAdd 1) := by
    apply hχ.1
    ext x
    rw [residueHom_inverse_power F E σ T.residueCardinality h, hχ.2, hcard]
  have he := congrArg χ hσ
  simpa only [map_inv, χ.apply_symm_apply] using he

end Residue

/-- Every positive cyclic degree has a continuous quotient probe whose value
on every normalized family's uniformizers is the positive generator. -/
theorem cyclic_probe (F : PadicField.{u} p) (T : F.TopologicalData)
    (N : ℕ) (hN : N ≠ 0) :
    letI := T.topology
    ∃ δ : Field.absoluteGaloisGroupAbelianization F.Carrier →ₜ*
        Multiplicative (ZMod N),
      ∀ (r : F.Carrierˣ →ₜ* Field.absoluteGaloisGroupAbelianization F.Carrier),
        GeometricProfiniteReciprocityRelation F T r →
        ∀ b : F.Carrierˣ, T.ord (b : F.Carrier) = 1 →
          δ (r b) = Multiplicative.ofAdd 1 := by
  let := T.topology
  obtain ⟨E, hGal, hE, hdeg⟩ :=
    unramifiedExtensionDegreeExistence p F N (Nat.pos_of_ne_zero hN)
  subst N
  let := hGal
  let E' := E.asPadicField (p := p)
  let : Algebra (Padic p) E'.Carrier := E'.algebra
  let : IsScalarTower (Padic p) F.Carrier E'.Carrier :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : NeZero (Module.finrank F.Carrier E.field) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨χ, hχ⟩ := ArithmeticCoordinate.coordinate_exists F E' hE
  have hcomm : IsMulCommutative Gal(E.field/F.Carrier) := .of_comm fun s t => by
    apply χ.injective
    simp only [map_mul, mul_comm]
  let L : FiniteAbelianExtension F.Carrier :=
    ⟨{ toIntermediateField := E.field }, hcomm⟩
  let c : L.galoisGroup →ₜ* Multiplicative (ZMod (Module.finrank F.Carrier E.field)) :=
    { toFun σ := (χ σ)⁻¹
      map_one' := by simp
      map_mul' s t := by simp [mul_comm]
      continuous_toFun := continuous_of_discreteTopology }
  refine ⟨c.comp L.abelianRestriction, ?_⟩
  intro r hr b hb
  exact inverse_coordinate_eq_one F E' T χ hχ (finiteFamilyOfHom r L b)
    (hr.2 L (L.asPadicField (p := p)).canonicalTopologicalData b hb)

/-- Open norm kernels and all cyclic probes determine the image of each
base-field unit of order one. -/
theorem profinite_eq_of_ord_eq_one (F : PadicField.{u} p) (T : F.TopologicalData) :
    letI := T.topology
    ∀ {r₁ r₂ : F.Carrierˣ →ₜ* Field.absoluteGaloisGroupAbelianization F.Carrier},
      GeometricProfiniteReciprocityRelation F T r₁ →
      GeometricProfiniteReciprocityRelation F T r₂ →
      ∀ b : F.Carrierˣ, T.ord (b : F.Carrier) = 1 → r₁ b = r₂ b := by
  let := T.topology
  intro r₁ r₂ h₁ h₂ b hb
  let := Algebra.charZero_of_charZero (Padic p) F.Carrier
  let : IsGalois F.Carrier (AlgebraicClosure F.Carrier) := ⟨⟩
  let : CompactSpace (Field.absoluteGaloisGroup F.Carrier) :=
    inferInstanceAs (CompactSpace Gal(AlgebraicClosure F.Carrier/F.Carrier))
  let := absoluteGaloisNonarchimedean F.Carrier
  let := abelianizationHausdorff (Field.absoluteGaloisGroup F.Carrier)
  let := quotientNonarchimedean
    (commutator (Field.absoluteGaloisGroup F.Carrier)).topologicalClosure
  refine ReciprocitySystemUniqueness.eq_of_forall_openSubgroup ?_ 1 (by norm_num) ?_
  · intro H hH hmem
    exact (WeilReciprocityUniqueness.mem_openSubgroup_iff h₁.1 h₂.1 H hH b).mp hmem
  · intro N hN
    obtain ⟨δ, hδ⟩ := cyclic_probe F T N hN
    refine ⟨{ toFun := fun g => δ g
              map_one' := map_one δ
              map_mul' := fun g h => map_mul δ g h }, ?_, ?_, ?_⟩
    · exact (isOpen_discrete ({1} : Set (Multiplicative (ZMod N)))).preimage δ.continuous
    · change δ (r₁ b) = Multiplicative.ofAdd ((1 : ℤ) : ZMod N)
      simpa only [Int.cast_one] using hδ r₁ h₁ b hb
    · change δ (r₂ b) = Multiplicative.ofAdd ((1 : ℤ) : ZMod N)
      simpa only [Int.cast_one] using hδ r₂ h₂ b hb

/-- Multiplying by a suitable uniformizer power reduces every unit to
order one, so the normalized profinite homomorphism is unique. -/
theorem profinite_eq (F : PadicField.{u} p) (T : F.TopologicalData) :
    letI := T.topology
    ∀ {r₁ r₂ : F.Carrierˣ →ₜ* Field.absoluteGaloisGroupAbelianization F.Carrier},
      GeometricProfiniteReciprocityRelation F T r₁ →
      GeometricProfiniteReciprocityRelation F T r₂ → r₁ = r₂ := by
  let := T.topology
  intro r₁ r₂ h₁ h₂
  let π := LocalFactor.PadicAbelian.uniformizerUnit T
  have hπ : T.ord (π : F.Carrier) = 1 :=
    LocalFactor.PadicAbelian.uniformizerUnit_ord T
  have heπ : r₁ π = r₂ π := profinite_eq_of_ord_eq_one F T h₁ h₂ π hπ
  apply ContinuousMonoidHom.ext
  intro x
  let k : ℤ := 1 - T.ord (x : F.Carrier)
  have hxπ : T.ord ((x * π ^ k : F.Carrierˣ) : F.Carrier) = 1 := by
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val,
      T.ord_mul x.ne_zero (zpow_ne_zero k π.ne_zero), T.ord_zpow, hπ, mul_one]
    dsimp only [k]
    omega
  have h := profinite_eq_of_ord_eq_one F T h₁ h₂ (x * π ^ k) hxπ
  rw [map_mul, map_mul, map_zpow, map_zpow, heπ] at h
  exact mul_right_cancel h

end FiniteArtinSystemUniqueness

/-- The full geometric finite-system relation determines the entire
coherent family, for every prime, carrier universe and supplied topology. -/
theorem geometricFiniteArtinSystemUniqueness :
    GeometricFiniteArtinSystemUniqueness.{u} := by
  intro p _ F T a₁ a₂ h₁ h₂
  let := T.topology
  let := Algebra.charZero_of_charZero (Padic p) F.Carrier
  have hr₁ := ProfiniteReciprocityReconstruction.reconstruct_geometric F T a₁ h₁.1 h₁.2
  have hr₂ := ProfiniteReciprocityReconstruction.reconstruct_geometric F T a₂ h₂.1 h₂.2
  have he := FiniteArtinSystemUniqueness.profinite_eq F T hr₁ hr₂
  calc a₁ = finiteFamilyOfHom (FiniteArtinReconstruction.reconstruct F.Carrier a₁ h₁.1.2) :=
      (FiniteArtinReconstruction.finiteFamilyOfHom_reconstruct F.Carrier a₁ h₁.1.2).symm
    _ = finiteFamilyOfHom (FiniteArtinReconstruction.reconstruct F.Carrier a₂ h₂.1.2) :=
      congrArg finiteFamilyOfHom he
    _ = a₂ := FiniteArtinReconstruction.finiteFamilyOfHom_reconstruct F.Carrier a₂ h₂.1.2

end Langlands.LocalClassField
