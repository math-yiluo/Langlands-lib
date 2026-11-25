import Langlands.ClassFieldTheory.Local.Artin.FiniteArtin
import Langlands.ClassFieldTheory.Local.FiniteUnramifiedFrobenius
import Langlands.ClassFieldTheory.Local.FiniteUnramifiedLocalField
import Langlands.ClassFieldTheory.Local.LocalFieldOrder
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseFrobenius

/-!
# The arithmetic normalization of the local Artin map on unramified extensions

This file belongs to the Library. It proves that the arithmetic Artin map
`arithmeticFiniteArtin K L` of `FiniteArtin.lean` sends an element `x` of `Kˣ` to the arithmetic
Frobenius raised to the normalized order of `x`, on every finite unramified extension, in two
vocabularies:

* NYLL's (`arithmeticFiniteArtin_eq_arithmeticFrobenius_zpow`): `L` a nonarchimedean local field
  with `Valuation.HasExtension` and NYLL's `IsUnramifiedValuedExtension K L`, Frobenius NYLL's
  `arithmeticFrobeniusOfUnramifiedValuation K L`;
* the Library's (`arithmeticFiniteArtin_eq_finiteUnramifiedFrobenius_zpow`): `E` a finite Galois
  intermediate field of Mathlib's `SeparableClosure K` with `ArithmeticUnramified K E`, Frobenius the
  Library's `finiteUnramifiedFrobenius K E hE` (the lift of `x ↦ x ^ q` on residues), order the
  Library's `normalizedUnitOrder K`.

The order of NYLL (`valuationMap`) is minus the Library's (`valuationMap_eq_neg_normalizedUnitOrder`).
The two Frobenius elements are matched through their action on residues: the integer ring of the
spectral local-field structure of `E` is the Library's `extensionIntegers K E`
(`spectralFiniteExtensionIntegerEquiv`), and the residue action of a Galois group of an unramified
extension is faithful (`finiteUnramified_residueHom_injective`).
-/

noncomputable section

universe u v

namespace Langlands.ClassFieldTheory.Local.Artin

open ValuativeRel IsLocalRing LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField
open Langlands.LocalField Langlands.LocalGalois Langlands.LocalGalois.Separable

section Order

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- NYLL's normalized valuation of a unit is minus the Library's normalized order. -/
theorem valuationMap_eq_neg_normalizedUnitOrder (x : Kˣ) :
    valuationMap K (Additive.ofMul x) = -normalizedUnitOrder K (.ofMul x) := by
  have h : normalizedUnitOrder K (.ofMul x) = -WithZero.log (discreteLocalValuation K (x : K)) := rfl
  rw [h, neg_neg]
  have h2 : discreteLocalValuation K (x : K) =
      ((WithZero.unitsWithZeroEquiv
        (Units.map (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).toMonoidHom
          (Units.map (valuation K).toMonoidWithZeroHom.toMonoidHom x)) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) := by
    rw [WithZero.coe_unitsWithZeroEquiv_eq_units_val]
    rfl
  rw [h2]
  rfl

theorem valuationMap_inv_eq_normalizedUnitOrder (x : Kˣ) :
    valuationMap K (Additive.ofMul x⁻¹) = normalizedUnitOrder K (.ofMul x) := by
  rw [valuationMap_eq_neg_normalizedUnitOrder, ofMul_inv, map_neg, neg_neg]

end Order

section NYLL

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  (L : Type v) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
  [Valuation.HasExtension (valuation K) (valuation L)] [IsUnramifiedValuedExtension K L]

/-- On a finite unramified extension (NYLL's vocabulary), the arithmetic Artin map sends `x` to
the arithmetic Frobenius raised to the normalized order of `x`. -/
theorem arithmeticFiniteArtin_eq_arithmeticFrobenius_zpow (x : Kˣ) :
    arithmeticFiniteArtin K L x =
      arithmeticFrobeniusOfUnramifiedValuation K L ^ normalizedUnitOrder K (.ofMul x) := by
  rw [arithmeticFiniteArtin_apply, ← valuationMap_inv_eq_normalizedUnitOrder]
  exact LocalClassFieldTheory.Universe.abelianLocalArtinMonoidHom_eq_frobenius_zpow K L x⁻¹

/-- On a finite unramified extension (NYLL's vocabulary), an element of normalized order one (a
uniformizer) goes to the arithmetic Frobenius. -/
theorem arithmeticFiniteArtin_of_normalizedUnitOrder_eq_one (π : Kˣ)
    (hπ : normalizedUnitOrder K (.ofMul π) = 1) :
    arithmeticFiniteArtin K L π = arithmeticFrobeniusOfUnramifiedValuation K L := by
  rw [arithmeticFiniteArtin_eq_arithmeticFrobenius_zpow, hπ, zpow_one]

/-- On a finite unramified extension (NYLL's vocabulary), the arithmetic Artin symbol of an element
of normalized order one acts on residues as `x ↦ x ^ q`, `q` the order of the residue field of
`K`. -/
theorem arithmeticFiniteArtin_residue_pow (π : Kˣ) (hπ : normalizedUnitOrder K (.ofMul π) = 1)
    (x : 𝒪[L]) :
    ∃ z : 𝒪[L], (z : L) = arithmeticFiniteArtin K L π (x : L) ∧
      residue 𝒪[L] z = residue 𝒪[L] x ^ Nat.card 𝓀[K] := by
  have h : valuationMap K (Additive.ofMul π⁻¹) = 1 := by
    rw [valuationMap_inv_eq_normalizedUnitOrder, hπ]
  exact LocalClassFieldTheory.Universe.abelianLocalArtinMap_inverseUniformizer_residue_pow K L π⁻¹ h x

end NYLL

section Spectral

/-! The spectral local-field structure of a finite intermediate field of the separable closure,
and NYLL's classes on it. -/

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The valuation of a finite extension with its spectral valuative relation extends the valuation
of `K`. -/
theorem spectral_hasExtension (X : Type u) [Field X] [Algebra K X] [FiniteDimensional K X] :
    letI := FiniteExtension.valuativeRel K X
    (valuation K).HasExtension (valuation X) := by
  let := FiniteExtension.valuativeRel K X
  constructor
  intro x y
  simp only [Valuation.comap_apply]
  rw [← Valuation.vle_iff_le, ← Valuation.vle_iff_le]
  exact (FiniteExtension.algebraMap_vle_iff K X x y).symm

private theorem map_maximalIdeal_eq_of_ringEquivs
    {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing R'] [IsLocalRing S']
    (eR : R ≃+* R') (eS : S ≃+* S') {f : R →+* S} {g : R' →+* S'}
    (hcomm : eS.toRingHom.comp f = g.comp eR.toRingHom)
    (hmap : (maximalIdeal R').map g = maximalIdeal S') :
    (maximalIdeal R).map f = maximalIdeal S := by
  have hinv : f.comp eR.symm.toRingHom = eS.symm.toRingHom.comp g := by
    apply RingHom.ext
    intro x
    apply eS.injective
    change eS (f (eR.symm x)) = eS (eS.symm (g x))
    rw [eS.apply_symm_apply]
    have hx := DFunLike.congr_fun hcomm (eR.symm x)
    change eS (f (eR.symm x)) = g (eR (eR.symm x)) at hx
    rwa [eR.apply_symm_apply] at hx
  have hm := congrArg (Ideal.map eS.symm.toRingHom) hmap
  rw [Ideal.map_map, ← hinv, ← Ideal.map_map,
    map_maximalIdeal_of_surjective eR.symm.toRingHom eR.symm.surjective,
    map_maximalIdeal_of_surjective eS.symm.toRingHom eS.symm.surjective] at hm
  exact hm

private theorem ramificationIdx_eq_one_of_map_maximalIdeal
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    (hmap : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S) :
    (maximalIdeal S).ramificationIdx R = 1 := by
  let q := maximalIdeal S
  let Sq := Localization.AtPrime q
  change q.ramificationIdx R = 1
  rw [Ideal.ramificationIdx_eq (maximalIdeal R) q, ENat.toNat_eq_iff_eq_natCast,
    Nat.cast_one, Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def,
    IsLocalRing.isMaximal_iff, IsScalarTower.algebraMap_eq R S Sq, ← Ideal.map_map, hmap,
    Localization.AtPrime.map_eq_maximalIdeal]

variable (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E] [IsGalois K E]

local instance spectralBaseNormedField : NontriviallyNormedField K := localNormedField K
local instance spectralBaseUltrametric : IsUltrametricDist K := localNormedField_ultrametric K
local instance spectralBaseComplete : CompleteSpace K := localNormedField_complete K

/-- The integer ring of the valuative relation of `K` is the Library's `baseIntegers K` (the unit
ball of `LocalGalois.localNormedField K`). -/
def baseIntegerEquiv : 𝒪[K] ≃+* baseIntegers K :=
  RingEquiv.subringCongr (localNormedField_integer K).symm

/-- An arithmetic-unramified stage is unramified in NYLL's sense for the spectral local-field
structure. -/
theorem isUnramifiedValuedExtension_of_arithmeticUnramified (hE : ArithmeticUnramified K E) :
    letI := FiniteExtension.normedField K E
    letI := FiniteExtension.valuativeRel K E
    haveI := FiniteExtension.isLocalField K E
    haveI := spectral_hasExtension K E
    IsUnramifiedValuedExtension K E := by
  let := FiniteExtension.normedField K E
  let := FiniteExtension.valuativeRel K E
  have := FiniteExtension.isLocalField K E
  have := spectral_hasExtension K E
  have hcomm : (spectralFiniteExtensionIntegerEquiv K E).toRingHom.comp
      (algebraMap 𝒪[K] 𝒪[E]) =
      (algebraMap (baseIntegers K) (extensionIntegers K E)).comp
        (baseIntegerEquiv K).toRingHom := by
    apply RingHom.ext
    intro x
    rfl
  exact ⟨ramificationIdx_eq_one_of_map_maximalIdeal
    (map_maximalIdeal_eq_of_ringEquivs (baseIntegerEquiv K) (spectralFiniteExtensionIntegerEquiv K E)
      hcomm hE.1)⟩

omit [FiniteDimensional K E] in
/-- The Galois group of an arithmetic-unramified stage is cyclic, generated by the arithmetic
Frobenius; in particular the stage is abelian. -/
theorem isAbelianGalois_of_arithmeticUnramified (hE : ArithmeticUnramified K E)
    [FiniteDimensional K E] : IsAbelianGalois K E where
  is_comm := ⟨fun σ τ => by
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (finiteUnramifiedFrobenius_generates K E hE σ)
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (finiteUnramifiedFrobenius_generates K E hE τ)
    exact zpow_mul_comm _ _ _⟩

/-- On an arithmetic-unramified stage, the arithmetic Artin symbol of an element of normalized
order one acts on the Library's residue field as `x ↦ x ^ q`, `q` the order of the residue field
of `K`. -/
theorem residueHom_arithmeticFiniteArtin (hE : ArithmeticUnramified K E)
    (π : Kˣ) (hπ : normalizedUnitOrder K (.ofMul π) = 1)
    (y : ResidueField (extensionIntegers K E)) :
    haveI := isAbelianGalois_of_arithmeticUnramified K E hE
    residueHom K E (arithmeticFiniteArtin K E π) y =
      y ^ Nat.card (ResidueField (baseIntegers K)) := by
  have := isAbelianGalois_of_arithmeticUnramified K E hE
  obtain ⟨x, rfl⟩ := residue_surjective y
  let := FiniteExtension.normedField K E
  let := FiniteExtension.valuativeRel K E
  have := FiniteExtension.isLocalField K E
  have := spectral_hasExtension K E
  have := isUnramifiedValuedExtension_of_arithmeticUnramified K E hE
  let e := spectralFiniteExtensionIntegerEquiv K E
  obtain ⟨z, hz, hres⟩ := arithmeticFiniteArtin_residue_pow K E π hπ (e.symm x)
  rw [residueHom_apply]
  have hz' : integerAut K E (arithmeticFiniteArtin K E π) x = e z :=
    Subtype.ext hz.symm
  rw [hz', Nat.card_congr (localResidueEquiv K).toEquiv]
  have h := congrArg (ResidueField.mapEquiv e) hres
  have h1 : ResidueField.mapEquiv e (residue 𝒪[E] z) = residue (extensionIntegers K E) (e z) := rfl
  have h2 : ResidueField.mapEquiv e (residue 𝒪[E] (e.symm x)) = residue (extensionIntegers K E) x := by
    change residue (extensionIntegers K E) (e (e.symm x)) = _
    rw [RingEquiv.apply_symm_apply]
  rw [map_pow, h1, h2] at h
  exact h

/-- On an arithmetic-unramified stage, an element of normalized order one goes to the Library's
arithmetic Frobenius `finiteUnramifiedFrobenius K E hE`. -/
theorem arithmeticFiniteArtin_eq_finiteUnramifiedFrobenius (hE : ArithmeticUnramified K E)
    (π : Kˣ) (hπ : normalizedUnitOrder K (.ofMul π) = 1) :
    haveI := isAbelianGalois_of_arithmeticUnramified K E hE
    arithmeticFiniteArtin K E π = finiteUnramifiedFrobenius K E hE := by
  have := isAbelianGalois_of_arithmeticUnramified K E hE
  apply finiteUnramified_residueHom_injective K E hE
  apply AlgEquiv.ext
  intro y
  rw [residueHom_arithmeticFiniteArtin K E hE π hπ, finiteUnramifiedFrobenius_residue]

/-- **Arithmetic normalization.** On an arithmetic-unramified stage `E` of `SeparableClosure K`, the
arithmetic Artin map sends `x` to the Library's arithmetic Frobenius raised to the normalized order
of `x`. -/
theorem arithmeticFiniteArtin_eq_finiteUnramifiedFrobenius_zpow (hE : ArithmeticUnramified K E)
    (x : Kˣ) :
    haveI := isAbelianGalois_of_arithmeticUnramified K E hE
    arithmeticFiniteArtin K E x =
      finiteUnramifiedFrobenius K E hE ^ normalizedUnitOrder K (.ofMul x) := by
  have := isAbelianGalois_of_arithmeticUnramified K E hE
  let := FiniteExtension.normedField K E
  let := FiniteExtension.valuativeRel K E
  have := FiniteExtension.isLocalField K E
  have := spectral_hasExtension K E
  have := isUnramifiedValuedExtension_of_arithmeticUnramified K E hE
  rw [arithmeticFiniteArtin_eq_arithmeticFrobenius_zpow K E x,
    ← arithmeticFiniteArtin_of_normalizedUnitOrder_eq_one K E (localUniformizer K)
      (normalizedUnitOrder_localUniformizer K),
    arithmeticFiniteArtin_eq_finiteUnramifiedFrobenius K E hE (localUniformizer K)
      (normalizedUnitOrder_localUniformizer K)]

end Spectral

end Langlands.ClassFieldTheory.Local.Artin
