import Langlands.Algebra.BrauerComparison.RegularClass
import Langlands.ClassFieldTheory.Local.Artin.ArtinLift
import Langlands.ClassFieldTheory.Local.Artin.FiniteArtinNormalization
import Langlands.ClassFieldTheory.Local.FiniteUnramifiedDegree
import Langlands.GaloisCohomology.Field.RelativeInflation
import Langlands.GaloisCohomology.Local.CharacterCup
import Langlands.GaloisCohomology.Local.Invariant

/-!
# The cup symbol of local Galois cohomology

For a nonarchimedean local field `K` with separable closure `Ksep`, a character
`χ : Gal(Ksep/K) → ℚ/ℤ` with open kernel and `a ∈ Kˣ`, the invariant of the cup product
`δχ ∪ a ∈ H²(K, Ksepˣ)` is the value of `χ` at the arithmetic Artin symbol of `a`
(`invariant_characterClass_cup`):

  `inv(δχ ∪ a) = χ(σ)` for every arithmetic Artin lift `σ` of `a`.

## Main statements

* `invariant_unramified`: the invariant of a class inflated (in the cochain model) from a finite
  arithmetic-unramified stage `E` of `SeparableClosure K` is the Library's unramified invariant
  `spectralUnramifiedInvariant K E hE` of the relative class.
* `invariant_characterCup_unramified`: for a character `ψ` of `Gal(E/K)` read on `Gal(Ksep/K)`,
  `inv(δψ ∪ a) = ord(a) · ψ(Frob_E)`, `Frob_E` the arithmetic Frobenius.
* `invariant_characterClass_cup`: the cup symbol.

## Proofs

`invariant_unramified` realizes the relative class by a central simple algebra with a splitting chart
over `E` (`exists_relativeClass_eq`); the Library's Brauer isomorphism takes it to the inflated class
for any separable closure (`brauerContinuousEquiv_at_chart`), and its invariant is computed on the
chart (`localBrauerInvariant_at_chart`). The inflation in the cochain model is the Library's
`relativeToContinuous` (`unitsModuleContinuousEquiv_symm_relativeToContinuous`).

For the unramified cup symbol, the character `ψ₀` of `Gal(E/K)` with `ψ₀(Frob_E) = 1/n`
(`n = [E : K]`) has standard cocycle the carry cocycle of the Library's `cyclicClass`, so
`δψ₀ ∪ a` is the inflation of `cyclicClass K E coord a`, whose invariant is `ord(a)/n`
(`spectralUnramifiedInvariant_cyclicClass`); every `ψ` is a multiple of `ψ₀`.

For the cup symbol, `D(χ, a) = inv(δχ ∪ a) − χ(σ)` is additive in `χ` and in `a`. If `ord(a) ≠ 0`,
subtract from `χ` an unramified character `ψ` (on a large enough unramified stage) with
`ord(a) · ψ(Frob) = χ(σ)`; then `χ − ψ` kills `σ`, so `σ` acts trivially on the fixed field `L'` of
`ker (χ − ψ)`, `a` is a norm from `L'` (the kernel of the Artin map is the norm group), and
`δ(χ − ψ) ∪ a = 0` (`characterCup_eq_zero_of_exists_norm`); together with the unramified case,
`D(χ, a) = 0`. If `ord(a) = 0`, write `a = (aπ)π⁻¹` with `π` a uniformizer and use an Artin lift of
`π` (`exists_isArithmeticArtinLift`).
-/

noncomputable section

namespace Langlands.GaloisCohomology.Local

open CategoryTheory Langlands.ProfiniteCohomology GroupCoh ClassFieldTheory.Local IntermediateField
open Langlands.LocalGalois.Separable Langlands.ClassFieldTheory.Local.Artin BrauerComparison

universe u

section Unramified

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ksep : Type u) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
  (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E] [IsGalois K E]
  [Algebra E Ksep] [IsScalarTower K E Ksep]

/-- The invariant of a class inflated from a finite arithmetic-unramified stage `E` of
`SeparableClosure K` (embedded in `Ksep`) is the Library's unramified invariant of the relative
class (Serre's: valuation, inverse connecting map, arithmetic Frobenius). -/
theorem invariant_unramified (hE : ArithmeticUnramified K E) (x : relativeCohomology K E 2) :
    invariant K Ksep ((unitsTowerMap K E Ksep 2).hom
        ((isoGroupCohomology (unitsModule K E) 2).inv.hom x)) =
      spectralUnramifiedInvariant K E hE x := by
  rw [← unitsModuleContinuousEquiv_symm_relativeToContinuous]
  let := Classical.decEq Gal(E/K)
  obtain ⟨A, e, rfl⟩ := exists_relativeClass_eq (K := K) (L := E) x
  have hA : (unitsModuleContinuousEquiv K Ksep 2).symm
      (relativeToContinuous K E Ksep 2 (relativeClass e)) = brauerEquiv K Ksep (Brauer.classOf A) := by
    rw [← brauerContinuousEquiv_at_chart K Ksep A E e]
    rfl
  rw [hA, invariant_brauerEquiv, localBrauerInvariant_at_chart K A E hE e]

end Unramified

section UnramifiedCup

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ksep : Type u) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
  (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E] [IsGalois K E]
  [Algebra E Ksep] [IsScalarTower K E Ksep]

/-- A character of `Gal(E/K)` read on `Gal(Ksep/K)` through restriction to `E`. -/
abbrev restrictCharacter (ψ : Gal(E/K) →* Multiplicative RationalModIntegers) :
    Gal(Ksep/K) →* Multiplicative RationalModIntegers :=
  ψ.comp (normalKrullRestriction K E Ksep).toMonoidHom

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsSepClosure K Ksep] in
theorem isOpen_ker_restrictCharacter (ψ : Gal(E/K) →* Multiplicative RationalModIntegers) :
    IsOpen ((restrictCharacter K Ksep E ψ).ker : Set Gal(Ksep/K)) := by
  have h : ((restrictCharacter K Ksep E ψ).ker : Set Gal(Ksep/K)) =
      (normalKrullRestriction K E Ksep) ⁻¹' (ψ.ker : Set Gal(E/K)) := rfl
  rw [h]
  exact (isOpen_discrete _).preimage (normalKrullRestriction K E Ksep).continuous

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsGalois K E] in
private theorem natCast_finrank_smul_rationalClass :
    (Module.finrank K E : ℤ) • rationalClass (1 / (Module.finrank K E : ℚ)) = 0 := by
  rw [← map_zsmul, zsmul_eq_mul, Int.cast_natCast,
    mul_one_div_cancel (Nat.cast_ne_zero.mpr Module.finrank_pos.ne'),
    Langlands.ClassFieldTheory.Global.FundamentalClass.rationalClass_eq_zero_iff]
  exact ⟨1, by simp⟩

local instance finrankNeZero : NeZero (Module.finrank K E) := ⟨Module.finrank_pos.ne'⟩

/-- On an arithmetic-unramified stage `E` of degree `n`, the character of `Gal(E/K)` with value
`1/n` at the arithmetic Frobenius. -/
def frobeniusCharacter (hE : ArithmeticUnramified K E) :
    Gal(E/K) →* Multiplicative RationalModIntegers :=
  (AddMonoidHom.toMultiplicative (ZMod.lift (Module.finrank K E)
    ⟨zmultiplesHom RationalModIntegers (rationalClass (1 / (Module.finrank K E : ℚ))),
      by simpa using natCast_finrank_smul_rationalClass K E⟩)).comp
    (finiteUnramifiedCyclicCoordinate K E hE).toMonoidHom

theorem toAdd_frobeniusCharacter (hE : ArithmeticUnramified K E) (g : Gal(E/K)) :
    (frobeniusCharacter K E hE g).toAdd =
      rationalClass (((finiteUnramifiedCyclicCoordinate K E hE g).toAdd.val : ℚ) /
        Module.finrank K E) := by
  set k := (finiteUnramifiedCyclicCoordinate K E hE g).toAdd
  have hk : k = ((k.val : ℤ) : ZMod (Module.finrank K E)) := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  simp only [frobeniusCharacter, MonoidHom.coe_comp, Function.comp_apply,
    AddMonoidHom.toMultiplicative_apply_apply, toAdd_ofAdd, MulEquiv.coe_toMonoidHom]
  change ZMod.lift (Module.finrank K E) _ k = _
  conv_lhs => rw [hk, ZMod.lift_coe]
  rw [zmultiplesHom_apply, ← map_zsmul, zsmul_eq_mul, Int.cast_natCast, mul_one_div]

theorem reprIco_frobeniusCharacter (hE : ArithmeticUnramified K E) (g : Gal(E/K)) :
    reprIco ((frobeniusCharacter K E hE g).toAdd : AddCircle (1 : ℚ)) =
      ((finiteUnramifiedCyclicCoordinate K E hE g).toAdd.val : ℚ) / Module.finrank K E := by
  rw [toAdd_frobeniusCharacter]
  apply reprIco_coe
  have hn : (0 : ℚ) < Module.finrank K E := Nat.cast_pos.mpr Module.finrank_pos
  constructor
  · positivity
  · rw [div_lt_one hn]
    exact_mod_cast ZMod.val_lt _

omit [IsSepClosure K Ksep] in
/-- The standard cocycle of the Frobenius character read on `Gal(Ksep/K)` is the carry cocycle of
the cyclic coordinate of `Gal(E/K)` (the cocycle of the Library's `cyclicClass`). -/
theorem charCocycle_restrictCharacter_frobeniusCharacter (hE : ArithmeticUnramified K E)
    (g h : Gal(Ksep/K)) :
    charCocycle (charAdd (characterToQZ (restrictCharacter K Ksep E (frobeniusCharacter K E hE))
        (isOpen_ker_restrictCharacter K Ksep E _))) (g, h) =
      (cyclicCarry (finiteUnramifiedCyclicCoordinate K E hE (AlgEquiv.restrictNormalHom E g)).toAdd
        (finiteUnramifiedCyclicCoordinate K E hE (AlgEquiv.restrictNormalHom E h)).toAdd : ℤ) := by
  unfold charCocycle
  rw [charAdd_characterToQZ, charAdd_characterToQZ]
  change ⌊reprIco ((frobeniusCharacter K E hE (AlgEquiv.restrictNormalHom E g)).toAdd :
      AddCircle (1 : ℚ)) +
    reprIco ((frobeniusCharacter K E hE (AlgEquiv.restrictNormalHom E h)).toAdd :
      AddCircle (1 : ℚ))⌋ = _
  rw [reprIco_frobeniusCharacter, reprIco_frobeniusCharacter, ← add_div, ← Nat.cast_add,
    Rat.floor_natCast_div_natCast]
  unfold cyclicCarry
  push_cast
  rfl

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsSepClosure K Ksep]
  [FiniteDimensional K E] [IsGalois K E] in
/-- The unit `a ∈ Kˣ` of `E` maps to the unit `a` of `Ksep`. -/
theorem unitInclusion_baseUnit (a : Kˣ) : unitInclusion E Ksep (baseUnit K E a) = baseUnit K Ksep a := by
  apply Units.ext
  exact (IsScalarTower.algebraMap_apply K E Ksep (a : K)).symm

/-- `δψ₀ ∪ a` for the Frobenius character `ψ₀` of an unramified stage is the inflation of the
Library's cyclic class of `a`. -/
theorem characterCup_frobeniusCharacter (hE : ArithmeticUnramified K E) (a : Kˣ) :
    characterCup K Ksep (restrictCharacter K Ksep E (frobeniusCharacter K E hE))
        (isOpen_ker_restrictCharacter K Ksep E _) a =
      (unitsTowerMap K E Ksep 2).hom ((isoGroupCohomology (unitsModule K E) 2).inv.hom
        (cyclicClass K E (finiteUnramifiedCyclicCoordinate K E hE).toMonoidHom a)) := by
  rw [← unitsModuleContinuousEquiv_symm_relativeToContinuous]
  obtain ⟨w, hw, hwc⟩ := exists_cocycle_relativeToContinuous_H2π K E Ksep
    (cyclicUnitCocycle K E (finiteUnramifiedCyclicCoordinate K E hE).toMonoidHom a)
  rw [cyclicClass, ← hw, characterCup]
  congr 1
  apply cocycleι_injective
  apply cochainOf_injective
  funext v
  rw [cochainOf_cocycleι_characterCupCocycle, hwc, charCocycle_restrictCharacter_frobeniusCharacter,
    natCast_zsmul]
  rw [← unitInclusion_baseUnit K Ksep E a]
  exact (map_nsmul (unitInclusion E Ksep) _ _).symm

/-- The invariant of `δψ₀ ∪ a` for the Frobenius character `ψ₀` of an unramified stage of degree
`n` is `ord(a)/n`. -/
theorem invariant_characterCup_frobeniusCharacter (hE : ArithmeticUnramified K E) (a : Kˣ) :
    invariant K Ksep (characterCup K Ksep (restrictCharacter K Ksep E (frobeniusCharacter K E hE))
        (isOpen_ker_restrictCharacter K Ksep E _) a) =
      rationalClass ((normalizedUnitOrder K (.ofMul a) : ℚ) / Module.finrank K E) := by
  rw [characterCup_frobeniusCharacter, invariant_unramified K Ksep E hE,
    spectralUnramifiedInvariant_cyclicClass]

theorem toAdd_frobeniusCharacter_frobenius (hE : ArithmeticUnramified K E) :
    (frobeniusCharacter K E hE (finiteUnramifiedFrobenius K E hE)).toAdd =
      rationalClass (1 / (Module.finrank K E : ℚ)) := by
  have hc : finiteUnramifiedCyclicCoordinate K E hE (finiteUnramifiedFrobenius K E hE) =
      Multiplicative.ofAdd 1 := by
    rw [← cyclicCoordinateGenerator_finiteUnramified K E hE, cyclicCoordinateGenerator,
      MulEquiv.apply_symm_apply]
  simp only [frobeniusCharacter, MonoidHom.coe_comp, Function.comp_apply,
    AddMonoidHom.toMultiplicative_apply_apply, toAdd_ofAdd, MulEquiv.coe_toMonoidHom]
  have h1 : (1 : ZMod (Module.finrank K E)) = ((1 : ℤ) : ZMod (Module.finrank K E)) :=
    Int.cast_one.symm
  rw [hc, toAdd_ofAdd, h1, ZMod.lift_coe, zmultiplesHom_apply, one_zsmul]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsSepClosure K Ksep]
  [FiniteDimensional K E] in
theorem restrictCharacter_pow (ψ : Gal(E/K) →* Multiplicative RationalModIntegers) (m : ℕ) :
    restrictCharacter K Ksep E (ψ ^ m) = restrictCharacter K Ksep E ψ ^ m := by
  ext g
  rfl

/-- **Unramified cup symbol.** For an arithmetic-unramified stage `E` of `SeparableClosure K`
embedded in `Ksep` and a character `ψ` of `Gal(E/K)`, read on `Gal(Ksep/K)`,
`inv(δψ ∪ a) = ord(a) · ψ(Frob_E)`. -/
theorem invariant_characterCup_unramified (hE : ArithmeticUnramified K E)
    (ψ : Gal(E/K) →* Multiplicative RationalModIntegers) (a : Kˣ) :
    invariant K Ksep (characterCup K Ksep (restrictCharacter K Ksep E ψ)
        (isOpen_ker_restrictCharacter K Ksep E ψ) a) =
      normalizedUnitOrder K (.ofMul a) • (ψ (finiteUnramifiedFrobenius K E hE)).toAdd := by
  set n := Module.finrank K E with hn_def
  have hn : 0 < n := Module.finrank_pos
  set F := finiteUnramifiedFrobenius K E hE
  have hFn : F ^ n = 1 := by
    have hcard : Nat.card Gal(E/K) = n := IsGalois.card_aut_eq_finrank K E
    rw [← hcard]
    exact pow_card_eq_one'
  have hq : n • QZ.toRationalModIntegers.symm (ψ F).toAdd = 0 := by
    change n • (ψ F).toAdd = 0
    rw [← toAdd_pow, ← map_pow, hFn, map_one, toAdd_one]
  obtain ⟨m, hm⟩ := QZ.exists_eq_nsmul_mk_one_div hn hq
  have hψF : (ψ F).toAdd = m • rationalClass (1 / (n : ℚ)) := hm
  have hψ : ψ = frobeniusCharacter K E hE ^ m := by
    apply MonoidHom.ext
    intro g
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (finiteUnramifiedFrobenius_generates K E hE g)
    rw [map_zpow, map_zpow]
    congr 1
    apply Multiplicative.toAdd.injective
    rw [MonoidHom.pow_apply, toAdd_pow, toAdd_frobeniusCharacter_frobenius, hψF]
  have h0 := isOpen_ker_restrictCharacter K Ksep E (frobeniusCharacter K E hE)
  have hm' : IsOpen ((restrictCharacter K Ksep E (frobeniusCharacter K E hE) ^ m).ker :
      Set Gal(Ksep/K)) := by
    rw [← restrictCharacter_pow]
    exact isOpen_ker_restrictCharacter K Ksep E _
  rw [characterCup_congr K Ksep (show restrictCharacter K Ksep E ψ =
      restrictCharacter K Ksep E (frobeniusCharacter K E hE) ^ m by rw [hψ, restrictCharacter_pow])
      _ hm', characterCup_pow_left K Ksep _ h0 m hm' a, map_nsmul,
    invariant_characterCup_frobeniusCharacter, hψF, smul_comm, ← map_zsmul, zsmul_eq_mul,
    mul_one_div]

end UnramifiedCup

section CupSymbol

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ksep : Type u) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]

section FixedField

variable {K Ksep}

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The fixed field of the kernel of a character with open kernel is finite over `K`. -/
theorem finiteDimensional_fixedField_ker (χ : Gal(Ksep/K) →* Multiplicative RationalModIntegers)
    (hχ : IsOpen (χ.ker : Set Gal(Ksep/K))) : FiniteDimensional K (fixedField χ.ker) :=
  finiteDimensional_fixedField_openSubgroup ⟨χ.ker, hχ⟩

omit [IsSepClosure K Ksep] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- An element of the kernel of `χ` acts trivially on the fixed field of the kernel. -/
theorem restrictNormalHom_fixedField_ker_eq_one [IsGalois K Ksep]
    (χ : Gal(Ksep/K) →* Multiplicative RationalModIntegers) {g : Gal(Ksep/K)} (hg : g ∈ χ.ker) :
    AlgEquiv.restrictNormalHom (fixedField χ.ker) g = 1 := by
  apply AlgEquiv.ext
  intro x
  apply Subtype.val_injective
  rw [AlgEquiv.restrictNormalHom_apply, AlgEquiv.one_apply]
  exact (mem_fixedField_iff _ _).1 x.2 g hg

omit [IsSepClosure K Ksep] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The fixed field of the kernel of a character is abelian over `K`. -/
theorem isAbelianGalois_fixedField_ker [IsGalois K Ksep]
    (χ : Gal(Ksep/K) →* Multiplicative RationalModIntegers) :
    IsAbelianGalois K (fixedField χ.ker) where
  is_comm := ⟨fun x y => by
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective Ksep x
    obtain ⟨τ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective Ksep y
    have hc : (τ * σ)⁻¹ * (σ * τ) ∈ χ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, mul_comm (χ τ) (χ σ),
        inv_mul_cancel]
    rw [← map_mul, ← map_mul, ← mul_inv_cancel_left (τ * σ) (σ * τ), map_mul (f :=
      AlgEquiv.restrictNormalHom (fixedField χ.ker)) (τ * σ),
      restrictNormalHom_fixedField_ker_eq_one χ hc, mul_one]⟩

end FixedField

variable {K Ksep}

/-- If an arithmetic Artin lift `σ` of `a` lies in the kernel of `χ`, then `δχ ∪ a = 0`: `σ` acts
trivially on the fixed field `L'` of `ker χ`, so the Artin symbol of `a` for `L' / K` is trivial and
`a` is a norm from `L'`. -/
theorem characterCup_eq_zero_of_isArithmeticArtinLift
    (χ : Gal(Ksep/K) →* Multiplicative RationalModIntegers) (hχ : IsOpen (χ.ker : Set Gal(Ksep/K)))
    {a : Kˣ} {σ : Gal(Ksep/K)} (hσ : IsArithmeticArtinLift K Ksep a σ) (h1 : χ σ = 1) :
    characterCup K Ksep χ hχ a = 0 := by
  have := finiteDimensional_fixedField_ker χ hχ
  have := isAbelianGalois_fixedField_ker (K := K) χ
  apply characterCup_eq_zero_of_exists_norm χ hχ a
  have hA : arithmeticFiniteArtin K (fixedField χ.ker) a = 1 := by
    rw [← hσ (fixedField χ.ker)]
    exact restrictNormalHom_fixedField_ker_eq_one χ h1
  obtain ⟨y, hy⟩ := (arithmeticFiniteArtin_eq_one_iff K (fixedField χ.ker) a).1 hA
  exact ⟨y, congrArg Units.val hy⟩

/-- For an arithmetic-unramified stage `E` and an arithmetic Artin lift `σ` of `a`, the invariant of
`δψ ∪ a` for a character `ψ` of `Gal(E/K)` is `ψ(σ|_E)`. -/
theorem invariant_characterCup_restrictCharacter_of_isArithmeticArtinLift
    (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E] [IsGalois K E]
    [Algebra E Ksep] [IsScalarTower K E Ksep] (hE : ArithmeticUnramified K E)
    (ψ : Gal(E/K) →* Multiplicative RationalModIntegers) {a : Kˣ} {σ : Gal(Ksep/K)}
    (hσ : IsArithmeticArtinLift K Ksep a σ) :
    invariant K Ksep (characterCup K Ksep (restrictCharacter K Ksep E ψ)
        (isOpen_ker_restrictCharacter K Ksep E ψ) a) =
      (restrictCharacter K Ksep E ψ σ).toAdd := by
  have := isAbelianGalois_of_arithmeticUnramified K E hE
  rw [invariant_characterCup_unramified K Ksep E hE]
  change _ = (ψ (AlgEquiv.restrictNormalHom E σ)).toAdd
  rw [hσ.restrictNormalHom_eq E, arithmeticFiniteArtin_eq_finiteUnramifiedFrobenius_zpow K E hE,
    map_zpow, toAdd_zpow]

/-- The cup symbol when `a` has nonzero normalized order. -/
private theorem invariant_characterClass_cup_of_ne_zero
    (χ : Gal(Ksep/K) →* Multiplicative RationalModIntegers) (hχ : IsOpen (χ.ker : Set Gal(Ksep/K)))
    {a : Kˣ} (ha : normalizedUnitOrder K (.ofMul a) ≠ 0) {σ : Gal(Ksep/K)}
    (hσ : IsArithmeticArtinLift K Ksep a σ) :
    invariant K Ksep (characterCup K Ksep χ hχ a) = (χ σ).toAdd := by
  set d := normalizedUnitOrder K (.ofMul a) with hd
  obtain ⟨r, hr⟩ := QuotientAddGroup.mk_surjective (s := AddSubgroup.zmultiples (1 : ℚ)) (χ σ).toAdd
  have hd0 : (d : ℚ) ≠ 0 := Int.cast_ne_zero.mpr ha
  set q : RationalModIntegers := rationalClass (r / d)
  have hdq : d • q = (χ σ).toAdd := by
    rw [← hr, ← map_zsmul, zsmul_eq_mul, mul_div_cancel₀ _ hd0]
    rfl
  have hzq : ((r.den : ℤ) * d) • q = 0 := by
    change ((r.den : ℤ) * d) • rationalClass (r / d) = 0
    rw [← map_zsmul, zsmul_eq_mul,
      Langlands.ClassFieldTheory.Global.FundamentalClass.rationalClass_eq_zero_iff]
    refine ⟨r.num, ?_⟩
    push_cast
    rw [mul_assoc, mul_div_cancel₀ r hd0, mul_comm]
    exact (Rat.mul_den_eq_num r).symm
  set n := ((r.den : ℤ) * d).natAbs with hn_def
  have hn : 0 < n := Int.natAbs_pos.mpr (mul_ne_zero (Int.natCast_ne_zero.mpr r.den_nz) ha)
  obtain ⟨E, hEfin, hEgal, hE, hEn⟩ := exists_finiteUnramified_finrank K n hn
  have : IsSepClosed Ksep := IsSepClosure.sep_closed K
  let ι : SeparableClosure K →ₐ[K] Ksep := IsSepClosed.lift
  let : Algebra E Ksep := (ι.comp E.val).toRingHom.toAlgebra
  have : IsScalarTower K E Ksep := IsScalarTower.of_algHom (ι.comp E.val)
  have hnq : n • QZ.toRationalModIntegers.symm q = 0 := by
    change n • q = 0
    rw [hn_def, natAbs_nsmul_eq_zero]
    exact hzq
  rw [← hEn] at hnq
  obtain ⟨m, hm⟩ := QZ.exists_eq_nsmul_mk_one_div Module.finrank_pos hnq
  set ψ := frobeniusCharacter K E hE ^ m
  have hψF : (ψ (finiteUnramifiedFrobenius K E hE)).toAdd = q := by
    rw [MonoidHom.pow_apply, toAdd_pow, toAdd_frobeniusCharacter_frobenius]
    exact hm.symm
  have hψσ : (restrictCharacter K Ksep E ψ σ).toAdd = (χ σ).toAdd := by
    rw [← invariant_characterCup_restrictCharacter_of_isArithmeticArtinLift E hE ψ hσ,
      invariant_characterCup_unramified K Ksep E hE, hψF, hdq]
  set ψ' := restrictCharacter K Ksep E ψ
  have hψ' : IsOpen (ψ'.ker : Set Gal(Ksep/K)) := isOpen_ker_restrictCharacter K Ksep E ψ
  have hχ' : IsOpen ((χ * ψ'⁻¹).ker : Set Gal(Ksep/K)) := by
    refine Subgroup.isOpen_mono (H₁ := χ.ker ⊓ ψ'.ker) (fun g hg => ?_) (hχ.inter hψ')
    rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hg
    rw [MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.inv_apply, hg.1, hg.2, inv_one, one_mul]
  have h1 : (χ * ψ'⁻¹) σ = 1 := by
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one]
    exact (Multiplicative.toAdd.injective hψσ).symm
  have hsplit : χ = (χ * ψ'⁻¹) * ψ' := by rw [inv_mul_cancel_right]
  rw [characterCup_congr K Ksep hsplit hχ (isOpen_ker_mul hχ' hψ'),
    characterCup_mul_left K Ksep _ _ hχ' hψ', characterCup_eq_zero_of_isArithmeticArtinLift _ hχ'
      hσ h1, zero_add, invariant_characterCup_restrictCharacter_of_isArithmeticArtinLift E hE ψ hσ,
    hψσ]

variable (K Ksep) in
/-- **The cup symbol.** For a character `χ : Gal(Ksep/K) → ℚ/ℤ` with open kernel, `a ∈ Kˣ` and an
arithmetic Artin lift `σ` of `a`, the invariant of `δχ ∪ a` is `χ(σ)`. -/
theorem invariant_characterClass_cup (χ : Gal(Ksep/K) →* Multiplicative RationalModIntegers)
    (hχ : IsOpen (χ.ker : Set Gal(Ksep/K))) (a : Kˣ) (σ : Gal(Ksep/K))
    (hσ : IsArithmeticArtinLift K Ksep a σ) :
    invariant K Ksep (characterCup K Ksep χ hχ a) = (χ σ).toAdd := by
  by_cases ha : normalizedUnitOrder K (.ofMul a) = 0
  · set π := localUniformizer K
    have hπ : normalizedUnitOrder K (.ofMul π) = 1 := normalizedUnitOrder_localUniformizer K
    obtain ⟨τ, hτ⟩ := exists_isArithmeticArtinLift K Ksep π
    have haπ : normalizedUnitOrder K (.ofMul (a * π)) ≠ 0 := by
      rw [ofMul_mul, map_add, ha, hπ]
      exact one_ne_zero
    have h1 := invariant_characterClass_cup_of_ne_zero χ hχ haπ (hσ.mul hτ)
    have h2 := invariant_characterClass_cup_of_ne_zero χ hχ (by rw [hπ]; exact one_ne_zero) hτ
    rw [characterCup_mul_right, map_add, h2, map_mul, toAdd_mul] at h1
    exact add_right_cancel h1
  · exact invariant_characterClass_cup_of_ne_zero χ hχ ha hσ

end CupSymbol

end Langlands.GaloisCohomology.Local
