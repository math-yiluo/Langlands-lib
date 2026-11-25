import Langlands.Cohomology.Profinite.Comparison.TwoCocycles
import Langlands.Cohomology.Profinite.Dimension.Procyclic
import Langlands.GaloisCohomology.Local.Duality.KummerCup

/-!
# The cup product of a character with a unit

For a Galois extension `L / K`, a character `χ : Gal(L/K) → ℚ/ℤ` with open kernel and `a ∈ Kˣ`,
`characterCup K L χ hχ a ∈ H²(Gal(L/K), Lˣ)` is the cup product `δχ ∪ a` of the class
`δχ ∈ H²(Gal(L/K), ℤ)` (`δ` the connecting map of `0 → ℤ → ℚ → ℚ/ℤ → 0`) with
`a ∈ H⁰(Gal(L/K), Lˣ)`, in the cochain model of `Langlands.ProfiniteCohomology` with the
coefficients `IntegerScalars` of the units module `unitsModule K L` (where the local invariant
lives). It is the class of the standard cocycle

  `(g, h) ↦ c_χ(g, h) • a`,  `c_χ(g, h) = ⌊r(χ g) + r(χ h)⌋ = r(χ g) + r(χ h) − r(χ (g h))`,

`r : ℚ/ℤ → [0, 1)` the representative (`GroupCoh.charCocycle`), which is the cocycle of `δχ ∪ a`
(`exists_cocycle_cupCharClassProf` computes the same cocycle for the foundations' cup product
`cupCharClassProf` over `ℤ`).

## Main declarations

* `characterToQZ χ hχ`: `χ` as a continuous additive character with values in `QZ`.
* `characterCup K L χ hχ a` with its cocycle `cochainOf_cocycleι_characterCupCocycle`.
* `characterCup_mul_left` (additive in the character), `characterCup_mul_right` (additive in the
  unit), `characterCup_one_left`, `characterCup_pow_left`.
* `characterCup_eq_zero_of_exists_norm`: `δχ ∪ a = 0` when `a` is a norm from the fixed field of
  `ker χ` (from the norm criterion on cocycles of the field layer,
  `exists_coboundary_charCocycle_smul_iff_exists_norm`).
-/

noncomputable section

namespace Langlands.GaloisCohomology.Local

universe u

open CategoryTheory Langlands.ProfiniteCohomology GroupCoh ClassFieldTheory.Local IntermediateField


section Character

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A character `G → ℚ/ℤ` with open kernel, as a continuous additive character with values in the
discrete group `QZ`. -/
def characterToQZ (χ : G →* Multiplicative RationalModIntegers) (hχ : IsOpen (χ.ker : Set G)) :
    Additive G →ₜ+ QZ where
  toFun x := QZ.toRationalModIntegers.symm (χ x.toMul).toAdd
  map_zero' := by simp
  map_add' x y := by simp
  continuous_toFun := by
    have h := Langlands.MonoidHom.isLocallyConstant_of_isOpen_ker χ hχ
    exact ((h.comp fun z => QZ.toRationalModIntegers.symm z.toAdd).comp_continuous
      continuous_toMul).continuous

@[simp]
theorem characterToQZ_apply (χ : G →* Multiplicative RationalModIntegers)
    (hχ : IsOpen (χ.ker : Set G)) (g : G) :
    characterToQZ χ hχ (Additive.ofMul g) = QZ.toRationalModIntegers.symm (χ g).toAdd :=
  rfl

theorem charAdd_characterToQZ (χ : G →* Multiplicative RationalModIntegers)
    (hχ : IsOpen (χ.ker : Set G)) (g : G) :
    charAdd (characterToQZ χ hχ) (Additive.ofMul g) = ((χ g).toAdd : AddCircle (1 : ℚ)) :=
  rfl

theorem charKer_charAdd_characterToQZ (χ : G →* Multiplicative RationalModIntegers)
    (hχ : IsOpen (χ.ker : Set G)) : charKer (charAdd (characterToQZ χ hχ)) = χ.ker := by
  ext g
  rw [mem_charKer, charAdd_characterToQZ, MonoidHom.mem_ker]
  exact toAdd_eq_zero

/-- The kernel of a product of characters with open kernels is open. -/
theorem isOpen_ker_mul {χ₁ χ₂ : G →* Multiplicative RationalModIntegers}
    (h₁ : IsOpen (χ₁.ker : Set G)) (h₂ : IsOpen (χ₂.ker : Set G)) :
    IsOpen ((χ₁ * χ₂).ker : Set G) := by
  refine Subgroup.isOpen_mono (H₁ := χ₁.ker ⊓ χ₂.ker) (fun g hg => ?_) (h₁.inter h₂)
  rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hg
  rw [MonoidHom.mem_ker, MonoidHom.mul_apply, hg.1, hg.2, one_mul]

/-- For `u, v ∈ ℚ/ℤ` with representatives `r(u), r(v) ∈ [0, 1)`, the carry `⌊r(u) + r(v)⌋` is
`r(u) + r(v) − r(u + v)`. -/
theorem floor_reprIco_add (u v : AddCircle (1 : ℚ)) :
    (⌊reprIco u + reprIco v⌋ : ℚ) = reprIco u + reprIco v - reprIco (u + v) := by
  have h1 := reprIco_mem u
  have h2 := reprIco_mem v
  have h3 := reprIco_mem (u + v)
  have hc : ((reprIco u + reprIco v - reprIco (u + v) : ℚ) : AddCircle (1 : ℚ)) = 0 := by
    rw [AddCircle.coe_sub, AddCircle.coe_add, coe_reprIco, coe_reprIco, coe_reprIco, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).1 hc
  rw [zsmul_one] at hn
  have hfl : ⌊reprIco u + reprIco v⌋ = n := by
    rw [Int.floor_eq_iff]
    simp only [Set.mem_Ico] at h1 h2 h3
    constructor <;> linarith
  rw [hfl, hn]

end Character

section Cocycle

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

/-- The Mathlib 2-cocycle `(g, h) ↦ c_χ(g, h) • a` of `Gal(L/K)` with values in `Lˣ`. -/
def characterCupCocycles₂ (χ : Additive Gal(L/K) →ₜ+ QZ) (a : Kˣ) :
    groupCohomology.cocycles₂ (unitsRepresentation K L) :=
  ⟨fun p => charCocycle (charAdd χ) p • baseUnit K L a, by
    apply (groupCohomology.mem_cocycles₂_iff _).2
    intro g h j
    change charCocycle (charAdd χ) (g * h, j) • baseUnit K L a +
        charCocycle (charAdd χ) (g, h) • baseUnit K L a =
      (unitsRepresentation K L).ρ g (charCocycle (charAdd χ) (h, j) • baseUnit K L a) +
        charCocycle (charAdd χ) (g, h * j) • baseUnit K L a
    rw [map_zsmul, baseUnit_fixed, ← add_smul, ← add_smul, charCocycle_cocycle]⟩

variable [IsGalois K L]

omit [IsGalois K L] in
theorem isLocallyConstant_characterCupCocycles₂ (χ : Additive Gal(L/K) →ₜ+ QZ) (a : Kˣ) :
    IsLocallyConstant fun v : Fin 2 → Gal(L/K) => characterCupCocycles₂ K L χ a (v 0, v 1) := by
  have h0 := (isLocallyConstant_charAdd χ).comp_continuous
    (f := fun v : Fin 2 → Gal(L/K) => v 0) (continuous_apply 0)
  have h1 := (isLocallyConstant_charAdd χ).comp_continuous
    (f := fun v : Fin 2 → Gal(L/K) => v 1) (continuous_apply 1)
  exact IsLocallyConstant.comp₂ h0 h1 fun x y =>
    (⌊reprIco x + reprIco y⌋ • baseUnit K L a : unitsModule K L)

/-- The standard cocycle of `δχ ∪ a` in the cochain model. -/
def characterCupCocycle (χ : Additive Gal(L/K) →ₜ+ QZ) (a : Kˣ) : cocycles (unitsModule K L) 2 :=
  cocyclesOfCocycles₂ (unitsModule K L) (characterCupCocycles₂ K L χ a)
    (isLocallyConstant_characterCupCocycles₂ K L χ a)

theorem cochainOf_cocycleι_characterCupCocycle (χ : Additive Gal(L/K) →ₜ+ QZ) (a : Kˣ)
    (v : Fin 2 → Gal(L/K)) :
    cochainOf (unitsModule K L) (cocycleι (unitsModule K L) 2 (characterCupCocycle K L χ a)) v =
      charCocycle (charAdd χ) (v 0, v 1) • baseUnit K L a :=
  congrFun (cochainOf_cocycleι_cocyclesOfCocycles₂ (unitsModule K L) _ _) v

/-- The cup product `δχ ∪ a ∈ H²(Gal(L/K), Lˣ)` of a character `χ` with open kernel and a unit
`a ∈ Kˣ`, as the class of its standard cocycle `(g, h) ↦ c_χ(g, h) • a`. -/
def characterCup (χ : Gal(L/K) →* Multiplicative RationalModIntegers)
    (hχ : IsOpen (χ.ker : Set Gal(L/K))) (a : Kˣ) : cohomology (unitsModule K L) 2 :=
  cohomologyπ (unitsModule K L) 2 (characterCupCocycle K L (characterToQZ χ hχ) a)

end Cocycle

section Algebra

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [IsGalois K L]

theorem cochainOf_cocycleι_characterCup (χ : Gal(L/K) →* Multiplicative RationalModIntegers)
    (hχ : IsOpen (χ.ker : Set Gal(L/K))) (a : Kˣ) (g h : Gal(L/K)) :
    cochainOf (unitsModule K L)
        (cocycleι (unitsModule K L) 2 (characterCupCocycle K L (characterToQZ χ hχ) a)) ![g, h] =
      charCocycle (charAdd (characterToQZ χ hχ)) (g, h) • baseUnit K L a :=
  cochainOf_cocycleι_characterCupCocycle K L _ a ![g, h]

/-- `characterCup` depends only on the character (the openness proof is irrelevant). -/
theorem characterCup_congr {χ₁ χ₂ : Gal(L/K) →* Multiplicative RationalModIntegers} (h : χ₁ = χ₂)
    (h₁ : IsOpen (χ₁.ker : Set Gal(L/K))) (h₂ : IsOpen (χ₂.ker : Set Gal(L/K))) (a : Kˣ) :
    characterCup K L χ₁ h₁ a = characterCup K L χ₂ h₂ a := by
  subst h
  rfl

/-- The cup product is additive in the unit. -/
theorem characterCup_mul_right (χ : Gal(L/K) →* Multiplicative RationalModIntegers)
    (hχ : IsOpen (χ.ker : Set Gal(L/K))) (a b : Kˣ) :
    characterCup K L χ hχ (a * b) = characterCup K L χ hχ a + characterCup K L χ hχ b := by
  rw [characterCup, characterCup, characterCup, ← map_add]
  congr 1
  apply cocycleι_injective
  apply cochainOf_injective
  rw [map_add, cochainOf_add]
  funext v
  rw [Pi.add_apply, cochainOf_cocycleι_characterCupCocycle, cochainOf_cocycleι_characterCupCocycle,
    cochainOf_cocycleι_characterCupCocycle, ← smul_add]
  congr 1
  simp only [baseUnit, map_mul]
  rfl

/-- The cup product with the trivial character vanishes. -/
theorem characterCup_one_left (h1 : IsOpen ((1 : Gal(L/K) →* Multiplicative RationalModIntegers).ker :
    Set Gal(L/K))) (a : Kˣ) : characterCup K L 1 h1 a = 0 := by
  rw [characterCup, ← map_zero (cohomologyπ (unitsModule K L) 2).hom]
  congr 1
  apply cocycleι_injective
  apply cochainOf_injective
  funext v
  rw [cochainOf_cocycleι_characterCupCocycle, map_zero, cochainOf_zero, Pi.zero_apply]
  have h : charCocycle (charAdd (characterToQZ (1 : Gal(L/K) →* Multiplicative RationalModIntegers)
      h1)) (v 0, v 1) = 0 := by
    apply Int.cast_injective (α := ℚ)
    rw [charCocycle_cast]
    simp only [charAdd_characterToQZ, MonoidHom.one_apply, toAdd_one, Int.cast_zero]
    have h0 : reprIco (0 : AddCircle (1 : ℚ)) = 0 := by
      have := reprIco_coe (q := (0 : ℚ)) (by simp)
      simpa using this
    change reprIco (0 : AddCircle (1 : ℚ)) + reprIco 0 - reprIco 0 = 0
    rw [h0]
    ring
  rw [h, zero_smul]

/-- The cup product is additive in the character. -/
theorem characterCup_mul_left (χ₁ χ₂ : Gal(L/K) →* Multiplicative RationalModIntegers)
    (h₁ : IsOpen (χ₁.ker : Set Gal(L/K))) (h₂ : IsOpen (χ₂.ker : Set Gal(L/K)))
    (h₁₂ : IsOpen ((χ₁ * χ₂).ker : Set Gal(L/K))) (a : Kˣ) :
    characterCup K L (χ₁ * χ₂) h₁₂ a = characterCup K L χ₁ h₁ a + characterCup K L χ₂ h₂ a := by
  rw [← sub_eq_zero, sub_add_eq_sub_sub, characterCup, characterCup, characterCup, ← map_sub,
    ← map_sub, cohomologyπ_two_eq_zero_iff]
  set ψ₁ := characterToQZ χ₁ h₁
  set ψ₂ := characterToQZ χ₂ h₂
  set ψ₁₂ := characterToQZ (χ₁ * χ₂) h₁₂
  let fl : Gal(L/K) → ℤ := fun g =>
    ⌊reprIco (charAdd ψ₁ (Additive.ofMul g)) + reprIco (charAdd ψ₂ (Additive.ofMul g))⌋
  have hadd (g : Gal(L/K)) :
      charAdd ψ₁₂ (Additive.ofMul g) = charAdd ψ₁ (Additive.ofMul g) + charAdd ψ₂ (Additive.ofMul g) :=
    rfl
  have hfl (g : Gal(L/K)) : (fl g : ℚ) = reprIco (charAdd ψ₁ (Additive.ofMul g)) +
      reprIco (charAdd ψ₂ (Additive.ofMul g)) - reprIco (charAdd ψ₁₂ (Additive.ofMul g)) := by
    rw [hadd]
    exact floor_reprIco_add _ _
  have hlc : IsLocallyConstant fl :=
    IsLocallyConstant.comp₂ (isLocallyConstant_charAdd ψ₁) (isLocallyConstant_charAdd ψ₂)
      fun u v => ⌊reprIco u + reprIco v⌋
  refine ⟨fun g => (-fl g) • baseUnit K L a, hlc.comp fun n => (-n) • baseUnit K L a,
    fun g h => ?_⟩
  have e : cochainOf (unitsModule K L) (cocycleι (unitsModule K L) 2
      (characterCupCocycle K L ψ₁₂ a - characterCupCocycle K L ψ₁ a -
        characterCupCocycle K L ψ₂ a)) ![g, h] =
      (charCocycle (charAdd ψ₁₂) (g, h) - charCocycle (charAdd ψ₁) (g, h) -
        charCocycle (charAdd ψ₂) (g, h)) • baseUnit K L a := by
    rw [map_sub, map_sub, sub_smul, sub_smul, ← cochainOf_cocycleι_characterCup,
      ← cochainOf_cocycleι_characterCup, ← cochainOf_cocycleι_characterCup]
    rfl
  rw [e, map_zsmul, baseUnit_fixed, ← sub_smul, ← add_smul]
  congr 1
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [charCocycle_cast, charCocycle_cast, charCocycle_cast, hfl, hfl, hfl, ofMul_mul]
  ring

/-- The cup product with a power of a character is the multiple of the cup product. -/
theorem characterCup_pow_left (χ : Gal(L/K) →* Multiplicative RationalModIntegers)
    (hχ : IsOpen (χ.ker : Set Gal(L/K))) (n : ℕ) (hn : IsOpen ((χ ^ n).ker : Set Gal(L/K)))
    (a : Kˣ) : characterCup K L (χ ^ n) hn a = n • characterCup K L χ hχ a := by
  induction n with
  | zero =>
    rw [zero_smul]
    have e : χ ^ 0 = 1 := pow_zero χ
    have h1 : IsOpen ((1 : Gal(L/K) →* Multiplicative RationalModIntegers).ker : Set Gal(L/K)) :=
      e ▸ hn
    rw [← characterCup_one_left K L h1 a]
    congr 1
  | succ n ih =>
    have hn' : IsOpen ((χ ^ n).ker : Set Gal(L/K)) := by
      refine Subgroup.isOpen_mono (H₁ := χ.ker) (fun g hg => ?_) hχ
      rw [MonoidHom.mem_ker] at hg ⊢
      rw [MonoidHom.pow_apply, hg, one_pow]
    have e : χ ^ (n + 1) = χ ^ n * χ := pow_succ χ n
    have h := characterCup_mul_left K L (χ ^ n) χ hn' hχ (e ▸ hn) a
    rw [succ_nsmul, ← ih hn', ← h]
    congr 1

end Algebra

section NormInt

variable {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L]

/-- `characterCup` vanishes exactly when the foundations' cup product `galCupClass` over `ℤ` of the
same character and unit vanishes: the two classes have the same standard cocycle, in the units
modules over `IntegerScalars` and over `ℤ`, which have the same underlying group and action. -/
theorem characterCup_eq_zero_iff_galCupClass_eq_zero
    (χ : Gal(L/K) →* Multiplicative RationalModIntegers) (hχ : IsOpen (χ.ker : Set Gal(L/K)))
    (a : Kˣ) : characterCup K L χ hχ a = 0 ↔ galCupClass K L (characterToQZ χ hχ) a = 0 := by
  obtain ⟨w, hw, hwc⟩ := exists_cocycle_cupCharClassProf (unitsModuleZ K L) (characterToQZ χ hχ)
    (unitsInvariant K L a)
  rw [galCupClass, ← hw, cohomologyπ_two_eq_zero_iff, characterCup, cohomologyπ_two_eq_zero_iff]
  constructor
  · rintro ⟨f, hf, hfz⟩
    refine ⟨f, hf, fun g h => ?_⟩
    have e := hfz g h
    rw [cochainOf_cocycleι_characterCup] at e
    rw [hwc]
    exact e
  · rintro ⟨f, hf, hfz⟩
    refine ⟨f, hf, fun g h => ?_⟩
    have e := hfz g h
    rw [hwc] at e
    rw [cochainOf_cocycleι_characterCup]
    exact e

end NormInt

section Norm

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]

/-- `δχ ∪ a = 0` when `a` is a norm from the fixed field of the kernel of `χ`: the standard cocycle
is then a coboundary, by the norm criterion on cocycles of the field layer
(`exists_coboundary_charCocycle_smul_iff_exists_norm`). -/
theorem characterCup_eq_zero_of_exists_norm (χ : Gal(L/K) →* Multiplicative RationalModIntegers)
    (hχ : IsOpen (χ.ker : Set Gal(L/K))) (a : Kˣ)
    (h : ∃ y : fixedField χ.ker, Algebra.norm K y = (a : K)) : characterCup K L χ hχ a = 0 := by
  rw [characterCup, cohomologyπ_two_eq_zero_iff]
  have h' : ∃ y : fixedField (charKer (charAdd (characterToQZ χ hχ))), Algebra.norm K y = (a : K) := by
    rw [charKer_charAdd_characterToQZ]
    exact h
  obtain ⟨f, hf, hfz⟩ :=
    (exists_coboundary_charCocycle_smul_iff_exists_norm (characterToQZ χ hχ) a).2 h'
  refine ⟨f, hf, fun g h => ?_⟩
  rw [cochainOf_cocycleι_characterCup]
  exact hfz g h

end Norm

end Langlands.GaloisCohomology.Local
