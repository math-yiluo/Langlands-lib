# The cup product of a character with a unit

`Langlands/GaloisCohomology/Local/CharacterCup.lean`, namespace `Langlands.GaloisCohomology.Local`.

Let `L / K` be a Galois extension (in the applications `L` a separable closure of a local field),
`G = Gal(L/K)` with its Krull topology, `χ : G → ℚ/ℤ` a character with open kernel (a homomorphism
`G →* Multiplicative RationalModIntegers`) and `a ∈ Kˣ`. The class `δχ ∈ H²(G, ℤ)` is the image of
`χ ∈ H¹(G, ℚ/ℤ)` under the connecting map of `0 → ℤ → ℚ → ℚ/ℤ → 0`, and `a` is a class of
`H⁰(G, Lˣ)`; their cup product is `characterCup K L χ hχ a ∈ H²(G, Lˣ)`, in the cochain model of
`Langlands.ProfiniteCohomology` with the coefficients `IntegerScalars` of the units module
`unitsModule K L`, where the local invariant `invariant K Ksep` is defined. It is the class of the
standard cocycle

  `(g, h) ↦ c_χ(g, h) • a`,   `c_χ(g, h) = ⌊r(χ g) + r(χ h)⌋ = r(χ g) + r(χ h) − r(χ (gh))`,

with `r : ℚ/ℤ → [0, 1)` the representative (the foundations' `GroupCoh.reprIco`, `charCocycle`):
`c_χ` is the coboundary of the lift `g ↦ r(χ g)` of `χ` to `ℚ`, i.e. a cocycle of `δχ`, and the cup
product of a 2-cocycle with an invariant element `a` of degree 0 is the cocycle times `a`. The same
cocycle represents the foundations' cup product `cupCharClassProf (unitsModuleZ K L) χ a` over `ℤ`
(`exists_cocycle_cupCharClassProf`), the class `galCupClass` of `Field/CyclicCup.lean`.

- **Bilinearity** (`characterCup_mul_left`, `characterCup_mul_right`): `δ(χ₁χ₂) ∪ a = δχ₁ ∪ a + δχ₂ ∪ a`
  and `δχ ∪ ab = δχ ∪ a + δχ ∪ b`; `δ1 ∪ a = 0`, `δ(χⁿ) ∪ a = n • (δχ ∪ a)`.
- **Comparison with the cup product over `ℤ`** (`characterCup_eq_zero_iff_galCupClass_eq_zero`):
  `characterCup K L χ hχ a = 0` exactly when the foundations' `galCupClass K L χ a = 0`.
- **Norms** (`characterCup_eq_zero_of_exists_norm`): if `a` is a norm from the fixed field `L_χ` of
  `ker χ`, then `δχ ∪ a = 0`.

## Declarations

```lean
-- G : Type u, [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
def characterToQZ (χ : G →* Multiplicative RationalModIntegers) (hχ : IsOpen (χ.ker : Set G)) :
    Additive G →ₜ+ QZ
theorem characterToQZ_apply (χ) (hχ) (g : G) :
    characterToQZ χ hχ (Additive.ofMul g) = QZ.toRationalModIntegers.symm (χ g).toAdd
theorem charAdd_characterToQZ (χ) (hχ) (g : G) :
    charAdd (characterToQZ χ hχ) (Additive.ofMul g) = ((χ g).toAdd : AddCircle (1 : ℚ))
theorem charKer_charAdd_characterToQZ (χ) (hχ) : charKer (charAdd (characterToQZ χ hχ)) = χ.ker
theorem isOpen_ker_mul {χ₁ χ₂ : G →* Multiplicative RationalModIntegers}
    (h₁ : IsOpen (χ₁.ker : Set G)) (h₂ : IsOpen (χ₂.ker : Set G)) :
    IsOpen ((χ₁ * χ₂).ker : Set G)
theorem floor_reprIco_add (u v : AddCircle (1 : ℚ)) :
    (⌊reprIco u + reprIco v⌋ : ℚ) = reprIco u + reprIco v - reprIco (u + v)

-- K L : Type u, [Field K] [Field L] [Algebra K L]
def characterCupCocycles₂ (χ : Additive Gal(L/K) →ₜ+ QZ) (a : Kˣ) :
    groupCohomology.cocycles₂ (unitsRepresentation K L)      -- (g, h) ↦ c_χ(g, h) • a
theorem isLocallyConstant_characterCupCocycles₂ (χ) (a) :
    IsLocallyConstant fun v : Fin 2 → Gal(L/K) => characterCupCocycles₂ K L χ a (v 0, v 1)
-- [IsGalois K L]
def characterCupCocycle (χ : Additive Gal(L/K) →ₜ+ QZ) (a : Kˣ) : cocycles (unitsModule K L) 2
theorem cochainOf_cocycleι_characterCupCocycle (χ) (a) (v : Fin 2 → Gal(L/K)) :
    cochainOf (unitsModule K L) (cocycleι (unitsModule K L) 2 (characterCupCocycle K L χ a)) v =
      charCocycle (charAdd χ) (v 0, v 1) • baseUnit K L a
def characterCup (χ : Gal(L/K) →* Multiplicative RationalModIntegers)
    (hχ : IsOpen (χ.ker : Set Gal(L/K))) (a : Kˣ) : cohomology (unitsModule K L) 2 :=
  cohomologyπ (unitsModule K L) 2 (characterCupCocycle K L (characterToQZ χ hχ) a)
theorem cochainOf_cocycleι_characterCup (χ) (hχ) (a : Kˣ) (g h : Gal(L/K)) :
    cochainOf (unitsModule K L)
        (cocycleι (unitsModule K L) 2 (characterCupCocycle K L (characterToQZ χ hχ) a)) ![g, h] =
      charCocycle (charAdd (characterToQZ χ hχ)) (g, h) • baseUnit K L a
theorem characterCup_congr {χ₁ χ₂} (h : χ₁ = χ₂) (h₁) (h₂) (a : Kˣ) :
    characterCup K L χ₁ h₁ a = characterCup K L χ₂ h₂ a
theorem characterCup_mul_right (χ) (hχ) (a b : Kˣ) :
    characterCup K L χ hχ (a * b) = characterCup K L χ hχ a + characterCup K L χ hχ b
theorem characterCup_one_left (h1 : IsOpen ((1 : Gal(L/K) →* Multiplicative RationalModIntegers).ker :
    Set Gal(L/K))) (a : Kˣ) : characterCup K L 1 h1 a = 0
theorem characterCup_mul_left (χ₁ χ₂ : Gal(L/K) →* Multiplicative RationalModIntegers)
    (h₁ : IsOpen (χ₁.ker : Set Gal(L/K))) (h₂ : IsOpen (χ₂.ker : Set Gal(L/K)))
    (h₁₂ : IsOpen ((χ₁ * χ₂).ker : Set Gal(L/K))) (a : Kˣ) :
    characterCup K L (χ₁ * χ₂) h₁₂ a = characterCup K L χ₁ h₁ a + characterCup K L χ₂ h₂ a
theorem characterCup_pow_left (χ) (hχ) (n : ℕ) (hn : IsOpen ((χ ^ n).ker : Set Gal(L/K)))
    (a : Kˣ) : characterCup K L (χ ^ n) hn a = n • characterCup K L χ hχ a
theorem characterCup_eq_zero_iff_galCupClass_eq_zero (χ) (hχ) (a : Kˣ) :   -- K L : Type
    characterCup K L χ hχ a = 0 ↔ galCupClass K L (characterToQZ χ hχ) a = 0
theorem characterCup_eq_zero_of_exists_norm (χ) (hχ) (a : Kˣ)
    (h : ∃ y : IntermediateField.fixedField χ.ker, Algebra.norm K y = (a : K)) :
    characterCup K L χ hχ a = 0
```

Universes: every declaration is for groups and fields in any universe `u` (`K L : Type u`), except
`characterCup_eq_zero_iff_galCupClass_eq_zero` (`K L : Type`): its statement is about the
foundations' `galCupClass`, a class in the cohomology over `ℤ`, which exists for groups in universe
`0` only.

## Proofs

- The cocycle identity of `c_χ` is the foundations' `GroupCoh.charCocycle_cocycle` (checked in `ℚ`
  from `r(χ g) + r(χ h) − r(χ(gh))`); the unit `a` is
  fixed by `G` (`baseUnit_fixed`), so `(g, h) ↦ c_χ(g, h) • a` is a Mathlib 2-cocycle; it is locally
  constant since `χ` is, and `cocyclesOfCocycles₂` makes it a cocycle of the cochain model.
- Additivity in `a` holds on cocycles. Additivity in `χ`: with `f(g) = ⌊r(χ₁ g) + r(χ₂ g)⌋`
  (`floor_reprIco_add`: `f = r∘χ₁ + r∘χ₂ − r∘(χ₁χ₂)`), the difference of the cocycles is
  `(g, h) ↦ (f(gh) − f(g) − f(h)) • a`, the coboundary of the locally constant cochain `g ↦ −f(g) • a`
  (`cohomologyπ_two_eq_zero_iff`).
- Norms: the standard cocycle of `δχ ∪ a` is the coboundary of a locally constant function exactly
  when `a` is a norm from the fixed field of `ker χ` (the norm criterion on cocycles of the field
  layer, `exists_coboundary_charCocycle_smul_iff_exists_norm`).
- Comparison: the foundations' `galCupClass K L χ a` has the same cocycle; a coboundary for one
  cocycle is a coboundary for the other, as the units modules over `ℤ` and over `IntegerScalars`
  have the same underlying group and action.

## Source and licence

New file. The construction follows Serre's definition of the symbol `(χ, b) = b · δχ`; the cyclic
cup products of the foundations (`Cohomology/Profinite/Cyclic/`, `Field/CyclicCup.lean`) are those
of the repository `leanprover-community/riemann-hypothesis`, commit `f1f6d65` (see their pages).

## References

- J.-P. Serre, *Local Fields*, chapter XIV, §1: definition of `(χ, b) = b · δχ ∈ Br(K)`,
  Proposition 1 (bilinearity), Proposition 2 and its Corollary 1 (`(χ, b) = 0` exactly when `b` is a
  norm from `L_χ`), p. 204.
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition, chapter I,
  §4, Proposition (1.4.8) (explicit inhomogeneous cochains of cup products; in degree `0` the cup
  product is the tensor product of the representatives), p. 44.
