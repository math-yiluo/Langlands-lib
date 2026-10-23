import Langlands.ClassFieldTheory.Local.UnramifiedInvariantCompatibilityStatement
import Langlands.ClassFieldTheory.Local.CyclicClassNormProof
import Langlands.LocalField.Normalization.Proof

/-! # Inflation compatibility of the explicit finite unramified invariant -/

noncomputable section

open IsLocalRing CategoryTheory

namespace Langlands.ClassFieldTheory.Local

universe u

namespace UnramifiedInflation

/-! ## Arithmetic Frobenius in a tower -/

section Residue

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

local instance : NontriviallyNormedField F.Carrier := F.canonicalNormedField
local instance : NormedAlgebra (Padic p) F.Carrier := F.canonicalNormedAlgebra
local instance : IsUltrametricDist F.Carrier :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (isNonarchimedean_spectralNorm (K := Padic p) (L := F.Carrier))
local instance : ProperSpace F.Carrier := FiniteDimensional.proper (Padic p) F.Carrier

variable (L M : Type u) [Field L] [Field M] [Algebra F.Carrier L] [Algebra F.Carrier M]
  [Algebra L M] [IsScalarTower F.Carrier L M] [Algebra.IsAlgebraic F.Carrier M]

section Algebraic

variable [Algebra.IsAlgebraic F.Carrier L]

/-- The field inclusion restricted to the spectral-norm integer rings. -/
def towerIntegerMap :
    LocalGalois.extensionIntegers F.Carrier L →+*
      LocalGalois.extensionIntegers F.Carrier M where
  toFun x := ⟨algebraMap L M (x : L), by
    have hx : spectralNorm F.Carrier L (x : L) ≤ 1 := x.2
    change spectralNorm F.Carrier M (algebraMap L M (x : L)) ≤ 1
    rwa [← spectralNorm.eq_of_tower]⟩
  map_one' := Subtype.ext (map_one (algebraMap L M))
  map_mul' x y := Subtype.ext (map_mul (algebraMap L M) (x : L) (y : L))
  map_zero' := Subtype.ext (map_zero (algebraMap L M))
  map_add' x y := Subtype.ext (map_add (algebraMap L M) (x : L) (y : L))

/-- Spectral norms are unchanged in the tower, so nonunits stay nonunits. -/
instance towerIntegerMap_isLocalHom : IsLocalHom (towerIntegerMap F L M) := by
  refine ⟨fun x hx => ?_⟩
  by_contra h
  have hm : x ∈ maximalIdeal (LocalGalois.extensionIntegers F.Carrier L) :=
    (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr h)
  have hm' : towerIntegerMap F L M x ∈
      maximalIdeal (LocalGalois.extensionIntegers F.Carrier M) := by
    rw [Valuation.mem_maximalIdeal_iff] at hm ⊢
    have h' : spectralNorm F.Carrier L (x : L) < 1 := hm
    change spectralNorm F.Carrier M (algebraMap L M (x : L)) < 1
    rwa [← spectralNorm.eq_of_tower]
  exact mem_nonunits_iff.mp ((mem_maximalIdeal _).mp hm') hx

/-- The residue-field inclusion induced by the tower. -/
abbrev towerResidueMap :
    ResidueField (LocalGalois.extensionIntegers F.Carrier L) →+*
      ResidueField (LocalGalois.extensionIntegers F.Carrier M) :=
  ResidueField.map (towerIntegerMap F L M)

end Algebraic

variable [Normal F.Carrier L]

/-- Residue actions commute with normal restriction along the tower. -/
theorem towerResidueMap_residueHom (σ : Gal(M/F.Carrier))
    (y : ResidueField (LocalGalois.extensionIntegers F.Carrier L)) :
    towerResidueMap F L M (LocalGalois.residueHom F.Carrier L (σ.restrictNormal L) y) =
      LocalGalois.residueHom F.Carrier M σ (towerResidueMap F L M y) := by
  obtain ⟨x, rfl⟩ := residue_surjective y
  change residue _ (towerIntegerMap F L M
      (LocalGalois.integerAut F.Carrier L (σ.restrictNormal L) x)) =
    residue _ (LocalGalois.integerAut F.Carrier M σ (towerIntegerMap F L M x))
  congr 1
  apply Subtype.ext
  exact σ.restrictNormal_commutes L (x : L)

/-- An arithmetic Frobenius of `M` restricts to the arithmetic Frobenius of `L`. -/
theorem restrictNormal_frobenius {σM : Gal(M/F.Carrier)} {σL : Gal(L/F.Carrier)}
    (hinj : Function.Injective (LocalGalois.residueHom F.Carrier L))
    (hL : ∀ y : ResidueField (LocalGalois.extensionIntegers F.Carrier L),
      LocalGalois.residueHom F.Carrier L σL y =
        y ^ Nat.card (ResidueField (LocalGalois.baseIntegers F.Carrier)))
    (hM : ∀ z : ResidueField (LocalGalois.extensionIntegers F.Carrier M),
      LocalGalois.residueHom F.Carrier M σM z =
        z ^ Nat.card (ResidueField (LocalGalois.baseIntegers F.Carrier))) :
    σM.restrictNormal L = σL := by
  apply hinj
  ext y
  apply (towerResidueMap F L M).injective
  rw [towerResidueMap_residueHom, hM, hL, map_pow]

end Residue

/-! ## Compatible cyclic coordinates -/

section Coordinates

variable (K L M : Type u) [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
  [Algebra L M] [IsScalarTower K L M] [Normal K L]

/-- If the positive generators correspond, the coordinates correspond by reduction. -/
theorem coordinate_restrict {n m : ℕ} (hdvd : n ∣ m)
    (χL : Gal(L/K) ≃* Multiplicative (ZMod n)) (χM : Gal(M/K) ≃* Multiplicative (ZMod m))
    (hσ : (cyclicCoordinateGenerator χM).restrictNormal L = cyclicCoordinateGenerator χL)
    (g : Gal(M/K)) :
    (χL (g.restrictNormal L)).toAdd = ZMod.castHom hdvd (ZMod n) (χM g).toAdd := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (cyclicCoordinateGenerator_generates χM g)
  have h1 : (cyclicCoordinateGenerator χM ^ k).restrictNormal L =
      cyclicCoordinateGenerator χL ^ k := by
    change AlgEquiv.restrictNormalHom L (cyclicCoordinateGenerator χM ^ k) = _
    rw [map_zpow]
    exact congrArg (· ^ k) hσ
  have e1 : χL (cyclicCoordinateGenerator χL ^ k) = Multiplicative.ofAdd (k : ZMod n) := by
    rw [map_zpow, cyclicCoordinateGenerator, MulEquiv.apply_symm_apply, ← ofAdd_zsmul,
      zsmul_one]
  have e2 : χM (cyclicCoordinateGenerator χM ^ k) = Multiplicative.ofAdd (k : ZMod m) := by
    rw [map_zpow, cyclicCoordinateGenerator, MulEquiv.apply_symm_apply, ← ofAdd_zsmul,
      zsmul_one]
  rw [h1, e1, e2, toAdd_ofAdd, toAdd_ofAdd, map_intCast]

/-- The same correspondence on standard representatives. -/
theorem coordinate_restrict_val {n m : ℕ} [NeZero m] (hdvd : n ∣ m)
    (χL : Gal(L/K) ≃* Multiplicative (ZMod n)) (χM : Gal(M/K) ≃* Multiplicative (ZMod m))
    (hσ : (cyclicCoordinateGenerator χM).restrictNormal L = cyclicCoordinateGenerator χL)
    (g : Gal(M/K)) :
    (χL (g.restrictNormal L)).toAdd.val = (χM g).toAdd.val % n := by
  rw [coordinate_restrict K L M hdvd χL χM hσ g, ZMod.castHom_apply, ZMod.cast_eq_val,
    ZMod.val_natCast]

end Coordinates

/-! ## Inflation of carry classes -/

section Cocycle

/-- Carries modulo `n` and modulo `m = n * k` differ by the coboundary of `i ↦ ⌊i / n⌋`. -/
theorem carry_identity {n m k i j : ℕ} (hn : 0 < n) (hm : m = n * k) :
    k * ((i + j) / m) + (i + j) % m / n = (i % n + j % n) / n + i / n + j / n := by
  apply Nat.eq_of_mul_eq_mul_left hn
  have h1 := Nat.div_add_mod (i + j) m
  have h2 := Nat.div_add_mod ((i + j) % m) n
  have h3 := Nat.div_add_mod (i % n + j % n) n
  have h4 := Nat.div_add_mod i n
  have h5 := Nat.div_add_mod j n
  have h6 : (i + j) % m % n = (i % n + j % n) % n := by
    rw [Nat.mod_mod_of_dvd _ (⟨k, hm⟩ : n ∣ m), Nat.add_mod]
  rw [mul_add, mul_add, mul_add, ← mul_assoc, ← hm]
  omega

variable (K L M : Type u) [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
  [Algebra L M] [IsScalarTower K L M] [Normal K L]

/-- The actual inflation coefficients send an included base unit to its inclusion. -/
theorem inflationCoefficients_baseUnit (a : Kˣ) :
    (inflationCoefficients K L M).hom (baseUnit K L a) = baseUnit K M a := by
  apply Units.ext
  exact (IsScalarTower.algebraMap_apply K L M (a : K)).symm

/-- Inflation of the carry class of `a` is the carry class of `a ^ k` for `m = n * k`. -/
theorem inflation_cyclicClass {n m k : ℕ} [NeZero n] [NeZero m] (hm : m = n * k)
    (χL : Gal(L/K) →* Multiplicative (ZMod n)) (χM : Gal(M/K) →* Multiplicative (ZMod m))
    (hχ : ∀ g : Gal(M/K), (χL (g.restrictNormal L)).toAdd.val = (χM g).toAdd.val % n)
    (a : Kˣ) :
    relativeInflation K L M 2 (cyclicClass K L χL a) = cyclicClass K M χM (a ^ k) := by
  rw [cyclicClass, cyclicClass, groupCohomology.H2π_comp_map_apply]
  symm
  rw [groupCohomology.H2π_eq_iff]
  refine ⟨fun g => ((χM g).toAdd.val / n) • baseUnit K M a, ?_⟩
  funext gh
  obtain ⟨g, h⟩ := gh
  have hid := carry_identity (i := (χM g).toAdd.val) (j := (χM h).toAdd.val)
    (NeZero.pos n) hm
  have hpow : baseUnit K M (a ^ k) = k • baseUnit K M a := by
    change Additive.ofMul (Units.map (algebraMap K M).toMonoidHom (a ^ k)) =
      k • (Additive.ofMul (Units.map (algebraMap K M).toMonoidHom a) : Additive Mˣ)
    rw [map_pow, ofMul_pow]
  have hgh : (χM (g * h)).toAdd.val = ((χM g).toAdd.val + (χM h).toAdd.val) % m := by
    rw [map_mul, toAdd_mul, ZMod.val_add]
  have hinf : (groupCohomology.mapCocycles₂ (AlgEquiv.restrictNormalHom L)
      (inflationCoefficients K L M) (cyclicUnitCocycle K L χL a)) (g, h) =
      cyclicCarry (χL (g.restrictNormal L)).toAdd (χL (h.restrictNormal L)).toAdd •
        baseUnit K M a := by
    change (inflationCoefficients K L M).hom
      (cyclicCarry (χL (g.restrictNormal L)).toAdd (χL (h.restrictNormal L)).toAdd •
        baseUnit K L a) = _
    rw [map_nsmul, inflationCoefficients_baseUnit]
  have hM : (cyclicUnitCocycle K M χM (a ^ k)) (g, h) =
      cyclicCarry (χM g).toAdd (χM h).toAdd • baseUnit K M (a ^ k) := rfl
  rw [Pi.sub_apply, hinf, hM, hpow]
  simp only [groupCohomology.d₁₂_hom_apply, map_nsmul, baseUnit_fixed]
  rw [sub_add_eq_add_sub, sub_eq_sub_iff_add_eq_add, smul_smul, ← add_nsmul, ← add_nsmul,
    ← add_nsmul]
  refine congrArg (· • baseUnit K M a) ?_
  simp only [cyclicCarry, hχ, hgh]
  rw [mul_comm _ k]
  omega

end Cocycle

/-! ## Invariants of carry classes under the carry normalization -/

section Normalization

open Langlands.LocalClassField

variable (K E : Type u) [Field K] [Field E] [Algebra K E] [FiniteDimensional K E]
  [IsGalois K E] {n : ℕ} [NeZero n]

/-- Under the carry normalization, a carry class is the inverse comparison of a norm class. -/
theorem cyclicClass_eq_symm (hnorm : CyclicClassNormNormalization.{u, u})
    (χ : Gal(E/K) ≃* Multiplicative (ZMod n)) (a : Kˣ) :
    cyclicClass K E χ.toMonoidHom a =
      (cyclicH2NormEquiv K E (cyclicCoordinateGenerator χ)
        (cyclicCoordinateGenerator_generates χ)).symm
          (Additive.ofMul (normQuotientProjection K E a)) := by
  rw [AddEquiv.eq_symm_apply]
  exact hnorm K E n χ _ _ (χ.apply_symm_apply _) a

/-- Under the carry normalization, every relative `H²` class is a carry class. -/
theorem exists_cyclicClass_eq (hnorm : CyclicClassNormNormalization.{u, u})
    (χ : Gal(E/K) ≃* Multiplicative (ZMod n)) (x : relativeCohomology K E 2) :
    ∃ a : Kˣ, cyclicClass K E χ.toMonoidHom a = x := by
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (normSubgroup K E)
    (Additive.toMul (cyclicH2NormEquiv K E (cyclicCoordinateGenerator χ)
      (cyclicCoordinateGenerator_generates χ) x))
  refine ⟨a, ?_⟩
  rw [cyclicClass_eq_symm K E hnorm χ a, AddEquiv.symm_apply_eq]
  exact congrArg Additive.ofMul ha

end Normalization

section Invariant

variable {p : ℕ} [Fact p.Prime] (F E : PadicField.{u} p)
  [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
  [FiniteDimensional F.Carrier E.Carrier] [IsGalois F.Carrier E.Carrier]
  [NeZero (Module.finrank F.Carrier E.Carrier)]

/-- Under the carry normalization, the invariant of the carry class of `a` is `ord a / [E:F]`. -/
theorem unramifiedH2Invariant_cyclicClass (hnorm : CyclicClassNormNormalization.{u, u})
    (hram : F.canonicalTopologicalData.ramificationIndex =
      E.canonicalTopologicalData.ramificationIndex)
    (χ : Gal(E.Carrier/F.Carrier) ≃*
      Multiplicative (ZMod (Module.finrank F.Carrier E.Carrier))) (a : F.Carrierˣ) :
    unramifiedH2Invariant F E hram χ (cyclicClass F.Carrier E.Carrier χ.toMonoidHom a) =
      rationalClass ((F.canonicalTopologicalData.ord (a : F.Carrier) : ℚ) /
        Module.finrank F.Carrier E.Carrier) := by
  rw [cyclicClass_eq_symm F.Carrier E.Carrier hnorm χ a,
    unramifiedH2Invariant_normRepresentative]

end Invariant

/-- The carry normalization implies inflation compatibility of the finite unramified invariant. -/
theorem inflationCompatibility_of_normalization (hnorm : CyclicClassNormNormalization.{u, u}) :
    UnramifiedInvariantInflationCompatibility.{u} := by
  intro p _ F L M _ _ _ _ _ _ _ _ _ _ hFL hFM χL χM hL hM x
  have : NeZero (Module.finrank F.Carrier L.Carrier) := ⟨Module.finrank_pos.ne'⟩
  have : NeZero (Module.finrank F.Carrier M.Carrier) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨hLinj, hLfrob⟩ := hL
  obtain ⟨-, hMfrob⟩ := hM
  obtain ⟨a, rfl⟩ := exists_cyclicClass_eq F.Carrier L.Carrier hnorm χL x
  have : FiniteDimensional L.Carrier M.Carrier :=
    Module.Finite.of_restrictScalars_finite F.Carrier L.Carrier M.Carrier
  have hm : Module.finrank F.Carrier M.Carrier =
      Module.finrank F.Carrier L.Carrier * Module.finrank L.Carrier M.Carrier :=
    (Module.finrank_mul_finrank F.Carrier L.Carrier M.Carrier).symm
  have hσ : (cyclicCoordinateGenerator χM).restrictNormal L.Carrier =
      cyclicCoordinateGenerator χL :=
    restrictNormal_frobenius F L.Carrier M.Carrier hLinj hLfrob hMfrob
  have hχ := coordinate_restrict_val F.Carrier L.Carrier M.Carrier ⟨_, hm⟩ χL χM hσ
  rw [inflation_cyclicClass F.Carrier L.Carrier M.Carrier hm χL.toMonoidHom χM.toMonoidHom hχ a,
    unramifiedH2Invariant_cyclicClass F M hnorm, unramifiedH2Invariant_cyclicClass F L hnorm]
  refine congrArg rationalClass ?_
  have hk : (Module.finrank L.Carrier M.Carrier : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  rw [Units.val_pow_eq_pow_val, ← zpow_natCast, PadicField.TopologicalData.ord_zpow, hm]
  push_cast
  rw [mul_comm (Module.finrank F.Carrier L.Carrier : ℚ), mul_div_mul_left _ _ hk]

end UnramifiedInflation

/-- Inflation along a tower of finite unramified Galois extensions preserves the
explicit finite invariant. -/
theorem unramifiedInvariantInflationCompatibility :
    UnramifiedInvariantInflationCompatibility.{u} :=
  UnramifiedInflation.inflationCompatibility_of_normalization
    cyclicClassNormNormalization.{u, u}

end Langlands.ClassFieldTheory.Local
