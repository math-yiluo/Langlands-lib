import Langlands.GaloisCohomology.Global.Abelianization.Frobenius
import Langlands.GaloisCohomology.Local.CupSymbol
import Langlands.Global.FiniteCompletionLocalField
import Langlands.Global.CompletionResidue
import Langlands.Galois.RestrictedRamification.Localization

/-!
# Artin lifts of uniformizers and geometric Frobenius lifts

For a number field `K`, a finite place `v` and the completion `K_v`, this file compares the
arithmetic Artin lifts of local class field theory (`IsArithmeticArtinLift`, for the local-field
structure `FiniteCompletion.valuativeRel v` of `K_v`) with the geometric Frobenius lifts
`IsGeometricFrobeniusLift v` of `Langlands.GaloisRepresentation` (defined through the residue
action on the spectral integers of `AlgebraicClosure K_v` for the norm of `K_v`), and, through
`continuousCharEquivSIdeleClass_sPresentation_one_single`, evaluates the characters of the
`S`-idèle class group attached to characters of `G_S` at the places outside `S` by local class
field theory.

## Main statements

* `residueHom_eq_pow_of_isArithmeticArtinLift`: for a nonarchimedean local field `F`, an
  arithmetic Artin lift `σ ∈ Gal(AlgebraicClosure F / F)` of an element of normalized order `1`
  acts on the residue field of the spectral integers of `AlgebraicClosure F` as `x ↦ x ^ q`, `q`
  the order of the residue field of `F`.
* with `extensionIntegers_eq_localClosureIntegers` and `card_residueField_localNormedField` of
  `Langlands.Galois.FrobeniusLift` (for `K_v`, the spectral integers of `AlgebraicClosure K_v` for the
  norm and for the local-field structure coincide, and the residue field has `N(v)` elements):
* `isGeometricFrobeniusLift_inv_of_isArithmeticArtinLift`: the inverse of an arithmetic Artin lift
  of an element of `K_v` of normalized order `1` is a geometric Frobenius lift at `v`;
  `normalizedUnitOrder_localUniformizer_eq_one`: `localUniformizer v` has normalized order `1`.
* `apply_quotientMap_autCongr_localToGlobalGalois`: a homomorphism from `G_S` to a commutative
  group takes the same value at `localizationHom ι S v σ` and at `σ` mapped by
  `localToGlobalGalois v` and carried to `Gal(Ω / K)` by an isomorphism
  `AlgebraicClosure K ≃ₐ[K] Ω`.
* `continuousCharEquivSIdeleClass_sPresentation_one_single_of_isArithmeticArtinLift`: for a
  continuous character `χ` of `G_S` with values in `ℤ/n` and `v ∉ S`, the character
  `continuousCharEquivSIdeleClass χ` takes at the generator of the divisors prime to `S` at `v`
  the value `χ(σ)⁻¹`, `σ` an arithmetic Artin lift of `localUniformizer v` read in `G_S` through
  `localizationHom ι S v`.

## Proofs

For the residue action, a residue element `x` of `AlgebraicClosure F` generates a finite extension
of degree `m` of the residue field `k` of `F`, so `x ^ (q ^ m) = x`; the unramified extension `E`
of degree `m` (`exists_finiteUnramified_finrank`) has a residue field with `q ^ m` elements whose
image in the residue field of `AlgebraicClosure F` contains every root of `X ^ (q ^ m) - X`, so
`x` comes from `E` (`mem_range_of_pow_card_eq`). On `E`, `σ` restricts to the arithmetic Artin
symbol of `π`, which acts on residues as `y ↦ y ^ q` (`residueHom_arithmeticFiniteArtin`), and
restriction is compatible with the residue actions (`towerSpectralResidueMap_residueHom`).

The two normed structures on `K_v` have the same valuation ring (both are the elements of
valuation at most `1`), so their spectral integers in `AlgebraicClosure K_v`, the integral
closures of that ring, coincide; the residue actions are then read on the same valuation subring
(`residueHom_eq_pow_iff`). The order of `localUniformizer v` is `1`: the valuation of `K_v` and
the normalized valuation of its local-field structure are surjective onto `ℤ` and have the same
nonnegative elements.

For the characters, `localToGlobalGalois v` is the decomposition homomorphism of the standard
embedding of `AlgebraicClosure K` into `AlgebraicClosure K_v`; carried to `Ω` it is the
decomposition homomorphism of an embedding of `Ω` which differs from `ι.finite v` by an
automorphism of `Ω`, hence a conjugate of it.

## References

See the page beside this file.
-/

noncomputable section

namespace Langlands.GaloisCohomology

universe u

section Tower

open IsLocalRing Langlands.LocalGalois

variable (K L E : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [Field E] [Algebra K E]
  [Algebra E L] [IsScalarTower K E L]

section Algebraic

variable [Algebra.IsAlgebraic K E]

/-- The map of spectral integers along a tower `K ⊆ E ⊆ L` of algebraic extensions. -/
def towerSpectralIntegerMap : extensionIntegers K E →+* extensionIntegers K L where
  toFun x := ⟨algebraMap E L x, by
    change spectralNorm K L (algebraMap E L (x : E)) ≤ 1
    rw [← spectralNorm.eq_of_tower (x : E)]
    exact x.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

instance towerSpectralIntegerMap_isLocalHom : IsLocalHom (towerSpectralIntegerMap K L E) where
  map_nonunit x hx := by
    apply (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.integer.integers (spectralValuation K E))).mpr
    have h := (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.integer.integers (spectralValuation K L))).mp hx
    apply NNReal.eq
    have h' := congrArg (fun r : NNReal => (r : ℝ)) h
    change spectralNorm K L (algebraMap E L (x : E)) = 1 at h'
    change spectralNorm K E (x : E) = 1
    rwa [spectralNorm.eq_of_tower (L := L) (x : E)]

/-- The map of residue fields along a tower `K ⊆ E ⊆ L`. -/
def towerSpectralResidueMap :
    ResidueField (extensionIntegers K E) →+* ResidueField (extensionIntegers K L) :=
  ResidueField.map (towerSpectralIntegerMap K L E)

theorem towerSpectralResidueMap_residue (x : extensionIntegers K E) :
    towerSpectralResidueMap K L E (residue _ x) = residue _ (towerSpectralIntegerMap K L E x) :=
  rfl

end Algebraic

/-- Restriction to a normal intermediate extension is compatible with the residue actions. -/
theorem towerSpectralResidueMap_residueHom [Normal K E] (σ : Gal(L/K))
    (y : ResidueField (extensionIntegers K E)) :
    towerSpectralResidueMap K L E (residueHom K E (AlgEquiv.restrictNormalHom E σ) y) =
      residueHom K L σ (towerSpectralResidueMap K L E y) := by
  obtain ⟨x, rfl⟩ := residue_surjective y
  rw [residueHom_apply, towerSpectralResidueMap_residue, towerSpectralResidueMap_residue,
    residueHom_apply]
  congr 1
  apply Subtype.ext
  exact AlgEquiv.restrictNormal_commutes σ E x

variable {E} in
/-- The residue action of `σ` is `x ↦ x ^ q` exactly when `σ y - y ^ q` lies in the maximal ideal
for all spectral integers `y`. -/
theorem residueHom_eq_pow_iff (σ : Gal(L/K)) (q : ℕ) :
    (∀ x, residueHom K L σ x = x ^ q) ↔ ∀ y ∈ extensionIntegers K L,
      (extensionIntegers K L).valuation (σ y - y ^ q) < 1 := by
  constructor
  · intro h y hy
    have e := h (residue _ ⟨y, hy⟩)
    rw [residueHom_apply, ← map_pow, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff] at e
    exact ((extensionIntegers K L).valuation_lt_one_iff _).1 e
  · intro h x
    obtain ⟨y, rfl⟩ := residue_surjective x
    rw [residueHom_apply, ← map_pow, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact ((extensionIntegers K L).valuation_lt_one_iff _).2 (h y y.2)

end Tower

open Polynomial in
/-- An element `x` with `x ^ q = x`, `q` the order of a finite field `k`, lies in the image of any
ring homomorphism from `k`. -/
theorem mem_range_of_pow_card_eq {k k' : Type*} [Field k] [Fintype k] [Field k'] (j : k →+* k')
    {x : k'} (hx : x ^ Fintype.card k = x) : x ∈ Set.range j := by
  classical
  have hq : 1 < Fintype.card k := Fintype.one_lt_card
  have hm : (X ^ Fintype.card k - X : k[X]).Monic := by
    apply Polynomial.monic_X_pow_sub
    rw [degree_X]
    exact_mod_cast hq
  have hroots : (X ^ Fintype.card k - X : k[X]).roots = Finset.univ.val :=
    FiniteField.roots_X_pow_card_sub_X k
  have hcard : Multiset.card (X ^ Fintype.card k - X : k[X]).roots =
      (X ^ Fintype.card k - X : k[X]).natDegree := by
    rw [hroots, Finset.card_val, Finset.card_univ, FiniteField.X_pow_card_sub_X_natDegree_eq k hq]
  have hmap := hm.roots_map_of_card_eq_natDegree j hcard
  have hx' : x ∈ ((X ^ Fintype.card k - X : k[X]).map j).roots := by
    rw [mem_roots (hm.map j).ne_zero, IsRoot.def, Polynomial.map_sub, Polynomial.map_pow, map_X,
      eval_sub, eval_pow, eval_X, hx, sub_self]
  rw [← hmap, hroots] at hx'
  obtain ⟨y, -, rfl⟩ := Multiset.mem_map.1 hx'
  exact ⟨y, rfl⟩

section LocalField

open IsLocalRing Langlands.LocalGalois Langlands.ClassFieldTheory.Local
  Langlands.ClassFieldTheory.Local.Artin

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

attribute [local instance] localNormedField localNormedField_ultrametric localNormedField_complete

/-- **The residue action of an Artin lift of an element of order one.** An arithmetic Artin lift
`σ` of an element of normalized order `1` acts on the residue field of the spectral integers of
`AlgebraicClosure F` as `x ↦ x ^ q`, `q` the order of the residue field of `F`. -/
theorem residueHom_eq_pow_of_isArithmeticArtinLift {π : Fˣ}
    (hπ : normalizedUnitOrder F (.ofMul π) = 1) {σ : Gal(AlgebraicClosure F/F)}
    (hσ : IsArithmeticArtinLift F (AlgebraicClosure F) π σ)
    (x : ResidueField (extensionIntegers F (AlgebraicClosure F))) :
    residueHom F (AlgebraicClosure F) σ x = x ^ Nat.card (ResidueField (baseIntegers F)) := by
  classical
  have : Finite (ResidueField (baseIntegers F)) := localResidue_finite F
  let : Fintype (ResidueField (baseIntegers F)) := Fintype.ofFinite _
  have hxint : IsIntegral (ResidueField (baseIntegers F)) x := Algebra.IsIntegral.isIntegral x
  have : FiniteDimensional (ResidueField (baseIntegers F))
      (IntermediateField.adjoin (ResidueField (baseIntegers F)) {x}) :=
    IntermediateField.adjoin.finiteDimensional hxint
  set m := Module.finrank (ResidueField (baseIntegers F))
    (IntermediateField.adjoin (ResidueField (baseIntegers F)) {x}) with hm
  have hm0 : 0 < m := Module.finrank_pos
  obtain ⟨E, hEfin, hEgal, hE, hEm⟩ := exists_finiteUnramified_finrank F m hm0
  let ιE : SeparableClosure F →ₐ[F] AlgebraicClosure F := IsSepClosed.lift
  let alg : Algebra E (AlgebraicClosure F) := (ιE.comp E.val).toRingHom.toAlgebra
  have tow : @IsScalarTower F E (AlgebraicClosure F) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq fun c => ((ιE.comp E.val).commutes c).symm
  have := isAbelianGalois_of_arithmeticUnramified F E hE
  have hrk : Module.finrank (ResidueField (baseIntegers F))
      (ResidueField (extensionIntegers F E)) = m :=
    ((Separable.arithmeticUnramified_iff_residue_finrank F E).1 hE).trans hEm
  have : FiniteDimensional (ResidueField (baseIntegers F)) (ResidueField (extensionIntegers F E)) :=
    Module.finite_of_finrank_pos (hrk ▸ hm0)
  have : Finite (ResidueField (extensionIntegers F E)) :=
    Module.finite_of_finite (ResidueField (baseIntegers F))
  let : Fintype (ResidueField (extensionIntegers F E)) := Fintype.ofFinite _
  have : Finite (IntermediateField.adjoin (ResidueField (baseIntegers F)) {x}) :=
    Module.finite_of_finite (ResidueField (baseIntegers F))
  let : Fintype (IntermediateField.adjoin (ResidueField (baseIntegers F)) {x}) :=
    Fintype.ofFinite _
  have hcardE : Fintype.card (ResidueField (extensionIntegers F E)) =
      Nat.card (ResidueField (baseIntegers F)) ^ m := by
    rw [Module.card_eq_pow_finrank (K := ResidueField (baseIntegers F)), hrk,
      Nat.card_eq_fintype_card]
  have hxpow : x ^ Fintype.card (ResidueField (extensionIntegers F E)) = x := by
    have hcardM : Fintype.card (IntermediateField.adjoin (ResidueField (baseIntegers F)) {x}) =
        Nat.card (ResidueField (baseIntegers F)) ^ m := by
      rw [Module.card_eq_pow_finrank (K := ResidueField (baseIntegers F)), ← hm,
        Nat.card_eq_fintype_card]
    have h := FiniteField.pow_card (⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩ :
      IntermediateField.adjoin (ResidueField (baseIntegers F)) {x})
    rw [hcardE, ← hcardM]
    exact congrArg Subtype.val h
  obtain ⟨y, rfl⟩ :=
    mem_range_of_pow_card_eq (towerSpectralResidueMap F (AlgebraicClosure F) E) hxpow
  rw [← towerSpectralResidueMap_residueHom, hσ.restrictNormalHom_eq E,
    residueHom_arithmeticFiniteArtin F E hE π hπ, map_pow]

end LocalField

section Frobenius

open scoped Valued
open IsLocalRing Langlands.LocalGalois NumberField IsDedekindDomain Langlands.Global
  Langlands.GaloisRepresentation Langlands.ClassFieldTheory.Local
  Langlands.ClassFieldTheory.Local.Artin

variable {K : Type u} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

/-- **An Artin lift of an element of order one is the inverse of a geometric Frobenius lift.** For
an element `π` of `K_v` of normalized order `1` and an arithmetic Artin lift `σ` of `π` (local
class field theory), `σ⁻¹` is a geometric Frobenius lift at `v`: `σ` acts on the residue field of
`AlgebraicClosure K_v` as `x ↦ x ^ N(v)`. -/
theorem isGeometricFrobeniusLift_inv_of_isArithmeticArtinLift {π : (FiniteCompletion K v)ˣ}
    (hπ : letI := FiniteCompletion.valuativeRel v
      letI := FiniteCompletion.isNonarchimedeanLocalField v
      normalizedUnitOrder (FiniteCompletion K v) (.ofMul π) = 1)
    {σ : LocalGroup v}
    (hσ : letI := FiniteCompletion.valuativeRel v
      letI := FiniteCompletion.isNonarchimedeanLocalField v
      IsArithmeticArtinLift (FiniteCompletion K v) (AlgebraicClosure (FiniteCompletion K v)) π σ) :
    IsGeometricFrobeniusLift v σ⁻¹ := by
  have h₂ : ∀ y ∈ localClosureIntegers v, (localClosureIntegers v).valuation
      (DFunLike.coe (F := Gal(AlgebraicClosure (FiniteCompletion K v)/FiniteCompletion K v)) σ y -
        y ^ Ideal.absNorm v.asIdeal) < 1 := by
    let _ := FiniteCompletion.valuativeRel v
    have := FiniteCompletion.isNonarchimedeanLocalField v
    let := localNormedField (FiniteCompletion K v)
    let := localNormedField_ultrametric (FiniteCompletion K v)
    let := localNormedField_complete (FiniteCompletion K v)
    rw [← card_residueField_localNormedField v]
    exact (residueHom_eq_pow_iff (FiniteCompletion K v) (AlgebraicClosure (FiniteCompletion K v))
      σ _).1 (residueHom_eq_pow_of_isArithmeticArtinLift (FiniteCompletion K v) hπ hσ)
  rw [← extensionIntegers_eq_localClosureIntegers v] at h₂
  intro x
  simp only [inv_inv]
  exact (residueHom_eq_pow_iff (FiniteCompletion K v) (AlgebraicClosure (FiniteCompletion K v))
    σ _).2 h₂ x

/-- The image of `globalUniformizer v` in `K_v` has normalized order `1`. -/
theorem normalizedUnitOrder_localUniformizer_eq_one :
    letI := FiniteCompletion.valuativeRel v
    letI := FiniteCompletion.isNonarchimedeanLocalField v
    normalizedUnitOrder (FiniteCompletion K v)
      (.ofMul (GaloisCohomology.localUniformizer v)) = 1 := by
  let _ := FiniteCompletion.valuativeRel v
  have := FiniteCompletion.isNonarchimedeanLocalField v
  set π := GaloisCohomology.localUniformizer v
  set u := ClassFieldTheory.Local.localUniformizer (FiniteCompletion K v)
  have hπv : Valued.v (π : FiniteCompletion K v) = WithZero.exp (-1 : ℤ) :=
    valued_localUniformizer v
  have hu : normalizedUnitOrder (FiniteCompletion K v) (.ofMul u) = 1 :=
    normalizedUnitOrder_localUniformizer _
  -- the order of `u` for `Valued.v`
  have hu0 : Valued.v (u : FiniteCompletion K v) ≠ 0 := (_root_.map_ne_zero _).2 u.ne_zero
  set m := -WithZero.log (Valued.v (u : FiniteCompletion K v)) with hm
  have hum : Valued.v (u : FiniteCompletion K v) = WithZero.exp (-m) := by
    rw [hm, neg_neg, WithZero.exp_log hu0]
  have hpos : 0 < m := by
    have h := (normalizedUnitOrder_pos_iff (FiniteCompletion K v) u).1 (by rw [hu]; exact one_pos)
    rw [ValuativeRel.vlt, FiniteCompletion.valuativeRel_vle, not_le, map_one, hum] at h
    have := WithZero.exp_lt_exp.1 (h.trans_eq WithZero.exp_zero.symm)
    omega
  -- `π ^ m / u` is a unit of the valuation ring
  have hw : normalizedUnitOrder (FiniteCompletion K v) (.ofMul (π ^ m * u⁻¹)) = 0 := by
    rw [normalizedUnitOrder_eq_zero_iff]
    have hv1 : Valued.v ((π ^ m * u⁻¹ : (FiniteCompletion K v)ˣ) : FiniteCompletion K v) = 1 := by
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, map_mul, map_zpow₀,
        map_inv₀, hπv, hum, ← WithZero.exp_zsmul, ← WithZero.exp_neg, ← WithZero.exp_add]
      rw [smul_eq_mul]
      ring_nf
      exact WithZero.exp_zero
    refine le_antisymm ?_ ?_
    · rw [← map_one (ValuativeRel.valuation (FiniteCompletion K v)),
        ← Valuation.vle_iff_le, FiniteCompletion.valuativeRel_vle, hv1, map_one]
    · rw [← map_one (ValuativeRel.valuation (FiniteCompletion K v)),
        ← Valuation.vle_iff_le, FiniteCompletion.valuativeRel_vle, hv1, map_one]
  rw [ofMul_mul, ofMul_zpow, ofMul_inv, map_add, map_zsmul, map_neg, hu, smul_eq_mul] at hw
  set k := normalizedUnitOrder (FiniteCompletion K v) (.ofMul π)
  have hk : m * k = 1 := by linarith
  have hk1 : 0 < k := by nlinarith
  nlinarith

end Frobenius

section Conjugation

open NumberField IsDedekindDomain Langlands.Global Langlands.GaloisRepresentation Langlands.Galois

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K)))

omit [IsSepClosure K Ω] in
/-- `localToGlobalGalois v` is the decomposition homomorphism of the standard embedding of
`AlgebraicClosure K` into `AlgebraicClosure K_v`. -/
theorem localToGlobalGalois_eq_decompositionHom (v : HeightOneSpectrum (𝓞 K))
    (σ : Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K)) :
    localToGlobalGalois v σ =
      decompositionHom (v.adicCompletion K) ((PlaceEmbeddings.standard K).finite v) σ :=
  (PlaceEmbeddings.decompositionHom_standard_finite v σ).symm

omit [NumberField K] [IsSepClosure K Ω] in
/-- Transport of a decomposition homomorphism along an isomorphism `f : A ≃ₐ[K] Ω`. -/
theorem autCongr_decompositionHom {A Kv Ωv : Type*} [Field A] [Algebra K A] [Field Kv] [Field Ωv]
    [Algebra K Kv] [Algebra Kv Ωv] [Algebra K Ωv] [IsScalarTower K Kv Ωv] [Normal K A] [Normal K Ω]
    (f : A ≃ₐ[K] Ω) (j : A →ₐ[K] Ωv) (σ : Gal(Ωv/Kv)) :
    f.autCongr (decompositionHom Kv j σ) = decompositionHom Kv (j.comp f.symm.toAlgHom) σ := by
  symm
  rw [decompositionHom_eq_iff]
  intro x
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.autCongr_apply,
    AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply,
    decompositionHom_apply]

/-- **The local Galois groups of `ι` and of Mathlib's embeddings.** A homomorphism from `G_S` to a
commutative group takes the same value at the localization `localizationHom ι S v σ` and at
`σ` mapped by `localToGlobalGalois v` and carried to `Gal(Ω / K)` by any isomorphism
`f : AlgebraicClosure K ≃ₐ[K] Ω`: the two embeddings of `Ω` into `AlgebraicClosure K_v` differ by an
automorphism of `Ω`, which conjugates the decomposition homomorphisms. -/
theorem apply_quotientMap_autCongr_localToGlobalGalois {M : Type*} [CommGroup M]
    (χ : GaloisGroupUnramifiedOutside K Ω S →* M) (f : AlgebraicClosure K ≃ₐ[K] Ω)
    (v : HeightOneSpectrum (𝓞 K))
    (σ : Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K)) :
    χ (GaloisGroupUnramifiedOutside.quotientMap K Ω S (f.autCongr (localToGlobalGalois v σ))) =
      χ (localizationHom ι S v σ) := by
  have : IsGalois K Ω := IsSepClosure.isGalois
  rw [localToGlobalGalois_eq_decompositionHom, autCongr_decompositionHom,
    localizationHom_eq_quotientMap]
  obtain ⟨g, hg⟩ := exists_eq_comp_of_normal (ι.finite v)
    (((PlaceEmbeddings.standard K).finite v).comp f.symm.toAlgHom)
  rw [hg, decompositionHom_comp]
  simp only [map_mul, map_inv]
  exact inv_mul_cancel_comm _ _

end Conjugation

section Character

open NumberField IsDedekindDomain Langlands.Global Langlands.GaloisRepresentation Langlands.Galois
  Langlands.ClassFieldTheory.Local Langlands.ClassFieldTheory.Local.Artin

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K))) {n : ℕ}
  [NeZero n]

/-- **The character of the `S`-idèle class group at a place outside `S`, by local class field
theory.** For a continuous character `χ` of `G_S` with values in `ℤ/n`, a finite place `v ∉ S` and
an arithmetic Artin lift `σ` (of local class field theory) of the uniformizer
`localUniformizer v`, the character `continuousCharEquivSIdeleClass χ` of the `S`-idèle class
group takes at the generator of the divisors prime to `S` at `v` the value `χ(σ)⁻¹`, `σ` mapped to
`G_S` by the localization `localizationHom ι S v`. -/
theorem continuousCharEquivSIdeleClass_sPresentation_one_single_of_isArithmeticArtinLift [Finite S]
    (h : Odd n ∨ IsTotallyComplex K)
    (χ : ContinuousMonoidHom (GaloisGroupUnramifiedOutside K Ω S) (Multiplicative (ZMod n)))
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S)
    (σ : Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K))
    (hσ : letI := FiniteCompletion.valuativeRel v
      letI := FiniteCompletion.isNonarchimedeanLocalField v
      IsArithmeticArtinLift (FiniteCompletion K v) (AlgebraicClosure (FiniteCompletion K v))
        (GaloisCohomology.localUniformizer v) σ) :
    continuousCharEquivSIdeleClass Ω (Set.toFinite S) h χ
        (sPresentation S (1, Multiplicative.ofAdd (Finsupp.single ⟨v, hv⟩ 1))) =
      (χ (localizationHom ι S v σ))⁻¹ := by
  rw [continuousCharEquivSIdeleClass_sPresentation_one_single h χ
    (IsSepClosure.equiv K (AlgebraicClosure K) Ω) hv σ⁻¹
    (isGeometricFrobeniusLift_inv_of_isArithmeticArtinLift v
      (normalizedUnitOrder_localUniformizer_eq_one v) hσ)]
  refine (apply_quotientMap_autCongr_localToGlobalGalois ι S χ.toMonoidHom
    (IsSepClosure.equiv K (AlgebraicClosure K) Ω) v σ⁻¹).trans ?_
  exact (congrArg χ (map_inv (localizationHom ι S v) σ)).trans (map_inv χ _)

end Character

end Langlands.GaloisCohomology
