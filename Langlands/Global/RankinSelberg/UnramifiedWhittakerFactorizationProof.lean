import Langlands.Global.RankinSelberg.UnramifiedWhittakerFactorizationStatement
import Langlands.Global.RankinSelberg.UnfoldingGL
import Langlands.Global.RankinSelberg.UnfoldingCoefficient
import Langlands.Global.RankinSelberg.UnequalAnalyticProof
import Langlands.Global.FiniteAdelicGL.PadicComparison
import Langlands.Automorphic.ContragredientSphericalSpectrum
import Langlands.Representation.Unramified.StandardHeckeSum
import Langlands.Representation.Unramified.TopHeckeOperator
import Langlands.Representation.Unramified.PrincipalSeriesHecke
import Langlands.Representation.Conductor.UnramifiedSphericalWhittaker
import Langlands.Representation.RankinSelberg.UnramifiedPairTorusCoefficient
import Langlands.Representation.RankinSelberg.HighlyRamified.EssentialInput

/-! # Proof of the factorization of global Whittaker functions at an unramified place

See the paired Markdown for the route.
-/

noncomputable section
universe u uQ
open NumberField MeasureTheory
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.UnramifiedWhittaker

open Langlands.GeneralLinear Langlands.GeneralLinear.Iwasawa Langlands.GeneralLinear.Spherical
open Langlands.Conductor

/-! ### Independence of the spherical Whittaker function from the uniformizer -/

section Local

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation K Γ₀}

theorem torus_eq_torus_mul {m : ℕ} (ϖ ϖ' : Kˣ) (lam : Fin m → ℤ) :
    torus ϖ' lam = torus ϖ lam * torus (ϖ⁻¹ * ϖ') lam := by
  unfold torus
  rw [← map_mul]
  congr 1
  funext i
  simp only [Pi.mul_apply]
  rw [mul_zpow, ← mul_assoc, ← mul_zpow, mul_inv_cancel, one_zpow, one_mul]

theorem torus_quotient_mem {n : ℕ} {ϖ ϖ' : Kˣ} (h : v (ϖ' : K) = v (ϖ : K))
    (lam : Fin (n + 1) → ℤ) :
    torus (ϖ⁻¹ * ϖ') lam ∈ integralSubgroup v.integer n := by
  have hu : v ((ϖ⁻¹ * ϖ' : Kˣ) : K) = 1 := by
    rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, h,
      inv_mul_cancel₀ ((Valuation.ne_zero_iff v).mpr ϖ.ne_zero)]
  apply diagonalUnits_mem
  intro i
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hu, one_zpow]

/-- The explicit spherical Whittaker function does not depend on the uniformizer. -/
theorem sphericalWhittaker_eq_of_isUniformizingElement {n : ℕ} {ϖ ϖ' : Kˣ}
    (hϖ : IsUniformizingElement v ϖ) (hϖ' : IsUniformizingElement v ϖ')
    {θ : GeneralLinear.upperUnipotent (n + 1) K →* ℂˣ} (hθ : IsIntegrallyTrivial v θ) (q : ℕ)
    (x : Fin (n + 1) → ℂˣ) :
    sphericalWhittaker hϖ' θ q x = sphericalWhittaker hϖ θ q x := by
  have hv := RankinSelberg.UnramifiedPairTorus.valuation_eq_of_isUniformizingElement v hϖ hϖ'
  have hval : ∀ lam : Fin (n + 1) → ℤ, sphericalWhittaker hϖ' θ q x (torus ϖ lam) =
      if Antitone lam then halfModulus q lam * satakeSchur x lam else 0 := by
    intro lam
    have ht : torus ϖ lam = torus ϖ' lam * (torus (ϖ⁻¹ * ϖ') lam)⁻¹ := by
      rw [torus_eq_torus_mul ϖ ϖ' lam, mul_inv_cancel_right]
    rw [ht, sphericalWhittaker_mul_integral hϖ' q x hθ _ (inv_mem (torus_quotient_mem hv lam)),
      sphericalWhittaker_torus hϖ' q x hθ]
  have h := eq_cellFunction hϖ hθ (sphericalWhittaker_mem hϖ' q x hθ)
    (fun g k hk => sphericalWhittaker_mul_integral hϖ' q x hθ g hk)
    (fun lam hlam => by rw [hval]; simp [hlam])
  refine h.trans ?_
  have hc : (fun lam => sphericalWhittaker hϖ' θ q x (torus ϖ lam)) =
      fun lam => if Antitone lam then halfModulus q lam * satakeSchur x lam else 0 :=
    funext hval
  rw [hc]
  funext g
  simp only [sphericalWhittaker, cellFunction]
  split_ifs with hg <;> rfl

end Local

/-! ### Coefficients of a spherical Hecke eigenvector over a `p`-adic field -/

section Coefficient

open Langlands.Unramified Langlands.Unramified.MinusculeCosets Langlands.Whittaker
open Langlands.Whittaker.UpperUnipotentCharacter (adjacentUnit)

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel

/-- The top elementary coefficient of a tuple is the product of its entries. -/
theorem elementaryCoefficient_ofTuple_top {n : ℕ} (z : Fin n → ℂˣ) :
    elementaryCoefficient (Eigenvalues.ofTuple z) n = ∏ i, (z i : ℂ) := by
  rw [elementaryCoefficient_ofTuple]
  have : Subsingleton {S : Finset (Fin n) // S.card = n} :=
    ⟨fun a b => Subtype.ext (((Finset.card_eq_iff_eq_univ _).1
      (a.2.trans (Fintype.card_fin n).symm)).trans
        ((Finset.card_eq_iff_eq_univ _).1 (b.2.trans (Fintype.card_fin n).symm)).symm)⟩
  rw [Fintype.sum_subsingleton _ ⟨Finset.univ, by simp⟩]

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p)

theorem card_residueField :
    Fintype.card K.canonicalTopologicalData.ResidueField =
      K.canonicalTopologicalData.residueCardinality := by
  rw [PadicField.TopologicalData.residueCardinality, Nat.card_eq_fintype_card]

theorem torus_neg_one_mul_standardDiagonal_last (r : ℕ) :
    torus K.canonicalTopologicalData.uniformizerUnit (fun _ : Fin (r + 1) => (-1 : ℤ)) *
      standardDiagonal K r (Fin.last (r + 1)) = 1 := by
  apply Units.ext
  rw [Units.val_mul, torus_val, standardDiagonal_val, Matrix.diagonal_mul_diagonal,
    Units.val_one, ← Matrix.diagonal_one]
  congr 1
  funext j
  have hj : j.val < (Fin.last (r + 1)).val := by rw [Fin.val_last]; exact j.isLt
  simp only [hj, ↓reduceIte, zpow_neg, zpow_one, Units.inv_mul]

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Shintani's uniqueness for a spherical vector with the standard Hecke scalars of a
Satake parameter `x`: every `θ`-functional has coefficient `ℓ(b) W°(·; x)`, for every
uniformizing element. -/
theorem coefficientMap_eq_smul_of_corner {r : ℕ}
    (ρ : Representation ℂ (GeneralLinear (r + 1) K.Carrier) V) (hρ : IsSmooth ρ)
    (x : Fin (r + 1) → ℂˣ)
    (b : fixedVectors ρ (sphericalOpenSubgroup K r).toSubgroup)
    (hb : ∀ i : Fin (r + 2), PairedHecke.corner K ρ hρ (standardHeckeElement K r i) b =
      standardHeckeScalar K (Eigenvalues.ofTuple x) i • b)
    {θ : GeneralLinear.upperUnipotent (r + 1) K.Carrier →* ℂˣ}
    (hθK : IsIntegrallyTrivial (ValuativeRel.valuation K.Carrier) θ)
    (hθ : ∀ i : Fin r, ∃ z : K.Carrier, ValuativeRel.valuation K.Carrier z *
        ValuativeRel.valuation K.Carrier (K.canonicalTopologicalData.uniformizerUnit : K.Carrier)
          ≤ 1 ∧ θ (adjacentUnit i z) ≠ 1)
    (ℓ : functionals (GeneralLinear.upperUnipotent (r + 1) K.Carrier) θ ρ)
    {ϖ : K.Carrierˣ} (hϖ : IsUniformizingElement (ValuativeRel.valuation K.Carrier) ϖ) :
    (coefficientMap ρ ℓ (b : V)).val = ℓ.val (b : V) •
      sphericalWhittaker hϖ θ K.canonicalTopologicalData.residueCardinality x := by
  have hϖ0 := uniformizerUnit_isUniformizingElement K
  set q := K.canonicalTopologicalData.residueCardinality
  have hcard : Fintype.card K.canonicalTopologicalData.ResidueField = q := card_residueField K
  have hq : 0 < q := hcard ▸ Fintype.card_pos
  rw [sphericalWhittaker_eq_of_isUniformizingElement hϖ0 hϖ hθK q x]
  refine Conductor.coefficientMap_eq_smul_sphericalWhittaker hϖ0 hq hcard (residueLift K)
    (residueLift_mem K) (fun _ _ h => residueLift_eq_of_lt_one K h)
    (fun _ hz => exists_residueLift_lt_one K hz) hθK hθ x ρ ℓ (b : V)
    (fun k hk => b.property ⟨k, hk⟩) (fun k hk1 hkm => ?_) ?_
  · have hs := standardHecke_cornerAction_eq_sum K ρ hρ ⟨k, by omega⟩ b
    have hc := congrArg Subtype.val (hb ⟨k, by omega⟩)
    exact hs.symm.trans hc
  · have hD := (standardHecke_cornerAction_last K ρ hρ b).symm.trans
      (congrArg Subtype.val (hb (Fin.last (r + 1))))
    rw [Submodule.coe_smul, standardHeckeScalar_last, elementaryCoefficient_ofTuple_top] at hD
    have hc0 : (∏ i, (x i : ℂ)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => (x i).ne_zero
    calc ρ (torus K.canonicalTopologicalData.uniformizerUnit fun _ => (-1 : ℤ)) (b : V)
        = (∏ i, (x i : ℂ))⁻¹ • ρ (torus K.canonicalTopologicalData.uniformizerUnit
            fun _ => (-1 : ℤ)) ((∏ i, (x i : ℂ)) • (b : V)) := by
          rw [map_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      _ = (∏ i, (x i : ℂ))⁻¹ • (b : V) := by
          rw [← hD, ← Module.End.mul_apply, ← map_mul,
            torus_neg_one_mul_standardDiagonal_last, map_one, Module.End.one_apply]

end Coefficient

/-! ### Global Whittaker coefficients -/

section Global

open Langlands.Global Langlands.Automorphic

local instance uwfpSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance uwfpSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _
local instance uwfpRationalAddCommGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance uwfpContinuousAddCommGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance uwfpSmoothAddCommGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance uwfpFormsAddCommGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance uwfpStableAddCommGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance uwfpRealizationAddCommGroup {F : Type u} [Field F] [NumberField F] {n : ℕ}
    (S : OperatorRealization F n) : AddCommGroup S.Space := Submodule.addCommGroup _

variable (F : Type u) [Field F] [NumberField F]

/-- The complex character of a unitary character of `𝔸` trivial on `F` is standard. -/
theorem isStandardAdditiveCharacter_complex
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) :
    IsStandardAdditiveCharacter F ψ.complex := by
  refine ⟨ψ.continuous_complex, fun h => ψ.nontrivial ?_, fun x => ?_, ψ.norm_complex⟩
  · ext x
    have hx := congrArg (fun χ : AddChar (Adeles F) ℂ => χ x) h
    simp only [HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply, AddChar.one_apply] at hx
    simpa using hx
  · rw [HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply, hψ x, Circle.coe_one]

/-- The adelic point with `h` at the finite place `v` and `1` at every other place. -/
abbrev localPoint {n : ℕ} (v : FinitePlace F) (h : FiniteLocalGL F n v) : Points F n :=
  (GeneralLinearGroupPoints.adelicEquiv F n).symm
    (AdelicGL.ofFinite F n (FiniteAdelicGL.localInclusion F n v h))

theorem split_ofFinite {n : ℕ} (D : FiniteAdelicGL F n) :
    AdelicGL.split F n (AdelicGL.ofFinite F n D) = (1, D) :=
  (AdelicGL.split F n).apply_symm_apply (1, D)

/-- An adelic matrix with trivial component at `v` commutes with every matrix supported
at `v`. -/
theorem ofFinite_localInclusion_comm {n : ℕ} (v : FinitePlace F) (A : AdelicGL F n)
    (hA : FiniteAdelicGL.localProjection F n v (AdelicGL.finite F n A) = 1)
    (h : FiniteLocalGL F n v) :
    A * AdelicGL.ofFinite F n (FiniteAdelicGL.localInclusion F n v h) =
      AdelicGL.ofFinite F n (FiniteAdelicGL.localInclusion F n v h) * A := by
  apply (AdelicGL.split F n).injective
  rw [map_mul, map_mul, split_ofFinite]
  change (AdelicGL.infinite F n A, AdelicGL.finite F n A) * (1, _) =
    (1, _) * (AdelicGL.infinite F n A, AdelicGL.finite F n A)
  rw [Prod.mk_mul_mk, Prod.mk_mul_mk, mul_one, one_mul]
  congr 1
  apply FiniteAdelicGL.ext_localProjection
  intro w
  rw [map_mul, map_mul]
  by_cases hw : w = v
  · subst hw
    rw [hA, FiniteAdelicGL.localProjection_localInclusion, one_mul, mul_one]
  · rw [FiniteAdelicGL.localProjection_localInclusion_of_ne F n v w hw, one_mul, mul_one]

/-- A point with trivial component at `v` commutes with every point supported at `v`. -/
theorem commute_localPoint {n : ℕ} (v : FinitePlace F) (g : Points F n)
    (hg : finiteComponent F n v g = 1) (h : FiniteLocalGL F n v) :
    g * localPoint F v h = localPoint F v h * g := by
  apply (GeneralLinearGroupPoints.adelicEquiv F n).injective
  rw [MulEquiv.map_mul, MulEquiv.map_mul, MulEquiv.apply_symm_apply]
  exact ofFinite_localInclusion_comm F v _ hg h

theorem localInclusion_apply_self {n : ℕ} (v : FinitePlace F) (h : FiniteLocalGL F n v)
    (i j : Fin n) : FiniteAdelicGL.localInclusion F n v h i j v = h i j := by
  rw [← FiniteAdelicGL.localProjection_apply, FiniteAdelicGL.localProjection_localInclusion]

theorem localInclusion_apply_of_ne {n : ℕ} (v w : FinitePlace F) (hw : w ≠ v)
    (h : FiniteLocalGL F n v) (i j : Fin n) :
    FiniteAdelicGL.localInclusion F n v h i j w =
      (1 : Matrix (Fin n) (Fin n) (FiniteCompletion F w)) i j := by
  rw [← FiniteAdelicGL.localProjection_apply,
    FiniteAdelicGL.localProjection_localInclusion_of_ne F n v w hw]
  rfl

/-- An off-diagonal entry of a matrix supported at `v` is the adele supported at `v`. -/
theorem ofFinite_localInclusion_apply_of_ne {n : ℕ} [DecidableEq (FinitePlace F)]
    (v : FinitePlace F) (h : FiniteLocalGL F n v) {i j : Fin n} (hij : i ≠ j) :
    (AdelicGL.ofFinite F n (FiniteAdelicGL.localInclusion F n v h) :
        Matrix (Fin n) (Fin n) (Adeles F)) i j =
      (((0 : InfiniteAdeles F),
        (RestrictedProduct.single (fun w : FinitePlace F => w.adicCompletionIntegers F) v
          (h i j) : FiniteAdeles F)) : Adeles F) := by
  change @Eq (InfiniteAdeleRing F × IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)
    ((1 : Matrix (Fin n) (Fin n) (InfiniteAdeleRing F)) i j,
      FiniteAdelicGL.localInclusion F n v h i j) _
  refine Prod.ext (Matrix.one_apply_ne hij) ?_
  apply IsDedekindDomain.FiniteAdeleRing.ext
  intro w
  by_cases hw : w = v
  · subst hw
    rw [localInclusion_apply_self]
    exact (RestrictedProduct.single_eq_same _ w (h i j)).symm
  · rw [localInclusion_apply_of_ne F v w hw, Matrix.one_apply_ne hij]
    exact (RestrictedProduct.single_eq_of_ne _ (h i j) hw).symm

/-- A diagonal entry of a matrix supported at `v`, with entry one there, is one. -/
theorem ofFinite_localInclusion_apply_diag {n : ℕ} (v : FinitePlace F)
    (h : FiniteLocalGL F n v) {i : Fin n} (hi : h i i = 1) :
    (AdelicGL.ofFinite F n (FiniteAdelicGL.localInclusion F n v h) :
        Matrix (Fin n) (Fin n) (Adeles F)) i i = 1 := by
  change @Eq (InfiniteAdeleRing F × IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)
    ((1 : Matrix (Fin n) (Fin n) (InfiniteAdeleRing F)) i i,
      FiniteAdelicGL.localInclusion F n v h i i) (1, 1)
  refine Prod.ext (Matrix.one_apply_eq i) ?_
  apply IsDedekindDomain.FiniteAdeleRing.ext
  intro w
  by_cases hw : w = v
  · subst hw
    rw [localInclusion_apply_self, hi]
    rfl
  · rw [localInclusion_apply_of_ne F v w hw, Matrix.one_apply_eq]
    rfl

/-- A below-diagonal entry of a matrix supported at `v`, with entry zero there, is zero. -/
theorem ofFinite_localInclusion_apply_zero {n : ℕ} (v : FinitePlace F)
    (h : FiniteLocalGL F n v) {i j : Fin n} (hij : i ≠ j) (h0 : h i j = 0) :
    (AdelicGL.ofFinite F n (FiniteAdelicGL.localInclusion F n v h) :
        Matrix (Fin n) (Fin n) (Adeles F)) i j = 0 := by
  classical
  rw [ofFinite_localInclusion_apply_of_ne F v h hij, h0, RestrictedProduct.single_zero]
  rfl

/-- The point supported at `v` by an upper unitriangular matrix is adelic unipotent. -/
theorem localPoint_mem_unipotentAdelic {n : ℕ} (v : FinitePlace F) (u : FiniteLocalGL F n v)
    (hu : u ∈ GeneralLinear.upperUnipotent n (FiniteCompletion F v)) :
    localPoint F v u ∈ unipotentAdelic F n := by
  rw [Unfolding.mem_unipotentAdelic_iff, MulEquiv.apply_symm_apply]
  refine ⟨fun i j hji => ofFinite_localInclusion_apply_zero F v u (ne_of_lt hji).symm
    (hu.1 hji), fun i => ofFinite_localInclusion_apply_diag F v u (hu.2 i)⟩

/-- The generic character of `ψ⁻¹` is the inverse of that of `ψ`. -/
theorem genericCharacter_inv (r : ℕ) (ψ : AddChar (Adeles F) ℂ) (m : Fin r → F)
    (x : unipotentAdelic F (r + 1)) :
    genericCharacter F r ψ⁻¹ m x = (genericCharacter F r ψ m x)⁻¹ :=
  AddChar.inv_apply' ψ _

variable [CompactSpace (AdeleQuotient F)]

theorem cuspFunction_add {r : ℕ} (T : CuspidalOperatorRealization F r) (y z : T.Space) :
    cuspFunction F T (y + z) = cuspFunction F T y + cuspFunction F T z := by
  funext x
  simp only [cuspFunction, map_add]
  rfl

theorem cuspFunction_smul {r : ℕ} (T : CuspidalOperatorRealization F r) (c : ℂ)
    (y : T.Space) : cuspFunction F T (c • y) = c • cuspFunction F T y := by
  funext x
  simp only [cuspFunction, map_smul]
  rfl

/-- Right translation by a finite adelic element. -/
theorem cuspFunction_finiteRepresentation {r : ℕ} (T : CuspidalOperatorRealization F r)
    (d : FiniteAdelicGL F (r + 1)) (y : T.Space) (z : Points F (r + 1)) :
    cuspFunction F T (T.realization.finiteRepresentation d y) z =
      cuspFunction F T y (z * (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm
        (AdelicGL.ofFinite F (r + 1) d)) := by
  simp only [UnequalAnalytic.cuspFunction_eq F T]
  change ContinuousRationalFunctions.evaluate F (r + 1) (T.realization.toContinuous y)
      (GeneralLinearGroupPoints.adelicEquiv F (r + 1) z * AdelicGL.ofFinite F (r + 1) d) =
    ContinuousRationalFunctions.evaluate F (r + 1) (T.realization.toContinuous y)
      (GeneralLinearGroupPoints.adelicEquiv F (r + 1)
        (z * (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm
          (AdelicGL.ofFinite F (r + 1) d)))
  have h := (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).map_mul z
    ((GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm (AdelicGL.ofFinite F (r + 1) d))
  rw [MulEquiv.apply_symm_apply] at h
  exact congrArg (ContinuousRationalFunctions.evaluate F (r + 1)
    (T.realization.toContinuous y)) h.symm

open AdelicSubgroupPoints in
/-- The integrand of a cusp Whittaker coefficient is integrable: it descends to a
continuous function on the compact quotient `N(F) \ N(𝔸)`. -/
theorem integrable_coefficientIntegrand {r : ℕ} (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (T : CuspidalOperatorRealization F r)
    (y : T.Space) (g : Points F (r + 1)) :
    Integrable (Unfolding.coefficientIntegrand F (Scheme F (r + 1)) (upperUnipotent F (r + 1))
      (genericCharacter F r ψ fun _ => 1) (cuspFunction F T y) g)
      (normalizedRationalQuotientHaarMeasure F (Scheme F (r + 1))
        (upperUnipotent F (r + 1))) := by
  have := rationalQuotientBorelSpace F (Scheme F (r + 1)) (upperUnipotent F (r + 1))
  have := Unfolding.compactSpace_unipotentRationalQuotient F (r + 1)
  have := normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F (Scheme F (r + 1))
    (upperUnipotent F (r + 1))
  let k : unipotentAdelic F (r + 1) → ℂ := fun n =>
    cuspFunction F T y ((n : Points F (r + 1)) * g) *
      starRingEnd ℂ (genericCharacter F r ψ (fun _ => 1) n)
  have hk : ∀ (c : rationalSubgroup F (Scheme F (r + 1)) (upperUnipotent F (r + 1)))
      (n : unipotentAdelic F (r + 1)), k ((c : unipotentAdelic F (r + 1)) * n) = k n := by
    intro c n
    simp only [k, Subgroup.coe_mul, mul_assoc]
    rw [Unfolding.cuspFunction_rational_mul F T y
        (Unfolding.mem_rationalSubgroup_of_unipotent F c),
      Unfolding.genericCharacter_rational_mul F r ψ hψ]
  have hkc : Continuous k :=
    ((Unfolding.continuous_cuspFunction F T y).comp
      (continuous_subtype_val.mul continuous_const)).mul
      (Complex.continuous_conj.comp (Unfolding.continuous_genericCharacter F r ψ hψ.1 _))
  have heq : Unfolding.coefficientIntegrand F (Scheme F (r + 1)) (upperUnipotent F (r + 1))
      (genericCharacter F r ψ fun _ => 1) (cuspFunction F T y) g =
        LeftCosetSpace.lift _ k hk :=
    Unfolding.out_eq_lift _ k hk
  rw [heq]
  have hc := LeftCosetSpace.continuous_lift _ k hk hkc
  exact integrableOn_univ.mp (hc.continuousOn.integrableOn_of_subset_isCompact isCompact_univ
    MeasurableSet.univ subset_rfl (measure_ne_top _ _))

open AdelicSubgroupPoints in
theorem cuspWhittaker_add {r : ℕ} (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (T : CuspidalOperatorRealization F r)
    (y z : T.Space) (g : Points F (r + 1)) :
    cuspWhittaker F T ψ (y + z) g = cuspWhittaker F T ψ y g + cuspWhittaker F T ψ z g := by
  have h1 := integrable_coefficientIntegrand F ψ hψ T y g
  have h2 := integrable_coefficientIntegrand F ψ hψ T z g
  have hsum := integral_add h1 h2
  have key : cuspWhittaker F T ψ (y + z) g =
      ∫ q, (Unfolding.coefficientIntegrand F (Scheme F (r + 1)) (upperUnipotent F (r + 1))
          (genericCharacter F r ψ fun _ => 1) (cuspFunction F T y) g q +
        Unfolding.coefficientIntegrand F (Scheme F (r + 1)) (upperUnipotent F (r + 1))
          (genericCharacter F r ψ fun _ => 1) (cuspFunction F T z) g q)
        ∂(normalizedRationalQuotientHaarMeasure F (Scheme F (r + 1))
          (upperUnipotent F (r + 1))) := by
    show ∫ q, Unfolding.coefficientIntegrand F (Scheme F (r + 1)) (upperUnipotent F (r + 1))
        (genericCharacter F r ψ fun _ => 1) (cuspFunction F T (y + z)) g q
        ∂(normalizedRationalQuotientHaarMeasure F (Scheme F (r + 1))
          (upperUnipotent F (r + 1))) = _
    congr 1
    funext q
    simp only [Unfolding.coefficientIntegrand, cuspFunction_add, Pi.add_apply, add_mul]
  exact key.trans hsum

theorem cuspWhittaker_smul {r : ℕ} (ψ : AddChar (Adeles F) ℂ)
    (T : CuspidalOperatorRealization F r) (c : ℂ) (y : T.Space) (g : Points F (r + 1)) :
    cuspWhittaker F T ψ (c • y) g = c * cuspWhittaker F T ψ y g := by
  simp only [cuspWhittaker, generalLinearWhittakerFunction,
    Unfolding.subgroupCharacterCoefficient_eq_integral]
  rw [← integral_const_mul]
  congr 1
  funext q
  simp only [Unfolding.coefficientIntegrand, cuspFunction_smul, Pi.smul_apply, smul_eq_mul,
    mul_assoc]

/-- Right translation of the cusp Whittaker coefficient by a finite adelic element. -/
theorem cuspWhittaker_finiteRepresentation {r : ℕ} (ψ : AddChar (Adeles F) ℂ)
    (T : CuspidalOperatorRealization F r) (d : FiniteAdelicGL F (r + 1)) (y : T.Space)
    (g : Points F (r + 1)) :
    cuspWhittaker F T ψ (T.realization.finiteRepresentation d y) g =
      cuspWhittaker F T ψ y (g * (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm
        (AdelicGL.ofFinite F (r + 1) d)) := by
  simp only [cuspWhittaker, generalLinearWhittakerFunction,
    Unfolding.subgroupCharacterCoefficient_eq_integral]
  congr 1
  funext q
  simp only [Unfolding.coefficientIntegrand, cuspFunction_finiteRepresentation, mul_assoc]

/-- The linear functional `y ↦ W_y(g)`. -/
def whittakerFunctional {r : ℕ} (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (T : CuspidalOperatorRealization F r)
    (g : Points F (r + 1)) : Module.Dual ℂ T.Space where
  toFun y := cuspWhittaker F T ψ y g
  map_add' y z := cuspWhittaker_add F ψ hψ T y z g
  map_smul' c y := cuspWhittaker_smul F ψ T c y g

open Langlands.Unramified Langlands.Unramified.MinusculeCosets
open Langlands.Whittaker.UpperUnipotentCharacter (adjacentUnit)

/-- An additive character takes sums to products. -/
theorem addChar_map_sum {A M I : Type*} [AddCommMonoid A] [CommMonoid M] (χ : AddChar A M)
    (s : Finset I) (f : I → A) : χ (∑ i ∈ s, f i) = ∏ i ∈ s, χ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

local instance uwfpLocalValuativeRel (v : FinitePlace F) : ValuativeRel (FiniteCompletion F v) :=
  (CompletionPadic.padicField v).canonicalTopologicalData.valuativeRel

omit [CompactSpace (AdeleQuotient F)] in
/-- On points supported at `v` by a unipotent matrix, the generic character of `ψ` is the
standard character of the component `ψ_v`. -/
theorem genericCharacter_localPoint {r : ℕ}
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)) (v : FinitePlace F)
    (ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v))
    (hψv : ClassField.Global.RelativeWeilGroup.IsCanonicalFiniteAdditiveComponent ψ v ψv)
    (u : GeneralLinear.upperUnipotent (r + 1) (CompletionPadic.padicField v).Carrier) :
    genericCharacter F r ψ.complex (fun _ => 1)
        ⟨localPoint F v u.val, localPoint_mem_unipotentAdelic F v u.val u.property⟩ =
      (@Whittaker.standardCharacter _ _
        (CompletionPadic.padicField v).canonicalTopologicalData.topology ψv r u : ℂ) := by
  classical
  rw [@Whittaker.standardCharacter_apply _ _
    (CompletionPadic.padicField v).canonicalTopologicalData.topology ψv r u]
  change ψ.complex (∑ i : Fin r, algebraMap F (Adeles F) 1 *
    ((GeneralLinearGroupPoints.adelicEquiv F (r + 1) (localPoint F v u.val) :
      Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)) i.castSucc i.succ)) = _
  rw [MulEquiv.apply_symm_apply, map_one]
  simp only [one_mul]
  rw [addChar_map_sum, addChar_map_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [ofFinite_localInclusion_apply_of_ne F v u.val (Fin.castSucc_lt_succ (i := i)).ne]
  exact congrArg (fun z : Circle => (z : ℂ)) (hψv _).symm

/-- For `g` trivial at `v`, the functional `y ↦ W_y(g)` is `θ`-equivariant for the local
action at `v`, when `θ` is the generic character on points supported at `v`. -/
theorem whittakerFunctional_mem {r : ℕ} (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (T : CuspidalOperatorRealization F r)
    (v : FinitePlace F) (g : Points F (r + 1)) (hg : finiteComponent F (r + 1) v g = 1)
    {θ : GeneralLinear.upperUnipotent (r + 1) (CompletionPadic.padicField v).Carrier →* ℂˣ}
    (hθg : ∀ u : GeneralLinear.upperUnipotent (r + 1) (CompletionPadic.padicField v).Carrier,
      genericCharacter F r ψ (fun _ => 1)
        ⟨localPoint F v u.val, localPoint_mem_unipotentAdelic F v u.val u.property⟩ = θ u) :
    whittakerFunctional F ψ hψ T g ∈
      Whittaker.functionals (GeneralLinear.upperUnipotent (r + 1)
        (CompletionPadic.padicField v).Carrier) θ (T.realization.localRepresentation v) := by
  intro u y
  change cuspWhittaker F T ψ (T.realization.finiteRepresentation
      (FiniteAdelicGL.localInclusion F (r + 1) v u.val) y) g = (θ u : ℂ) * cuspWhittaker F T ψ y g
  rw [cuspWhittaker_finiteRepresentation]
  have hc : g * localPoint F v u.val =
      ((⟨localPoint F v u.val, localPoint_mem_unipotentAdelic F v u.val u.property⟩ :
        unipotentAdelic F (r + 1)) : Points F (r + 1)) * g :=
    commute_localPoint F v g hg u.val
  rw [hc, Unfolding.cuspWhittaker_mul_left F T ψ hψ y _ g, hθg]

/-- Factorization at `v` for a vector spherical at `v`, for a character `θ` given by the
generic character on points supported at `v`. -/
theorem cuspWhittaker_mul_localPoint {r : ℕ} (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (T : CuspidalOperatorRealization F r)
    (P : CuspidalSpectralPresentation.{u, uQ} T) (v : FinitePlace F)
    (hvP : v ∉ P.exceptional) (x : T.Space)
    (hx : ∀ k ∈ FiniteAdelicGL.localIntegral F (r + 1) v,
      T.realization.finiteRepresentation (FiniteAdelicGL.localInclusion F (r + 1) v k) x = x)
    (a : Fin (r + 1) → ℂˣ)
    (ha : Eigenvalues.ofTuple a = P.spectralSystem.eigenvalues v hvP)
    {θ : GeneralLinear.upperUnipotent (r + 1) (CompletionPadic.padicField v).Carrier →* ℂˣ}
    (hθK : IsIntegrallyTrivial
      (ValuativeRel.valuation (CompletionPadic.padicField v).Carrier) θ)
    (hθ : ∀ i : Fin r, ∃ z : (CompletionPadic.padicField v).Carrier,
      ValuativeRel.valuation (CompletionPadic.padicField v).Carrier z *
        ValuativeRel.valuation (CompletionPadic.padicField v).Carrier
          ((CompletionPadic.padicField v).canonicalTopologicalData.uniformizerUnit :
            (CompletionPadic.padicField v).Carrier) ≤ 1 ∧ θ (adjacentUnit i z) ≠ 1)
    (g : Points F (r + 1)) (hg : finiteComponent F (r + 1) v g = 1)
    (hθg : ∀ u : GeneralLinear.upperUnipotent (r + 1) (CompletionPadic.padicField v).Carrier,
      genericCharacter F r ψ (fun _ => 1)
        ⟨localPoint F v u.val, localPoint_mem_unipotentAdelic F v u.val u.property⟩ = θ u)
    {ϖ : (CompletionPadic.padicField v).Carrierˣ}
    (hϖ : IsUniformizingElement
      (ValuativeRel.valuation (CompletionPadic.padicField v).Carrier) ϖ)
    (h : FiniteLocalGL F (r + 1) v) :
    cuspWhittaker F T ψ x (g * localPoint F v h) = cuspWhittaker F T ψ x g *
      sphericalWhittaker hϖ θ
        (CompletionPadic.padicField v).canonicalTopologicalData.residueCardinality a h := by
  let ℓ : Whittaker.functionals (GeneralLinear.upperUnipotent (r + 1)
      (CompletionPadic.padicField v).Carrier) θ (T.realization.localRepresentation v) :=
    ⟨whittakerFunctional F ψ hψ T g, whittakerFunctional_mem F ψ hψ T v g hg hθg⟩
  have hxK : x ∈ fixedVectors (T.realization.localRepresentation v)
      (Correspondence.sphericalSubgroup (CompletionPadic.padicField v) r) := fun k =>
    hx k.val ((SetLike.ext_iff.mp (FiniteAdelicGL.localIntegral_eq_sphericalSubgroup F v r)
      k.val).mpr k.property)
  let b : fixedVectors (T.realization.localRepresentation v)
      (Correspondence.sphericalSubgroup (CompletionPadic.padicField v) r) := ⟨x, hxK⟩
  have key := coefficientMap_eq_smul_of_corner (CompletionPadic.padicField v)
    (T.realization.localRepresentation v) (T.realization.localRepresentation_isSmooth_canonical v)
    a b (fun i => (P.corner_eq_smul v hvP b i).trans
      (congrArg (fun s => standardHeckeScalar (CompletionPadic.padicField v) s i • b) ha.symm))
    hθK hθ ℓ hϖ
  have e := congrFun key h
  change cuspWhittaker F T ψ (T.realization.finiteRepresentation
      (FiniteAdelicGL.localInclusion F (r + 1) v h) x) g =
    cuspWhittaker F T ψ x g * sphericalWhittaker hϖ θ
      (CompletionPadic.padicField v).canonicalTopologicalData.residueCardinality a h at e
  rw [cuspWhittaker_finiteRepresentation] at e
  exact e

end Global

open Langlands.Unramified.MinusculeCosets in
open Langlands.Whittaker in
/-- **Factorization of global Whittaker functions at an unramified place** (Cogdell 2004,
§2.2, p.206; Shintani 1976). -/
theorem unramifiedWhittakerFactorization :
    UnramifiedWhittakerFactorizationStatement.{u, uQ} := by
  intro F _ _ _ ψ hψF r T P S hP hS x hxS v hv ψv hψv ϖ hϖ a ha g hg h ιh q
  have hvP : v ∉ P.exceptional := fun hvP => hv (hP hvP)
  have hψ := isStandardAdditiveCharacter_complex F ψ hψF
  have hψi := Unfolding.isStandardAdditiveCharacter_inv F ψ.complex hψ
  obtain ⟨ψz, hψz, h0⟩ := hS v hv
  have hz := RankinSelberg.HighlyRamified.hasIntegerConductor_of_additiveConductor_eq_zero
    (CompletionPadic.padicField v) ψz h0
  have hvz : ∀ t, ψv t = ψz t := fun t => (hψv t).trans (hψz t).symm
  let := (CompletionPadic.padicField v).canonicalTopologicalData.topology
  let := (CompletionPadic.padicField v).canonicalTopologicalData.valuativeRel
  have hint : Conductor.HasIntegerConductor ψv :=
    ⟨fun t ht => (hvz t).trans (hz.1 t ht),
      fun t ht => hz.2 t fun y hy => (hvz _).symm.trans (ht y hy)⟩
  have hu := Langlands.Unramified.uniformizerUnit_isUniformizingElement
    (CompletionPadic.padicField v)
  have hθi := Conductor.exists_adjacentUnit_ne_one hint hu r
  refine ⟨?_, ?_⟩
  · refine cuspWhittaker_mul_localPoint F ψ.complex hψ T P v hvP x (hxS v hv) a ha
      (isIntegrallyTrivial_standardCharacter hint.1 r) (fun i => ?_) g hg
      (genericCharacter_localPoint F ψ v ψv hψv) hϖ h
    obtain ⟨z, hz1, hz2⟩ := hθi i
    refine ⟨z, hz1, fun e => hz2 ?_⟩
    change (standardCharacter ψv r (UpperUnipotentCharacter.adjacentUnit i z))⁻¹ = 1
    rw [e, inv_one]
  · refine cuspWhittaker_mul_localPoint F ψ.complex⁻¹ hψi T P v hvP x (hxS v hv) a ha
      (isIntegrallyTrivial_inverseStandardCharacter hint.1 r) hθi g hg (fun u => ?_) hϖ h
    rw [genericCharacter_inv, genericCharacter_localPoint F ψ v ψv hψv u]
    exact (Units.val_inv_eq_inv_val _).symm

end Langlands.Global.RankinSelbergGlobal.UnramifiedWhittaker
