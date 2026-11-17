import Langlands.Automorphic.ContragredientHeckeTransfer
import Langlands.Global.RankinSelberg.UnramifiedWhittakerFactorizationProof
import Langlands.Global.RankinSelberg.UnequalDualEulerFactorizationReduction
import Langlands.Global.RankinSelberg.ContragredientDualSpherical
import Langlands.Global.RankinSelberg.UnfoldingDualGL
import Langlands.Representation.Conductor.SphericalDualParameters
import Langlands.Representation.Whittaker.DualTransform

/-! # Splitting of dual Whittaker functions at an unramified place, through the contragredient

See the paired Markdown for the statements and the route.
-/

noncomputable section
universe u uQ
open NumberField
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.ContragredientDualSplit

open Langlands.GeneralLinear Langlands.GeneralLinear.Iwasawa Langlands.GeneralLinear.Spherical
open Langlands.Conductor

/-! ### Local duality of spherical Whittaker functions -/

section Local

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation K Γ₀} {n : ℕ} {ϖ : Kˣ} (hϖ : IsUniformizingElement v ϖ) (q : ℕ)

/-- **Local duality.** If `θ` and `θ'` are integrally trivial and `θ` composed with the
reflection `u ↦ w₀ ᵗu⁻¹ w₀` is `θ'`, then `W°_θ(w₀ ᵗg⁻¹; x) = W°_θ'(g; x⁻¹)`. -/
theorem sphericalWhittaker_weylLong_mul_inverseTranspose
    {θ θ' : GeneralLinear.upperUnipotent (n + 1) K →* ℂˣ} (hθ : IsIntegrallyTrivial v θ)
    (hθ' : IsIntegrallyTrivial v θ')
    (hrefl : ∀ u, θ (Whittaker.reflectedUnipotent u) = θ' u) (x : Fin (n + 1) → ℂˣ)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) K) :
    sphericalWhittaker hϖ θ q x (weylLong (n + 1) K * inverseTranspose (n + 1) K g) =
      sphericalWhittaker hϖ θ' q x⁻¹ g := by
  let f : Matrix.GeneralLinearGroup (Fin (n + 1)) K → ℂ := fun g =>
    sphericalWhittaker hϖ θ q x (weylLong (n + 1) K * inverseTranspose (n + 1) K g)
  have htorus : ∀ lam : Fin (n + 1) → ℤ, f (torus ϖ lam) =
      if Antitone lam then halfModulus q lam * satakeSchur x⁻¹ lam else 0 := by
    intro lam
    change sphericalWhittaker hϖ θ q x
      (weylLong (n + 1) K * inverseTranspose (n + 1) K (torus ϖ lam)) = _
    rw [inverseTranspose_torus_eq]
    have hw : weylLong (n + 1) K * torus ϖ (fun i => -lam i) =
        torus ϖ (dualWeight lam) * weylLong (n + 1) K := by
      have hd : torus ϖ (dualWeight lam) =
          weylLong (n + 1) K * torus ϖ (fun i => -lam i) * weylLong (n + 1) K :=
        (weylLong_mul_torus_mul_weylLong (F := K) (ϖ := ϖ) (fun i => -lam i)).symm
      rw [hd, mul_assoc _ (weylLong (n + 1) K), weylLong_mul_self, mul_one]
    rw [hw, sphericalWhittaker_mul_integral hϖ q x hθ _
      weylLong_mem_integralSubgroup_of_valuation, sphericalWhittaker_torus hϖ q x hθ]
    simp only [antitone_dualWeight_iff, halfModulus_dualWeight]
    split_ifs with hlam
    · rw [satakeSchur_inv x hlam]
    · rfl
  have hmem : f ∈ (Whittaker.equivariantFunctions (GeneralLinear.upperUnipotent (n + 1) K) θ').toSubmodule := by
    intro u g
    have e : weylLong (n + 1) K * inverseTranspose (n + 1) K (u.val * g) =
        (Whittaker.reflectedUnipotent u).val *
          (weylLong (n + 1) K * inverseTranspose (n + 1) K g) := by
      rw [Whittaker.reflectedUnipotent_val, map_mul]
      calc weylLong (n + 1) K * (inverseTranspose (n + 1) K u.val * inverseTranspose (n + 1) K g)
          = (weylLong (n + 1) K * inverseTranspose (n + 1) K u.val) *
              ((weylLong (n + 1) K * weylLong (n + 1) K) * inverseTranspose (n + 1) K g) := by
            rw [weylLong_mul_self, one_mul, mul_assoc]
        _ = _ := by simp only [mul_assoc]
    change sphericalWhittaker hϖ θ q x (weylLong (n + 1) K * inverseTranspose (n + 1) K (u.val * g))
      = _
    rw [e, sphericalWhittaker_mem hϖ q x hθ, hrefl]
  have hK : ∀ g, ∀ k ∈ integralSubgroup v.integer n, f (g * k) = f g := by
    intro g k hk
    change sphericalWhittaker hϖ θ q x (weylLong (n + 1) K * inverseTranspose (n + 1) K (g * k)) =
      sphericalWhittaker hϖ θ q x (weylLong (n + 1) K * inverseTranspose (n + 1) K g)
    rw [map_mul, ← mul_assoc]
    exact sphericalWhittaker_mul_integral hϖ q x hθ _
      (inverseTranspose_mem_integralSubgroup_of_valuation hk)
  have hzero : ∀ lam : Fin (n + 1) → ℤ, ¬ Antitone lam → f (torus ϖ lam) = 0 := by
    intro lam hlam
    rw [htorus]; exact ite_eq_right_iff.mpr fun h => absurd h hlam
  have h := eq_cellFunction hϖ hθ' hmem hK hzero
  change f g = _
  rw [h]
  exact congrFun (cellFunction_congr hϖ θ' fun lam hlam => by rw [htorus]; simp [hlam]) g

end Local

/-! ### Global points -/

section Points

local instance dualSplitSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance dualSplitSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F]

/-- The component at `v` of the long Weyl element of `GL_n(𝔸)` is the long Weyl element of
`GL_n(F_v)`. -/
theorem finiteComponent_weylLong (n : ℕ) (v : FinitePlace F) :
    finiteComponent F n v ((GeneralLinearGroupPoints.adelicEquiv F n).symm
      (GeneralLinear.weylLong n (Adeles F))) = GeneralLinear.weylLong n (FiniteCompletion F v) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [finiteComponent_apply, MulEquiv.apply_symm_apply, GeneralLinear.weylLong_entry,
    GeneralLinear.weylLong_entry]
  split_ifs <;> rfl

/-- `(w ᵗg⁻¹)_v = w_v` when `g_v = 1`. -/
theorem finiteComponent_dualPoint {n : ℕ} (v : FinitePlace F) {g : Points F n}
    (hg : finiteComponent F n v g = 1) :
    finiteComponent F n v (Unfolding.dualPoint F n g) =
      GeneralLinear.weylLong n (FiniteCompletion F v) := by
  have e : finiteComponent F n v (Unfolding.dualPoint F n g) =
      finiteComponent F n v ((GeneralLinearGroupPoints.adelicEquiv F n).symm
        (GeneralLinear.weylLong n (Adeles F))) *
        GeneralLinear.inverseTranspose n _ (finiteComponent F n v g) := by
    simp only [finiteComponent, Unfolding.dualPoint, MulEquiv.apply_symm_apply, map_mul,
      ContragredientDual.finite_inverseTranspose,
      ContragredientDual.localProjection_inverseTranspose]
  rw [e, hg, map_one, mul_one, finiteComponent_weylLong]

/-- `w ᵗ(g ι_v(h))⁻¹ = (w ᵗg⁻¹) ι_v(ᵗh⁻¹)`. -/
theorem dualPoint_mul_localPoint {n : ℕ} (v : FinitePlace F) (g : Points F n)
    (h : FiniteLocalGL F n v) :
    Unfolding.dualPoint F n (g * localPoint F n v h) =
      Unfolding.dualPoint F n g * localPoint F n v (GeneralLinear.inverseTranspose n _ h) := by
  apply (GeneralLinearGroupPoints.adelicEquiv F n).injective
  simp only [Unfolding.dualPoint, MulEquiv.apply_symm_apply, map_mul,
    LocalPointFactorization.adelicEquiv_localPoint, ContragredientDual.inverseTranspose_ofFinite,
    ContragredientDual.inverseTranspose_localInclusion, mul_assoc]

/-- **Splitting of a dual function at `v`.** If `W(g ι_v(h)) = W(g) φ(h)` whenever `g_v = 1`,
and `φ(w_v) = 1`, then the dual function `W̃(g) = W(w ᵗg⁻¹)` satisfies
`W̃(g ι_v(h)) = W̃(g) φ(w_v ᵗh⁻¹)` whenever `g_v = 1`. -/
theorem dualFunction_mul_localPoint {n : ℕ} (v : FinitePlace F) {W : Points F n → ℂ}
    {φ : FiniteLocalGL F n v → ℂ}
    (hW : ∀ g, finiteComponent F n v g = 1 → ∀ h, W (g * localPoint F n v h) = W g * φ h)
    (hφ : φ (GeneralLinear.weylLong n (FiniteCompletion F v)) = 1)
    {g : Points F n} (hg : finiteComponent F n v g = 1) (h : FiniteLocalGL F n v) :
    dualFunction F n W (g * localPoint F n v h) =
      dualFunction F n W g *
        φ (GeneralLinear.weylLong n (FiniteCompletion F v) *
          GeneralLinear.inverseTranspose n _ h) := by
  obtain ⟨p, hp, e⟩ : ∃ p : Points F n, finiteComponent F n v p = 1 ∧
      Unfolding.dualPoint F n g =
        p * localPoint F n v (GeneralLinear.weylLong n (FiniteCompletion F v)) := by
    refine ⟨Unfolding.dualPoint F n g * (localPoint F n v
      (GeneralLinear.weylLong n (FiniteCompletion F v)))⁻¹, ?_, by group⟩
    have h1 := LocalPointFactorization.finiteComponent_mul_inv_localPoint F n v
      (Unfolding.dualPoint F n g)
    rwa [finiteComponent_dualPoint F v hg] at h1
  have hd : dualFunction F n W g = W p := by
    rw [Unfolding.dualFunction_eq, e, hW p hp, hφ, mul_one]
  rw [Unfolding.dualFunction_eq, dualPoint_mul_localPoint, e, mul_assoc,
    ← LocalPointFactorization.localPoint_mul, hW p hp, hd]

end Points

/-! ### Splitting through Hecke scalars -/

section Global

open Langlands.Global Langlands.Automorphic Langlands.Unramified

local instance dualSplitRationalAddCommGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance dualSplitContinuousAddCommGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance dualSplitSmoothAddCommGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance dualSplitFormsAddCommGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance dualSplitStableAddCommGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance dualSplitRealizationAddCommGroup {F : Type u} [Field F] [NumberField F] {n : ℕ}
    (S : OperatorRealization F n) : AddCommGroup S.Space := Submodule.addCommGroup _

/-- Inverting a tuple inverts its multiset of eigenvalues. -/
theorem ofTuple_map_inv {n : ℕ} (a : Fin n → ℂˣ) :
    (Eigenvalues.ofTuple a).map (fun z => z⁻¹) = Eigenvalues.ofTuple a⁻¹ := by
  apply Sym.ext
  simp [Eigenvalues.ofTuple, List.map_ofFn, Function.comp_def]
  exact List.Perm.refl _

variable (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

local instance dualSplitLocalValuativeRel (v : FinitePlace F) :
    ValuativeRel (FiniteCompletion F v) :=
  (CompletionPadic.padicField v).canonicalTopologicalData.valuativeRel
local instance dualSplitLocalTopology (v : FinitePlace F) (m : ℕ) :
    TopologicalSpace (FiniteLocalGL F m v) :=
  (CompletionPadic.padicField v).canonicalGeneralLinearTopology m
local instance dualSplitLocalTopologicalGroup (v : FinitePlace F) (m : ℕ) :
    IsTopologicalGroup (FiniteLocalGL F m v) :=
  (CompletionPadic.padicField v).canonicalGeneralLinearTopologicalGroup m
local instance dualSplitLocalT2 (v : FinitePlace F) (m : ℕ) : T2Space (FiniteLocalGL F m v) :=
  (CompletionPadic.padicField v).canonicalGeneralLinearT2Space m
local instance dualSplitLocalMeasurable (v : FinitePlace F) (m : ℕ) :
    MeasurableSpace (FiniteLocalGL F m v) :=
  borel _
local instance dualSplitLocalBorel (v : FinitePlace F) (m : ℕ) :
    BorelSpace (FiniteLocalGL F m v) := ⟨rfl⟩

open Langlands.Unramified.MinusculeCosets in
open Langlands.Whittaker.UpperUnipotentCharacter (adjacentUnit) in
/-- Factorization at `v` for a vector spherical at `v` whose spherical vectors at `v` have the
standard Hecke scalars of `a`: the same statement as
`UnramifiedWhittaker.cuspWhittaker_mul_localPoint`, with the hypothesis on the Hecke scalars
in place of a spectral presentation. -/
theorem cuspWhittaker_mul_localPoint_of_corner {r : ℕ} (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (T : CuspidalOperatorRealization F r)
    (v : FinitePlace F) (x : T.Space)
    (hx : ∀ k ∈ FiniteAdelicGL.localIntegral F (r + 1) v,
      T.realization.finiteRepresentation (FiniteAdelicGL.localInclusion F (r + 1) v k) x = x)
    (a : Fin (r + 1) → ℂˣ)
    (hT : ∀ (b : fixedVectors (T.realization.localRepresentation v)
        (sphericalOpenSubgroup (CompletionPadic.padicField v) r).toSubgroup) (i : Fin (r + 2)),
      PairedHecke.corner (CompletionPadic.padicField v) (T.realization.localRepresentation v)
          (T.realization.localRepresentation_isSmooth_canonical v)
          (standardHeckeElement (CompletionPadic.padicField v) r i) b =
        standardHeckeScalar (CompletionPadic.padicField v) (Eigenvalues.ofTuple a) i • b)
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
        ⟨UnramifiedWhittaker.localPoint F v u.val,
          UnramifiedWhittaker.localPoint_mem_unipotentAdelic F v u.val u.property⟩ = θ u)
    {ϖ : (CompletionPadic.padicField v).Carrierˣ}
    (hϖ : IsUniformizingElement
      (ValuativeRel.valuation (CompletionPadic.padicField v).Carrier) ϖ)
    (h : FiniteLocalGL F (r + 1) v) :
    cuspWhittaker F T ψ x (g * localPoint F (r + 1) v h) = cuspWhittaker F T ψ x g *
      sphericalWhittaker hϖ θ
        (CompletionPadic.padicField v).canonicalTopologicalData.residueCardinality a h := by
  let ℓ : Whittaker.functionals (GeneralLinear.upperUnipotent (r + 1)
      (CompletionPadic.padicField v).Carrier) θ (T.realization.localRepresentation v) :=
    ⟨UnramifiedWhittaker.whittakerFunctional F ψ hψ T g,
      UnramifiedWhittaker.whittakerFunctional_mem F ψ hψ T v g hg hθg⟩
  have hxK : x ∈ fixedVectors (T.realization.localRepresentation v)
      (Correspondence.sphericalSubgroup (CompletionPadic.padicField v) r) := fun k =>
    hx k.val ((SetLike.ext_iff.mp (FiniteAdelicGL.localIntegral_eq_sphericalSubgroup F v r)
      k.val).mpr k.property)
  let b : fixedVectors (T.realization.localRepresentation v)
      (Correspondence.sphericalSubgroup (CompletionPadic.padicField v) r) := ⟨x, hxK⟩
  have key := UnramifiedWhittaker.coefficientMap_eq_smul_of_corner
    (CompletionPadic.padicField v)
    (T.realization.localRepresentation v) (T.realization.localRepresentation_isSmooth_canonical v)
    a b (hT b) hθK hθ ℓ hϖ
  have e := congrFun key h
  change cuspWhittaker F T ψ (T.realization.finiteRepresentation
      (FiniteAdelicGL.localInclusion F (r + 1) v h) x) g =
    cuspWhittaker F T ψ x g * sphericalWhittaker hϖ θ
      (CompletionPadic.padicField v).canonicalTopologicalData.residueCardinality a h at e
  rw [UnramifiedWhittaker.cuspWhittaker_finiteRepresentation] at e
  exact e

open Langlands.Whittaker in
/-- **Splitting at `v` from Hecke scalars.** The two halves of
`UnramifiedWhittakerFactorizationStatement` at the uniformizer `placeUniformizer v`, for a
vector spherical outside `S` whose spherical vectors at `v` have the standard Hecke scalars
of `a`, when `ψ_v` has conductor `𝒪_v`. -/
theorem whittaker_split_of_corner (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψF : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) {r : ℕ}
    (T : CuspidalOperatorRealization F r) {S : Finset (FinitePlace F)}
    {x : T.Space} (hx : IsSphericalOutside F T S x) {v : FinitePlace F} (hv : v ∉ S)
    {ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v)}
    (hψv : ClassField.Global.RelativeWeilGroup.IsCanonicalFiniteAdditiveComponent ψ v ψv)
    (h0 : (CompletionPadic.padicField v).canonicalTopologicalData.additiveConductor ψv = 0)
    (a : Fin (r + 1) → ℂˣ)
    (hT : ∀ (b : fixedVectors (T.realization.localRepresentation v)
        (sphericalOpenSubgroup (CompletionPadic.padicField v) r).toSubgroup) (i : Fin (r + 2)),
      PairedHecke.corner (CompletionPadic.padicField v) (T.realization.localRepresentation v)
          (T.realization.localRepresentation_isSmooth_canonical v)
          (standardHeckeElement (CompletionPadic.padicField v) r i) b =
        standardHeckeScalar (CompletionPadic.padicField v) (Eigenvalues.ofTuple a) i • b) :
    (∀ g, finiteComponent F (r + 1) v g = 1 → ∀ h' : FiniteLocalGL F (r + 1) v,
      cuspWhittaker F T ψ.complex x (g * localPoint F (r + 1) v h') =
        cuspWhittaker F T ψ.complex x g * UnequalDualEuler.sphStd v ψv r a h') ∧
    (∀ g, finiteComponent F (r + 1) v g = 1 → ∀ h' : FiniteLocalGL F (r + 1) v,
      cuspWhittaker F T ψ.complex⁻¹ x (g * localPoint F (r + 1) v h') =
        cuspWhittaker F T ψ.complex⁻¹ x g * UnequalDualEuler.sphInv v ψv r a h') := by
  have hψ := UnramifiedWhittaker.isStandardAdditiveCharacter_complex F ψ hψF
  have hψi := Unfolding.isStandardAdditiveCharacter_inv F ψ.complex hψ
  have hint := RankinSelberg.HighlyRamified.hasIntegerConductor_of_additiveConductor_eq_zero
    (CompletionPadic.padicField v) ψv h0
  let := (CompletionPadic.padicField v).canonicalTopologicalData.topology
  let := (CompletionPadic.padicField v).canonicalTopologicalData.valuativeRel
  have hu := Langlands.Unramified.uniformizerUnit_isUniformizingElement
    (CompletionPadic.padicField v)
  have hθi := Conductor.exists_adjacentUnit_ne_one hint hu r
  refine ⟨fun g hg h' => ?_, fun g hg h' => ?_⟩
  · refine cuspWhittaker_mul_localPoint_of_corner F ψ.complex hψ T v x (hx v hv) a hT
      (isIntegrallyTrivial_standardCharacter hint.1 r) (fun i => ?_) g hg
      (UnramifiedWhittaker.genericCharacter_localPoint F ψ v ψv hψv)
      (LocalPointFactorization.isUniformizingElement_canonical v) h'
    obtain ⟨z, hz1, hz2⟩ := hθi i
    refine ⟨z, hz1, fun e => hz2 ?_⟩
    change (standardCharacter ψv r (UpperUnipotentCharacter.adjacentUnit i z))⁻¹ = 1
    rw [e, inv_one]
  · refine cuspWhittaker_mul_localPoint_of_corner F ψ.complex⁻¹ hψi T v x (hx v hv) a hT
      (isIntegrallyTrivial_inverseStandardCharacter hint.1 r) hθi g hg (fun u => ?_)
      (LocalPointFactorization.isUniformizingElement_canonical v) h'
    rw [UnramifiedWhittaker.genericCharacter_inv,
      UnramifiedWhittaker.genericCharacter_localPoint F ψ v ψv hψv u]
    exact (Units.val_inv_eq_inv_val _).symm

variable {F}

omit [CompactSpace (AdeleQuotient F)] in
/-- `W°(w ᵗh⁻¹; a⁻¹) = W°⁻(h; a)` at `v`, for `ψ_v` of conductor `𝒪_v`. -/
theorem sphStd_inv_weylLong_mul_inverseTranspose {v : FinitePlace F}
    {ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v)}
    (h0 : (CompletionPadic.padicField v).canonicalTopologicalData.additiveConductor ψv = 0)
    (r : ℕ) (a : Fin (r + 1) → ℂˣ) (h : FiniteLocalGL F (r + 1) v) :
    UnequalDualEuler.sphStd v ψv r a⁻¹ (GeneralLinear.weylLong (r + 1) (FiniteCompletion F v) *
        GeneralLinear.inverseTranspose (r + 1) (FiniteCompletion F v) h) =
      UnequalDualEuler.sphInv v ψv r a h := by
  let _ := (CompletionPadic.padicField v).canonicalTopologicalData.topology
  have hθ := isIntegrallyTrivial_standardCharacter
    (UnequalDualEuler.integer_trivial_of_conductor h0) r
  have hθ' := isIntegrallyTrivial_inverseStandardCharacter
    (UnequalDualEuler.integer_trivial_of_conductor h0) r
  have e := sphericalWhittaker_weylLong_mul_inverseTranspose (LocalPointFactorization.isUniformizingElement_canonical v)
    (CompletionPadic.padicField v).canonicalTopologicalData.residueCardinality hθ hθ'
    (fun u => Whittaker.standardCharacter_reflected _ u) a⁻¹ h
  rw [inv_inv] at e
  exact e

omit [CompactSpace (AdeleQuotient F)] in
/-- `W°⁻(w ᵗh⁻¹; a⁻¹) = W°(h; a)` at `v`, for `ψ_v` of conductor `𝒪_v`. -/
theorem sphInv_inv_weylLong_mul_inverseTranspose {v : FinitePlace F}
    {ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v)}
    (h0 : (CompletionPadic.padicField v).canonicalTopologicalData.additiveConductor ψv = 0)
    (r : ℕ) (a : Fin (r + 1) → ℂˣ) (h : FiniteLocalGL F (r + 1) v) :
    UnequalDualEuler.sphInv v ψv r a⁻¹ (GeneralLinear.weylLong (r + 1) (FiniteCompletion F v) *
        GeneralLinear.inverseTranspose (r + 1) (FiniteCompletion F v) h) =
      UnequalDualEuler.sphStd v ψv r a h := by
  let _ := (CompletionPadic.padicField v).canonicalTopologicalData.topology
  have hθ := isIntegrallyTrivial_standardCharacter
    (UnequalDualEuler.integer_trivial_of_conductor h0) r
  have hθ' := isIntegrallyTrivial_inverseStandardCharacter
    (UnequalDualEuler.integer_trivial_of_conductor h0) r
  have e := sphericalWhittaker_weylLong_mul_inverseTranspose (LocalPointFactorization.isUniformizingElement_canonical v)
    (CompletionPadic.padicField v).canonicalTopologicalData.residueCardinality hθ' hθ
    (fun u => Whittaker.inverseStandardCharacter_reflected _ u) a⁻¹ h
  rw [inv_inv] at e
  exact e

omit [CompactSpace (AdeleQuotient F)] in
/-- `W°(w_v; a) = 1`. -/
theorem sphStd_weylLong {v : FinitePlace F}
    {ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v)}
    (h0 : (CompletionPadic.padicField v).canonicalTopologicalData.additiveConductor ψv = 0)
    (r : ℕ) (a : Fin (r + 1) → ℂˣ) :
    UnequalDualEuler.sphStd v ψv r a (GeneralLinear.weylLong (r + 1) (FiniteCompletion F v)) =
      1 := by
  let _ := (CompletionPadic.padicField v).canonicalTopologicalData.topology
  have hθ := isIntegrallyTrivial_standardCharacter
    (UnequalDualEuler.integer_trivial_of_conductor h0) r
  have e := sphericalWhittaker_mul_integral (LocalPointFactorization.isUniformizingElement_canonical v)
    (CompletionPadic.padicField v).canonicalTopologicalData.residueCardinality a hθ 1
    weylLong_mem_integralSubgroup_of_valuation
  rw [one_mul] at e
  exact e.trans (sphericalWhittaker_one _ _ _ hθ)

omit [CompactSpace (AdeleQuotient F)] in
/-- `W°⁻(w_v; a) = 1`. -/
theorem sphInv_weylLong {v : FinitePlace F}
    {ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v)}
    (h0 : (CompletionPadic.padicField v).canonicalTopologicalData.additiveConductor ψv = 0)
    (r : ℕ) (a : Fin (r + 1) → ℂˣ) :
    UnequalDualEuler.sphInv v ψv r a (GeneralLinear.weylLong (r + 1) (FiniteCompletion F v)) =
      1 := by
  let _ := (CompletionPadic.padicField v).canonicalTopologicalData.topology
  have hθ := isIntegrallyTrivial_inverseStandardCharacter
    (UnequalDualEuler.integer_trivial_of_conductor h0) r
  have e := sphericalWhittaker_mul_integral (LocalPointFactorization.isUniformizingElement_canonical v)
    (CompletionPadic.padicField v).canonicalTopologicalData.residueCardinality a hθ 1
    weylLong_mem_integralSubgroup_of_valuation
  rw [one_mul] at e
  exact e.trans (sphericalWhittaker_one _ _ _ hθ)

variable (F)

/-- **Splitting of the dual Whittaker functions at `v`.** Let `Td` realize the contragredient
of `T`, let `Pd` present `Td`, and let `a` be a Satake parameter of the presented spectrum of
`Td` at a place `v ∉ S` where `ψ_v` has conductor `𝒪_v`. For `x` spherical outside `S`, the
dual `W̃(g) = W(w ᵗg⁻¹)` of the `ψ`-Whittaker function of `x` splits at `v` with factor
`W°⁻(·; a)`, and the dual of its `ψ⁻¹`-Whittaker function with factor `W°(·; a)`. -/
theorem dualWhittaker_split (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψF : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) {r : ℕ}
    {T Td : CuspidalOperatorRealization F r}
    (hTd : Td.realization.IsContragredientOf T.realization)
    (Pd : CuspidalSpectralPresentation.{u, uQ} Td) {S : Finset (FinitePlace F)}
    (hPd : Pd.exceptional ⊆ S)
    {x : T.Space} (hx : IsSphericalOutside F T S x) {v : FinitePlace F} (hv : v ∉ S)
    {ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v)}
    (hψv : ClassField.Global.RelativeWeilGroup.IsCanonicalFiniteAdditiveComponent ψ v ψv)
    (h0 : (CompletionPadic.padicField v).canonicalTopologicalData.additiveConductor ψv = 0)
    {a : Fin (r + 1) → ℂˣ}
    (ha : Unramified.Eigenvalues.ofTuple a =
      Pd.spectralSystem.eigenvalues v (fun hvP => hv (hPd hvP))) :
    (∀ g, finiteComponent F (r + 1) v g = 1 → ∀ h' : FiniteLocalGL F (r + 1) v,
      dualFunction F (r + 1) (cuspWhittaker F T ψ.complex x) (g * localPoint F (r + 1) v h') =
        dualFunction F (r + 1) (cuspWhittaker F T ψ.complex x) g *
          UnequalDualEuler.sphInv v ψv r a h') ∧
    (∀ g, finiteComponent F (r + 1) v g = 1 → ∀ h' : FiniteLocalGL F (r + 1) v,
      dualFunction F (r + 1) (cuspWhittaker F T ψ.complex⁻¹ x)
          (g * localPoint F (r + 1) v h') =
        dualFunction F (r + 1) (cuspWhittaker F T ψ.complex⁻¹ x) g *
          UnequalDualEuler.sphStd v ψv r a h') := by
  have hs : (Pd.spectralSystem.eigenvalues v (fun hvP => hv (hPd hvP))).map (fun z => z⁻¹) =
      Eigenvalues.ofTuple a⁻¹ := by
    rw [← ha]
    exact ofTuple_map_inv a
  have hT : ∀ (b : fixedVectors (T.realization.localRepresentation v)
        (sphericalOpenSubgroup (CompletionPadic.padicField v) r).toSubgroup) (i : Fin (r + 2)),
      PairedHecke.corner (CompletionPadic.padicField v) (T.realization.localRepresentation v)
          (T.realization.localRepresentation_isSmooth_canonical v)
          (standardHeckeElement (CompletionPadic.padicField v) r i) b =
        standardHeckeScalar (CompletionPadic.padicField v) (Eigenvalues.ofTuple a⁻¹) i • b :=
    fun b i => (CuspidalOperatorRealization.corner_eq_smul_of_contragredient_presentation T Td
      hTd Pd v (fun hvP => hv (hPd hvP)) b i).trans
        (congrArg (fun s => standardHeckeScalar (CompletionPadic.padicField v) s i • b) hs)
  have hsplit := whittaker_split_of_corner F ψ hψF T hx hv hψv h0 a⁻¹ hT
  refine ⟨fun g hg h' => ?_, fun g hg h' => ?_⟩
  · rw [dualFunction_mul_localPoint F v hsplit.1 (sphStd_weylLong h0 r a⁻¹) hg h',
      sphStd_inv_weylLong_mul_inverseTranspose h0 r a h']
  · rw [dualFunction_mul_localPoint F v hsplit.2 (sphInv_weylLong h0 r a⁻¹) hg h',
      sphInv_inv_weylLong_mul_inverseTranspose h0 r a h']

end Global

end Langlands.Global.RankinSelbergGlobal.ContragredientDualSplit
