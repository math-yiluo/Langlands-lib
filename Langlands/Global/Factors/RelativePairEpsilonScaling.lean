import Langlands.Global.Factors.RelativePairEpsilonReduction
import Langlands.Global.Factors.RelativeIsometryDeterminant
import Langlands.Correspondence.ArithmeticEpsilonScaling
import Langlands.Correspondence.HenniartExtensionDeterminant
import Langlands.Representation.RankinSelberg.PairFactorCharacterChangeProof
import Langlands.Representation.RankinSelberg.EqualRankEpsilonCharacterChangeProof
import Langlands.VirtualRepresentation.UnitaryDegreeGenerators
import Langlands.VirtualRepresentation.DescentProof
import Langlands.Representation.Whittaker.PadicCharacterIndependence

/-!
# Change of additive character for the pair epsilon clause

If some
`c q^(-ms)` is both the Weil-side and the GL-side epsilon factor of `(x, y)` and
`(T x, T y)` for one additive character `ψ`, then the same holds for every other
nontrivial additive character `ψ' = ψ^a`, `ψ^a(x) = ψ(ax)`.

On basis pairs both sides change by the same rule: on the Weil side
`ε(s, σ ⊗ τ, ψ^a) = det(σ)(w)^(dim τ) det(τ)(w)^(dim σ) |a|^(N(s - 1/2)) ε(s, σ ⊗ τ, ψ)`
for a Weil element `w` with reciprocity image `a` (Deligne's scaling law,
`ArithmeticEpsilonScaling`), and on the GL side
`ε(s, π × τ, ψ^a) = ω_π(a)^(rk τ) ω_τ(a)^(rk π) |a|^(N(s - 1/2)) ε(s, π × τ, ψ)`
(Cogdell–Piatetski-Shapiro 1994, Lemma 2.1, and the equal-rank analogue of the
Library). Both bilinear epsilon maps therefore change by a correction term built from
determinants (resp. central characters) at `w` (resp. `a`), degrees, `|a|^(-1/2)` and
`ord a`. On the graph of `T` the two corrections agree by the determinant clause
(`pairedLattice_determinant`, for the base reciprocity candidate of the system, which is
geometric) and by preservation of degrees.
-/

noncomputable section

set_option autoImplicit false

universe uF uV uW uP uE

namespace Langlands.VirtualRepresentation

/-- The correction term of the change of additive character, as an integer-bilinear
map with values in `Additive ℂˣ × ℤ`: for a determinant-type additive map `δ`, a degree
`n`, a unit `κ` and an integer `k`, it sends `(x, y)` to
`(δ(x)^(n y) δ(y)^(n x) κ^(n x · n y), n x · n y · k)`. -/
def epsilonCorrection {M : Type*} [AddCommGroup M] (δ : M →+ Additive ℂˣ) (n : M →+ ℤ)
    (κ : ℂˣ) (k : ℤ) : M →ₗ[ℤ] M →ₗ[ℤ] Additive ℂˣ × ℤ :=
  LinearMap.mk₂ ℤ
    (fun x y => (n y • δ x + n x • δ y + (n x * n y) • Additive.ofMul κ, n x * n y * k))
    (fun x x' y => by
      refine Prod.ext ?_ ?_
      · simp only [map_add, Prod.fst_add, add_mul]
        module
      · simp only [map_add, Prod.snd_add]
        ring)
    (fun c x y => by
      refine Prod.ext ?_ ?_
      · simp only [map_zsmul, smul_eq_mul, Prod.smul_fst]
        module
      · simp only [map_zsmul, smul_eq_mul, Prod.smul_snd]
        ring)
    (fun x y y' => by
      refine Prod.ext ?_ ?_
      · simp only [map_add, Prod.fst_add, mul_add]
        module
      · simp only [map_add, Prod.snd_add]
        ring)
    (fun c x y => by
      refine Prod.ext ?_ ?_
      · simp only [map_zsmul, smul_eq_mul, Prod.smul_fst]
        module
      · simp only [map_zsmul, smul_eq_mul, Prod.smul_snd]
        ring)

@[simp]
theorem epsilonCorrection_apply {M : Type*} [AddCommGroup M] (δ : M →+ Additive ℂˣ)
    (n : M →+ ℤ) (κ : ℂˣ) (k : ℤ) (x y : M) :
    epsilonCorrection δ n κ k x y =
      (n y • δ x + n x • δ y + (n x * n y) • Additive.ofMul κ, n x * n y * k) := rfl

/-- Two integer-bilinear maps on integral lattices agreeing on pairs of basis classes
are equal. -/
theorem bilinear_ext {ι κ N : Type*} [AddCommGroup N] [Module ℤ N]
    {Φ Ψ : IntegralLattice ι →ₗ[ℤ] IntegralLattice κ →ₗ[ℤ] N}
    (h : ∀ a b, Φ (generator a) (generator b) = Ψ (generator a) (generator b)) : Φ = Ψ :=
  integral_hom_ext fun a => integral_hom_ext fun b => h a b

end Langlands.VirtualRepresentation

namespace Langlands.VirtualRepresentation.PadicSupercuspidal

open Langlands.RankinSelberg

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance relativePairEpsilonScalingTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance relativePairEpsilonScalingValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance relativePairEpsilonScalingLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

/-- `|a|^(-N/2) = (|a|^(1/2))^(-N)` for the residue-normalized absolute value. -/
theorem normalizedAbs_cpow_neg_half (a : F.Carrierˣ) (N : ℕ) :
    ((F.canonicalTopologicalData.normalizedAbs (a : F.Carrier) : ℝ) : ℂ) ^ (-(N : ℂ) / 2) =
      (((LocalFactor.NonabelianSystem.positiveScale (LocalFactor.PadicAbelian.sqrtNormalizedAbs F a)
        (LocalFactor.PadicAbelian.sqrtNormalizedAbs_pos F a))⁻¹ ^ (N : ℤ) : ℂˣ) : ℂ) := by
  set κ := LocalFactor.PadicAbelian.sqrtNormalizedAbs F a
  have hκ : (0 : ℝ) ≤ κ := κ.2
  rw [← LocalFactor.PadicAbelian.sqrtNormalizedAbs_sq F a]
  have h1 : (-(N : ℂ) / 2) = ((-(N : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h1, ← Complex.ofReal_cpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hκ]
  have h2 : ((2 : ℕ) : ℝ) * (-(N : ℝ) / 2) = -(N : ℝ) := by push_cast; ring
  rw [h2, Real.rpow_neg hκ, Real.rpow_natCast]
  simp only [Units.val_inv_eq_inv_val, LocalFactor.NonabelianSystem.positiveScale,
    zpow_natCast, inv_pow]
  push_cast
  rfl

/-- The central character of a unitary supercuspidal basis class is the central
character of each representative, in the sense of `HasGLCentralCharacter`. -/
theorem hasGLCentralCharacter_of_isUnitaryBasisCentralCharacter {r : ℕ} {hr : 0 < r + 1}
    (A : GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r + 1))
    (hu : (⟨⟨r + 1, hr⟩, A.isoClass⟩ : Supercuspidal.Basis.{uF, uV} F.Carrier) ∈
      Supercuspidal.unitarySet.{uF, uV} F.Carrier)
    {ω : F.Carrierˣ →* ℂˣ}
    (h : IsUnitaryBasisCentralCharacter F ⟨⟨⟨r + 1, hr⟩, A.isoClass⟩, hu⟩ ω) :
    Classification.HasGLCentralCharacter F.Carrier (r + 1) A.obj.representation ω :=
  fun c v => (Henniart.Extension.supercuspidalCentralActsBy_iff F (n := ⟨r + 1, hr⟩) A c (ω c)).mp
    (h c) v

/-- Change of additive character for the JPSS epsilon certificate of two unitary
supercuspidal basis classes (Cogdell and Piatetski-Shapiro 1994, Lemma 2.1, and its
equal-rank analogue), with self-dual measures for `ψ` and `ψ^a`:
`ε(s, π × τ, ψ^a) = ω_π(a)^(rk τ) ω_τ(a)^(rk π) |a|^(N(s - 1/2)) ε(s, π × τ, ψ)`. -/
theorem IsUnitaryBasisPairEpsilonFactor.scale
    {ψ : Correspondence.NontrivialAdditiveCharacter F}
    {ν ν' : Correspondence.LocalAdditiveHaarMeasure F}
    (hν : Correspondence.IsSelfDualMeasure F ψ ν) (a : F.Carrierˣ)
    (hν' : Correspondence.IsSelfDualMeasure F (ψ.scale a) ν')
    {α β : UnitaryBasis.{uF, uV} F} {e : ℂˣ × ℤ}
    (h : IsUnitaryBasisPairEpsilonFactor F ψ ν α β e) :
    IsUnitaryBasisPairEpsilonFactor F (ψ.scale a) ν' α β
      (e.1 * unitaryBasisCentralCharacter F α a ^ ((β.val.1 : ℕ) : ℤ) *
          unitaryBasisCentralCharacter F β a ^ ((α.val.1 : ℕ) : ℤ) *
          (LocalFactor.NonabelianSystem.positiveScale
            (LocalFactor.PadicAbelian.sqrtNormalizedAbs F a)
            (LocalFactor.PadicAbelian.sqrtNormalizedAbs_pos F a))⁻¹ ^
              (((α.val.1 : ℕ) : ℤ) * (β.val.1 : ℕ)),
        e.2 + ((α.val.1 : ℕ) : ℤ) * (β.val.1 : ℕ) *
          F.canonicalTopologicalData.ord (a : F.Carrier)) := by
  have hωα := isUnitaryBasisCentralCharacter_unitaryBasisCentralCharacter F α
  have hωβ := isUnitaryBasisCentralCharacter_unitaryBasisCentralCharacter F β
  generalize unitaryBasisCentralCharacter F α = ωα at hωα ⊢
  generalize unitaryBasisCentralCharacter F β = ωβ at hωβ ⊢
  obtain ⟨⟨⟨_ | r, hr⟩, π⟩, hα⟩ := α
  · exact absurd hr (lt_irrefl 0)
  obtain ⟨⟨⟨_ | t, ht⟩, σ⟩, hβ⟩ := β
  · exact absurd ht (lt_irrefl 0)
  induction π using Quotient.inductionOn with
  | h A =>
    induction σ using Quotient.inductionOn with
    | h B =>
      have hA := hasGLCentralCharacter_of_isUnitaryBasisCentralCharacter F A hα hωα
      have hB := hasGLCentralCharacter_of_isUnitaryBasisCentralCharacter F B hβ hωβ
      change IsPadicSymmetricEpsilonFactor F ψ ν A.obj.representation B.obj.representation e at h
      change IsPadicSymmetricEpsilonFactor F (ψ.scale a) ν' A.obj.representation
        B.obj.representation _
      let νS : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ := ⟨ν, hν⟩
      let νS' : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData (ψ.scale a) :=
        ⟨ν', hν'⟩
      have hchange : ∃ e' : ℂˣ × ℤ, IsPadicSymmetricEpsilonFactor F (ψ.scale a) ν'
          A.obj.representation B.obj.representation e' ∧
          e'.2 = e.2 + ((r + 1) * (t + 1) : ℕ) * F.canonicalTopologicalData.ord (a : F.Carrier) ∧
          (e'.1 : ℂ) = (e.1 : ℂ) * ((ωα a : ℂˣ) : ℂ) ^ (t + 1) * ((ωβ a : ℂˣ) : ℂ) ^ (r + 1) *
            ((F.canonicalTopologicalData.normalizedAbs (a : F.Carrier) : ℝ) : ℂ) ^
              (-(((r + 1) * (t + 1) : ℕ) : ℂ) / 2) := by
        by_cases hrt : r = t
        · subst hrt
          exact equalRankEpsilonCharacterChange p F r A.obj.representation B.obj.representation
            ωα ωβ A.property.1 A.property.2.1 B.property.1 B.property.2.1 hA hB ψ νS a νS' e h
        · exact pairFactorCharacterChange.2 p F r t A.obj.representation B.obj.representation
            ωα ωβ hrt A.property.1 A.property.2.1 B.property.1 B.property.2.1 hA hB ψ νS a νS' e h
      obtain ⟨e', he', h2, h1⟩ := hchange
      convert he' using 1
      refine Prod.ext ?_ ?_
      · apply Units.ext
        rw [h1, normalizedAbs_cpow_neg_half]
        simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, PNat.mk_coe]
        rw [← Nat.cast_mul]
        simp only [zpow_natCast]
      · rw [h2]
        simp only [PNat.mk_coe]
        push_cast
        ring

/-- The central characters of unitary virtual supercuspidal classes, evaluated at `a`,
as an additive map. -/
def centralCharacterAt (a : F.Carrierˣ) : UnitaryLattice.{uF, uV} F →+ Additive ℂˣ where
  toFun x := Additive.ofMul (latticeCentralCharacter F x a)
  map_zero' := by simp
  map_add' x y := by simp

/-- Change of additive character for the bilinear JPSS epsilon map on unitary virtual
supercuspidal classes: the epsilon map for `ψ^a` is the one for `ψ` plus the
correction built from central characters at `a`, degrees, `|a|^(-1/2)` and `ord a`. -/
theorem epsilonHom_unitaryBasisPairEpsilon_scale
    {ψ : Correspondence.NontrivialAdditiveCharacter F}
    {ν ν' : Correspondence.LocalAdditiveHaarMeasure F}
    (hν : Correspondence.IsSelfDualMeasure F ψ ν) (a : F.Carrierˣ)
    (hν' : Correspondence.IsSelfDualMeasure F (ψ.scale a) ν') :
    epsilonHom (unitaryBasisPairEpsilon.{uF, uV} F (ψ.scale a) ν' hν') =
      epsilonHom (unitaryBasisPairEpsilon.{uF, uV} F ψ ν hν) +
        epsilonCorrection (centralCharacterAt.{uF, uV} F a) (unitaryDegree.{uF, uV} F).toAddMonoidHom
          (LocalFactor.NonabelianSystem.positiveScale
            (LocalFactor.PadicAbelian.sqrtNormalizedAbs F a)
            (LocalFactor.PadicAbelian.sqrtNormalizedAbs_pos F a))⁻¹
          (F.canonicalTopologicalData.ord (a : F.Carrier)) := by
  apply bilinear_ext
  intro α β
  have h0 := (exists_isUnitaryBasisPairEpsilonFactor F ψ ν hν α β).choose_spec
  have h1 := IsUnitaryBasisPairEpsilonFactor.scale F hν a hν' h0
  have h2 := (exists_isUnitaryBasisPairEpsilonFactor F (ψ.scale a) ν' hν' α β).choose_spec
  have he := IsUnitaryBasisPairEpsilonFactor.unique h2 h1
  rw [LinearMap.add_apply, LinearMap.add_apply, epsilonHom_generator, epsilonHom_generator,
    epsilonCorrection_apply]
  change (Additive.ofMul (exists_isUnitaryBasisPairEpsilonFactor F (ψ.scale a) ν' hν' α β).choose.1,
    (exists_isUnitaryBasisPairEpsilonFactor F (ψ.scale a) ν' hν' α β).choose.2) = _
  rw [he]
  simp only [centralCharacterAt, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    latticeCentralCharacter_generator, LinearMap.toAddMonoidHom_coe, unitaryDegree_generator]
  unfold unitaryBasisPairEpsilon
  refine Prod.ext ?_ ?_
  · simp only [ofMul_mul, ofMul_zpow, Prod.fst_add]
    module
  · simp only [Prod.snd_add]

end Langlands.VirtualRepresentation.PadicSupercuspidal

namespace Langlands.VirtualRepresentation.LocalWeil

open Langlands.Weil.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance relativePairEpsilonScalingWeilTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance relativePairEpsilonScalingWeilValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance relativePairEpsilonScalingWeilLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

/-- The determinants of the canonical realizations of unitary virtual Weil classes,
evaluated at `w`, as an additive map. -/
def realizeDeterminantAt (w : localWeilGroup F) : UnitaryLattice.{uF, uV} F →+ Additive ℂˣ where
  toFun x := Additive.ofMul (ExactGrothendieckGroup.determinantCharacter _ (unitaryRealize F x) w)
  map_zero' := by simp
  map_add' x y := by simp

/-- The degrees of the canonical realizations of unitary virtual Weil classes. -/
def realizeDegree : UnitaryLattice.{uF, uV} F →+ ℤ :=
  ((ExactGrothendieckGroup.degree _).comp (unitaryRealize.{uF, uV} F)).toAddMonoidHom

/-- Change of additive character for the bilinear arithmetic epsilon map on unitary
virtual Weil classes: for `a` the reciprocity image of `w` under the base candidate of
the system, the epsilon map for `ψ^a` is the one for `ψ` plus the correction built from
determinants at `w`, degrees, `|a|^(-1/2)` and `ord a`. -/
theorem epsilonHom_unitaryBasisPairEpsilon_scale
    (eC : LocalFactor.CommonClosure.ReciprocityFamily F)
    (ε : LocalFactor.NonabelianSystem.Assignment.{uF, uE} F)
    (hε : LocalFactor.NonabelianSystem.IsSystem F eC ε)
    (ψ : Correspondence.NontrivialAdditiveCharacter F) (w : localWeilGroup F)
    (hW : HasUnitaryBasisPairEpsilonFactors.{uF, uV, uE} F eC ε hε ψ)
    (hW' : HasUnitaryBasisPairEpsilonFactors.{uF, uV, uE} F eC ε hε
      (ψ.scale (Correspondence.reciprocityHom F (Correspondence.baseReciprocityCandidate F eC) w))) :
    epsilonHom (unitaryBasisPairEpsilon F eC ε hε _ hW') =
      epsilonHom (unitaryBasisPairEpsilon F eC ε hε ψ hW) +
        epsilonCorrection (realizeDeterminantAt.{uF, uV} F w) (realizeDegree.{uF, uV} F)
          (LocalFactor.NonabelianSystem.positiveScale
            (LocalFactor.PadicAbelian.sqrtNormalizedAbs F
              (Correspondence.reciprocityHom F (Correspondence.baseReciprocityCandidate F eC) w))
            (LocalFactor.PadicAbelian.sqrtNormalizedAbs_pos F _))⁻¹
          (F.canonicalTopologicalData.ord
            (Correspondence.reciprocityHom F (Correspondence.baseReciprocityCandidate F eC) w :
              F.Carrier)) := by
  apply bilinear_ext
  intro α β
  obtain ⟨A, hAr, hpA⟩ := exists_unitaryRealize_generator F α
  obtain ⟨B, hBr, hpB⟩ := exists_unitaryRealize_generator F β
  rw [LinearMap.add_apply, LinearMap.add_apply, epsilonHom_generator, epsilonHom_generator,
    epsilonCorrection_apply]
  unfold unitaryBasisPairEpsilon
  have h0 := (hW α β).choose_spec
  have h2 := (hW' α β).choose_spec
  generalize (hW α β).choose = g at h0 ⊢
  generalize (hW' α β).choose = g' at h2 ⊢
  rw [hpA, hpB] at h0 h2
  have h1 := Correspondence.isArithmeticPairEpsilonFactor_zeroMonodromy_scale F eC ε hε ψ
    A.val B.val A.property B.property w h0
  obtain ⟨he1, he2⟩ := Correspondence.IsArithmeticPairEpsilonFactor.unique F h2 h1
  rw [he1, he2]
  simp only [realizeDeterminantAt, realizeDegree, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    LinearMap.toAddMonoidHom_coe, LinearMap.comp_apply, hAr, hBr,
    ExactGrothendieckGroup.degree_ofRepresentation,
    ExactGrothendieckGroup.determinantCharacter_ofRepresentation]
  refine Prod.ext ?_ ?_
  · simp only [ofMul_mul, ofMul_zpow, Prod.fst_add]
    module
  · simp only [Prod.snd_add]

/-- `realizeDegree` is the unitary degree. -/
theorem realizeDegree_apply (x : UnitaryLattice.{uF, uV} F) :
    realizeDegree F x = unitaryDegree F x := by
  change ExactGrothendieckGroup.degree _ (realizeExact F (includeUnitary F x)) = _
  rw [degree_realizeExact]
  rfl

/-- `realizeDeterminantAt` is the unitary determinant evaluated at `w`. -/
theorem realizeDeterminantAt_apply (w : localWeilGroup F) (x : UnitaryLattice.{uF, uV} F) :
    realizeDeterminantAt F w x = Additive.ofMul (Additive.toMul (unitaryDeterminant F x) w) := by
  rw [unitaryDeterminant_eq_determinant_realizeExact]
  rfl

end Langlands.VirtualRepresentation.LocalWeil

namespace Langlands.Global.PoleComparison

open Langlands.VirtualRepresentation Langlands.VirtualRepresentation.RelativeGlobal
open Langlands.Global.CompletionPadic Langlands.ClassFieldTheory.Global

variable (F E : Type uF) [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
  (c : FundamentalClass.ClassFamily.{uF}) (v : FinitePlace F)

/-- Change of additive character for the pair epsilon clause on the graph of a
generated positive isometry: a common epsilon factor of `(x, y)` and `(T x, T y)` at
`(ψ, ν)` gives one at every `(ψ', ν')`. -/
def RelativePairEpsilonScaling : Prop :=
  RelativeWeilGroup.IsArithmeticClassFamily c →
  ∀ (T : weilImage.{uF, uW, uP} F E c v ≃ₗ[ℤ] automorphicImage.{uF, uW, uP} F E c v),
    RelativeGeneratedPositiveIsometry F E c v T →
    ∀ (ψ ψ' : Correspondence.NontrivialAdditiveCharacter (padicField v))
      (ν ν' : Correspondence.LocalAdditiveHaarMeasure (padicField v)),
      Correspondence.IsSelfDualMeasure (padicField v) ψ ν →
      Correspondence.IsSelfDualMeasure (padicField v) ψ' ν' →
    ∀ (eC : LocalFactor.CommonClosure.ReciprocityFamily (padicField v))
      (ε : LocalFactor.NonabelianSystem.Assignment.{uF, uE} (padicField v))
      (hε : LocalFactor.NonabelianSystem.IsSystem (padicField v) eC ε)
      (x y : weilImage.{uF, uW, uP} F E c v) (e : ℂˣ × ℤ),
      LocalWeil.IsUnitaryPairEpsilonFactor (padicField v) eC ε hε ψ x.1 y.1 e →
      PadicSupercuspidal.IsUnitaryPairEpsilonFactor (padicField v) ψ ν (T x).1 (T y).1 e →
      ∃ e' : ℂˣ × ℤ,
        LocalWeil.IsUnitaryPairEpsilonFactor (padicField v) eC ε hε ψ' x.1 y.1 e' ∧
        PadicSupercuspidal.IsUnitaryPairEpsilonFactor (padicField v) ψ' ν' (T x).1 (T y).1 e'

/-- Change of additive character for the common pair epsilon factor on the graph of a
generated positive isometry: if some `c q^(-ms)` is both the Weil-side and the GL-side
epsilon factor of `(x, y)` and `(T x, T y)` for `ψ` (with a self-dual measure), then
the same holds for every other nontrivial additive character `ψ'`. -/
theorem relativePairEpsilonScaling : RelativePairEpsilonScaling.{uF, uW, uP, uE} F E c v := by
  intro hc T hT ψ ψ' ν ν' hν hν' eC ε hε x y e hW hG
  obtain ⟨a, ha⟩ := (padicField v).canonicalTopologicalData.exists_unit_scale_eq ψ ψ'
  set e0 := Correspondence.baseReciprocityCandidate (padicField v) eC with he0def
  have he0 : Correspondence.IsGeometricReciprocity (padicField v) e0 :=
    Correspondence.isGeometricReciprocity_of_isBaseReciprocity (padicField v) e0 eC
      (Correspondence.baseReciprocityCandidate_spec (padicField v) eC) hε.1
  obtain ⟨w, rfl⟩ := Correspondence.reciprocityHom_surjective (padicField v) e0 a
  have hW0 := LocalWeil.hasUnitaryBasisPairEpsilonFactors.{uF, uW, uE} (padicField v) eC ε hε ψ
  have hW1 := LocalWeil.hasUnitaryBasisPairEpsilonFactors.{uF, uW, uE} (padicField v) eC ε hε ψ'
  rw [LocalWeil.isUnitaryPairEpsilonFactor_iff (padicField v) eC ε hε ψ hW0] at hW
  rw [PadicSupercuspidal.isUnitaryPairEpsilonFactor_iff (padicField v) ψ ν hν] at hG
  have hΦΘ := epsilonPair_injective (hW.symm.trans hG)
  refine ⟨_, (LocalWeil.isUnitaryPairEpsilonFactor_iff (padicField v) eC ε hε ψ' hW1 _ _ _).mpr rfl,
    ?_⟩
  rw [PadicSupercuspidal.isUnitaryPairEpsilonFactor_iff (padicField v) ψ' ν' hν']
  subst ha
  rw [LocalWeil.epsilonHom_unitaryBasisPairEpsilon_scale (padicField v) eC ε hε ψ w hW0 hW1,
    PadicSupercuspidal.epsilonHom_unitaryBasisPairEpsilon_scale (padicField v) hν _ hν']
  simp only [LinearMap.add_apply]
  rw [hΦΘ]
  refine congrArg epsilonPair (congrArg₂ (· + ·) rfl ?_)
  have hδ : ∀ z : weilImage.{uF, uW, uP} F E c v,
      LocalWeil.realizeDeterminantAt (padicField v) w z.1 =
        PadicSupercuspidal.centralCharacterAt (padicField v)
          (Correspondence.reciprocityHom (padicField v) e0 w) (T z).1 := by
    intro z
    rw [LocalWeil.realizeDeterminantAt_apply]
    change _ = Additive.ofMul (PadicSupercuspidal.latticeCentralCharacter _ (T z).1 _)
    rw [pairedLattice_determinant F E c v hc e0 he0 (relative_graph_mem_pair F E c v T hT z) w]
  have hn : ∀ z : weilImage.{uF, uW, uP} F E c v,
      LocalWeil.realizeDegree (padicField v) z.1 =
        (PadicSupercuspidal.unitaryDegree (padicField v)).toAddMonoidHom (T z).1 := by
    intro z
    rw [LocalWeil.realizeDegree_apply, LinearMap.toAddMonoidHom_coe, hT.2.2.1 z]
  simp only [epsilonCorrection_apply, hδ, hn]
  rfl

end Langlands.Global.PoleComparison
