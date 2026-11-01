import Langlands.Representation.RankinSelberg.TwoBlockSecondWhittakerDeformationStatement
import Langlands.Representation.RankinSelberg.TwoBlockWhittakerDeformationProof
import Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergence.RadicalIwasawa
import Langlands.Representation.RankinSelberg.WhittakerTypeEquivalence
import Langlands.Representation.RankinSelberg.WhittakerGammaAdapters
import Langlands.Representation.RankinSelberg.LocalFactor
import Langlands.Representation.Induction.CharacterTwistProof
import Langlands.Representation.Induction.Equivalences
import Langlands.Representation.Whittaker.AlgebraicTwist
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Proof of the entire standard-character deformation on the second lower block

Proof of `Langlands.RankinSelberg.TwoBlockSecondWhittakerDeformationStatement`.
The published first-block inverse-character theorem `twoBlockWhittakerDeformation`
is applied with the additive character `ψ.scale (-1)` and evaluated at `-u`. An
actual equivalence between the global twist by `|det|^u` of the first-block family
at `-u` and the second-block family at `u` is constructed on lower-induced sections,
and the coefficients are multiplied by `|det g|^u`.
-/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker GeneralLinear

universe uF uW

namespace TwoBlockSecondDeformation

section Tensor

variable {R : Type*} [CommRing R] {n : ℕ} (B : BlockShape n)
  {V : Fin B.length → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/-- Twisting every block factor by a character multiplies the dependent tensor action
of the Levi by the product of the block characters. -/
theorem blockTensor_twist_apply (c : ∀ i, GeneralLinear (B.size i) R →* ℂˣ)
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) R) (V i))
    (L : B.Levi R) (x : PiTensorProduct ℂ V) :
    B.blockTensor (fun i => Langlands.twist (c i) (σ i)) L x =
      ((∏ i, c i (L i) : ℂˣ) : ℂ) • B.blockTensor σ L x := by
  have hL : B.blockTensor (fun i => Langlands.twist (c i) (σ i)) L =
      ((∏ i, c i (L i) : ℂˣ) : ℂ) • B.blockTensor σ L := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply,
      LinearMap.smul_apply, BlockShape.blockTensor_tprod, BlockShape.blockTensor_tprod]
    change PiTensorProduct.tprod ℂ (fun i => ((c i (L i) : ℂˣ) : ℂ) • σ i (L i) (v i)) = _
    rw [(PiTensorProduct.tprod ℂ).map_smul_univ, Units.coe_prod]
  exact LinearMap.congr_fun hL x

end Tensor

section Inducing

universe uG uV

variable {G : Type uG} [Group G] {P : Subgroup G} {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Identity coordinates between two inducing actions that agree pointwise. -/
def inducingEquivOfApply {τ τ' : Representation ℂ P V} (hτ : ∀ q x, τ q x = τ' q x) :
    τ.Equiv τ' :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ V) (fun q => LinearMap.ext fun x => hτ q x)

end Inducing

section Transport

universe uR uG uV uW'

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module R V] {V' : Type uW'} [AddCommGroup V'] [Module R V']
  {ρ : Representation R G V} {ρ' : Representation R G V'} {N : Subgroup G} {θ : N →* Rˣ}

theorem equiv_apply_symm_apply_rep (E : ρ.Equiv ρ') (g : G) (w : V') :
    E (ρ g (E.symm w)) = ρ' g w := by
  have hE := Representation.IntertwiningMap.isIntertwining ρ ρ' E.toIntertwiningMap g (E.symm w)
  simpa only [Representation.Equiv.coe_toIntertwiningMap,
    Representation.Equiv.apply_symm_apply] using hE

theorem equiv_symm_apply_apply_rep (E : ρ.Equiv ρ') (g : G) (v : V) :
    E.symm (ρ' g (E v)) = ρ g v := by
  have hE := Representation.IntertwiningMap.isIntertwining ρ' ρ E.symm.toIntertwiningMap g (E v)
  simpa only [Representation.Equiv.coe_toIntertwiningMap,
    Representation.Equiv.symm_apply_apply] using hE

/-- Matrix coefficients of a functional pulled back along an equivalence. -/
theorem functionalsCongr_symm_val_rep (E : ρ.Equiv ρ') (ℓ : functionals N θ ρ') (g : G)
    (w : V') :
    ((Whittaker.functionalsCongr E).symm ℓ).val (ρ g (E.symm w)) = ℓ.val (ρ' g w) := by
  rw [Whittaker.functionalsCongr_symm_apply, equiv_apply_symm_apply_rep]

/-- Matrix coefficients of a functional pushed forward along an equivalence. -/
theorem functionalsCongr_val_rep (E : ρ.Equiv ρ') (ℓ : functionals N θ ρ) (g : G) (v : V) :
    (Whittaker.functionalsCongr E ℓ).val (ρ' g (E v)) = ℓ.val (ρ g v) := by
  rw [Whittaker.functionalsCongr_apply, equiv_symm_apply_apply_rep]

theorem functionalsCongr_val_ne_zero (E : ρ.Equiv ρ') (ℓ : functionals N θ ρ)
    (hℓ : ℓ.val ≠ 0) : (Whittaker.functionalsCongr E ℓ).val ≠ 0 := by
  intro h0
  apply hℓ
  ext v
  have hv := LinearMap.congr_fun h0 (E v)
  rwa [Whittaker.functionalsCongr_apply, Representation.Equiv.symm_apply_apply] at hv

theorem functionalsCongr_symm_val_ne_zero (E : ρ.Equiv ρ') (ℓ : functionals N θ ρ')
    (hℓ : ℓ.val ≠ 0) : ((Whittaker.functionalsCongr E).symm ℓ).val ≠ 0 := by
  intro h0
  apply hℓ
  ext w
  have hw := LinearMap.congr_fun h0 (E.symm w)
  rwa [Whittaker.functionalsCongr_symm_apply, Representation.Equiv.apply_symm_apply] at hw

end Transport

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
variable {t : ℕ} (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1)
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

private theorem isTopologicalRing :
    letI := F.canonicalTopologicalData.topology
    IsTopologicalRing F.Carrier := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  infer_instance

/-- On the lower block parabolic, `|det|^u` is the product of the block powers
`|det a_i|^u` of its Levi projection. -/
theorem determinantComplexPower_oppositeParabolic (u : ℂ)
    (q : (succBlockShape m h).oppositeParabolic F.Carrier) :
    F.canonicalTopologicalData.determinantComplexPower (t + 1) u
        (q : GeneralLinear (t + 1) F.Carrier) =
      ∏ i, F.canonicalTopologicalData.determinantComplexPower (m i + 1) u
        ((succBlockShape m h).oppositeLeviProjection F.Carrier q i) := by
  change F.canonicalTopologicalData.unramifiedCharacter _
      (determinant (q : GeneralLinear (t + 1) F.Carrier)) =
    ∏ i, F.canonicalTopologicalData.unramifiedCharacter _
      (determinant ((succBlockShape m h).oppositeLeviProjection F.Carrier q i))
  rw [TwoBlockConvergence.determinant_oppositeParabolic, map_prod]

/-- The ambient twist `|det|^u` combined with the first-block twist `|det|^(-u)`
gives the second-block twist `|det|^u` on every lower parabolic element. -/
theorem ambient_mul_firstBlock_eq_secondBlock (u : ℂ)
    (q : (succBlockShape m h).oppositeParabolic F.Carrier) :
    F.canonicalTopologicalData.determinantComplexPower (t + 1) u
        (q : GeneralLinear (t + 1) F.Carrier) *
      ∏ i, F.canonicalTopologicalData.determinantComplexPower (m i + 1)
        (if i = 0 then -u else 0)
        ((succBlockShape m h).oppositeLeviProjection F.Carrier q i) =
      ∏ i, F.canonicalTopologicalData.determinantComplexPower (m i + 1)
        (if i = 1 then u else 0)
        ((succBlockShape m h).oppositeLeviProjection F.Carrier q i) := by
  rw [determinantComplexPower_oppositeParabolic]
  simp only [Fin.prod_univ_two, Fin.isValue, ↓reduceIte, one_ne_zero, zero_ne_one,
    PadicField.TopologicalData.determinantComplexPower_neg,
    PadicField.TopologicalData.determinantComplexPower_zero, MonoidHom.inv_apply,
    MonoidHom.one_apply, mul_one, one_mul]
  rw [mul_comm (F.canonicalTopologicalData.determinantComplexPower (m 0 + 1) u _), mul_assoc,
    mul_inv_cancel, mul_one]

/-- The smooth ambient character `|det|^u` of `GL_(t+1)`. -/
def ambientCharacter (u : ℂ) :
    letI := F.canonicalTopologicalData.topology
    Induction.SmoothCharacter ℂ (GeneralLinear (t + 1) F.Carrier) :=
  letI := F.canonicalTopologicalData.topology
  ⟨F.canonicalTopologicalData.determinantComplexPower (t + 1) u,
    F.canonicalTopologicalData.isOpen_ker_determinantComplexPower (t + 1) u⟩

/-- The actual comparison of lower-induced representations
`|det|^u ⊗ ρ'_(-u) ≅ ρ_u`, where `ρ'` is the published first-block family and `ρ`
the second-block family: multiplication of sections by `|det|^u`, followed by the
identity on the dependent tensor carrier. -/
def twistComparison
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)) (u : ℂ) :
    letI := F.canonicalTopologicalData.topology
    (Langlands.twist (F.canonicalTopologicalData.determinantComplexPower (t + 1) u)
      (twoBlockDeformedInduced F m h σ (-u))).Equiv
      (twoBlockSecondDeformedInduced F m h σ u) :=
  letI := F.canonicalTopologicalData.topology
  haveI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  (Induction.smoothInductionTwistEquiv ((succBlockShape m h).oppositeParabolic F.Carrier)
    (ambientCharacter F u)
    (Langlands.twist
      (F.canonicalTopologicalData.oppositeParabolicHalfModulus (succBlockShape m h))
      (((succBlockShape m h).blockTensor (twoBlockDeformedBlocks F m σ (-u))).comp
        ((succBlockShape m h).oppositeLeviProjection F.Carrier)))).trans
    (Induction.smoothInducedEquiv ((succBlockShape m h).oppositeParabolic F.Carrier)
      (inducingEquivOfApply (fun q x => by
        change (F.canonicalTopologicalData.determinantComplexPower (t + 1) u
              (q : GeneralLinear (t + 1) F.Carrier) : ℂ) •
            ((F.canonicalTopologicalData.oppositeParabolicHalfModulus (succBlockShape m h) q :
                ℂ) •
              (succBlockShape m h).blockTensor (twoBlockDeformedBlocks F m σ (-u))
                ((succBlockShape m h).oppositeLeviProjection F.Carrier q) x) =
          (F.canonicalTopologicalData.oppositeParabolicHalfModulus (succBlockShape m h) q :
              ℂ) •
            (succBlockShape m h).blockTensor (twoBlockSecondDeformedBlocks F m σ u)
              ((succBlockShape m h).oppositeLeviProjection F.Carrier q) x
        have key := congrArg Units.val (ambient_mul_firstBlock_eq_secondBlock F m h u q)
        rw [Units.val_mul] at key
        rw [blockTensor_twist_apply (succBlockShape m h)
            (fun i => F.canonicalTopologicalData.determinantComplexPower (m i + 1)
              (if i = 0 then -u else 0)) σ,
          blockTensor_twist_apply (succBlockShape m h)
            (fun i => F.canonicalTopologicalData.determinantComplexPower (m i + 1)
              (if i = 1 then u else 0)) σ,
          ← key, mul_smul]
        exact smul_comm _ _ _)))

/-- At parameter zero the two families are the same untwisted induction; this is the
induced equivalence of the identity coordinates. -/
def zeroComparison
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)) :
    letI := F.canonicalTopologicalData.topology
    (twoBlockDeformedInduced F m h σ 0).Equiv (twoBlockSecondDeformedInduced F m h σ 0) :=
  letI := F.canonicalTopologicalData.topology
  haveI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  Induction.smoothInducedEquiv ((succBlockShape m h).oppositeParabolic F.Carrier)
    (inducingEquivOfApply (fun q x => by
      change (F.canonicalTopologicalData.oppositeParabolicHalfModulus (succBlockShape m h) q :
            ℂ) •
          (succBlockShape m h).blockTensor (twoBlockDeformedBlocks F m σ 0)
            ((succBlockShape m h).oppositeLeviProjection F.Carrier q) x =
        (F.canonicalTopologicalData.oppositeParabolicHalfModulus (succBlockShape m h) q :
            ℂ) •
          (succBlockShape m h).blockTensor (twoBlockSecondDeformedBlocks F m σ 0)
            ((succBlockShape m h).oppositeLeviProjection F.Carrier q) x
      rw [twoBlockDeformedBlocks_zero, twoBlockSecondDeformedBlocks_zero]))

/-- Every second-block coefficient at `u` comes from a first-block coefficient at `-u`
multiplied by `|det g|^u`: transport of the functional and vector along
`twistComparison`. -/
theorem exists_second_coefficient
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)) (u : ℂ)
    (ℓ : letI := F.canonicalTopologicalData.topology
      glFunctionals ψ t (twoBlockDeformedInduced F m h σ (-u)))
    (hℓ : ℓ.val ≠ 0) (v) :
    letI := F.canonicalTopologicalData.topology
    ∃ ℓ' : glFunctionals ψ t (twoBlockSecondDeformedInduced F m h σ u), ℓ'.val ≠ 0 ∧
      ∃ v', ∀ g, (F.canonicalTopologicalData.determinantComplexPower (t + 1) u g : ℂ) *
          ℓ.val (twoBlockDeformedInduced F m h σ (-u) g v) =
        ℓ'.val (twoBlockSecondDeformedInduced F m h σ u g v') := by
  let _ := F.canonicalTopologicalData.topology
  let E := twistComparison F m h σ u
  let ℓ2 := twistFunctional (upperUnipotent (t + 1) F.Carrier) (standardCharacter ψ t)
    (F.canonicalTopologicalData.determinantComplexPower (t + 1) u)
    (determinantComplexPower_upperUnipotent F (t + 1) u) _ ℓ
  refine ⟨Whittaker.functionalsCongr E ℓ2, functionalsCongr_val_ne_zero E ℓ2 hℓ, E v,
    fun g => ?_⟩
  rw [functionalsCongr_val_rep]
  change _ = ℓ.val ((F.canonicalTopologicalData.determinantComplexPower (t + 1) u g : ℂ) •
    twoBlockDeformedInduced F m h σ (-u) g v)
  rw [map_smul, smul_eq_mul]

/-- The second clause at `u`, from the first-block clause at `-u` for the inverse
character of `ψ.scale (-1)`. -/
theorem secondCoefficient_of_firstCoefficient
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
    (V : ℂ → GeneralLinear (t + 1) F.Carrier → ℂ) (u : ℂ)
    (hV : letI := F.canonicalTopologicalData.topology
      letI := isTopologicalRing F
      ∃ ℓ : glInverseFunctionals (ψ.scale (-1)) t (twoBlockDeformedInduced F m h σ (-u)),
        ℓ.val ≠ 0 ∧ ∃ v, ∀ g, V (-u) g = ℓ.val (twoBlockDeformedInduced F m h σ (-u) g v)) :
    letI := F.canonicalTopologicalData.topology
    ∃ ℓ : glFunctionals ψ t (twoBlockSecondDeformedInduced F m h σ u), ℓ.val ≠ 0 ∧
      ∃ v, ∀ g, (F.canonicalTopologicalData.determinantComplexPower (t + 1) u g : ℂ) *
          V (-u) g = ℓ.val (twoBlockSecondDeformedInduced F m h σ u g v) := by
  let _ := F.canonicalTopologicalData.topology
  let _ := isTopologicalRing F
  obtain ⟨ℓ', hℓ', v', hv'⟩ := hV
  obtain ⟨ℓ, hℓ, v, hv⟩ := exists_second_coefficient F m h ψ σ u
    (_root_.Langlands.RankinSelberg.functionalsCongr
      (inverseStandardCharacter_scale_neg_one ψ t) ℓ') hℓ' v'
  refine ⟨ℓ, hℓ, v, fun g => ?_⟩
  rw [hv' g]
  exact hv g

/-- Multiplying a family by `|det g|^u` and reversing the parameter keeps one common
compact open right stabilizer: intersect with the kernel of `|det|`. -/
theorem exists_level_twistedFamily
    (V : ℂ → GeneralLinear (t + 1) F.Carrier → ℂ)
    (hV : letI := F.canonicalTopologicalData.topology
      ∃ K : Subgroup (GeneralLinear (t + 1) F.Carrier),
        IsOpen (K : Set (GeneralLinear (t + 1) F.Carrier)) ∧
        IsCompact (K : Set (GeneralLinear (t + 1) F.Carrier)) ∧
        ∀ (u : ℂ) (g : GeneralLinear (t + 1) F.Carrier) (k : K), V u (g * k) = V u g) :
    letI := F.canonicalTopologicalData.topology
    ∃ K : Subgroup (GeneralLinear (t + 1) F.Carrier),
      IsOpen (K : Set (GeneralLinear (t + 1) F.Carrier)) ∧
      IsCompact (K : Set (GeneralLinear (t + 1) F.Carrier)) ∧
      ∀ (u : ℂ) (g : GeneralLinear (t + 1) F.Carrier) (k : K),
        (F.canonicalTopologicalData.determinantComplexPower (t + 1) u (g * k) : ℂ) *
            V (-u) (g * k) =
          (F.canonicalTopologicalData.determinantComplexPower (t + 1) u g : ℂ) * V (-u) g := by
  let _ := F.canonicalTopologicalData.topology
  have := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  obtain ⟨K₀, hK₀o, hK₀c, hK₀⟩ := hV
  refine ⟨K₀ ⊓ (F.canonicalTopologicalData.determinantNorm (t + 1)).ker, ?_, ?_, ?_⟩
  · exact hK₀o.inter (F.canonicalTopologicalData.isOpen_ker_determinantNorm (t + 1))
  · exact hK₀c.inter_right (Subgroup.isClosed_of_isOpen _
      (F.canonicalTopologicalData.isOpen_ker_determinantNorm (t + 1)))
  · intro u g k
    have hk : F.canonicalTopologicalData.determinantNorm (t + 1)
        (k : GeneralLinear (t + 1) F.Carrier) = 1 := k.property.2
    have hc : F.canonicalTopologicalData.determinantComplexPower (t + 1) u
        (k : GeneralLinear (t + 1) F.Carrier) = 1 := by
      apply Units.ext
      rw [PadicField.TopologicalData.determinantComplexPower_apply, hk]
      simp
    rw [map_mul, Units.val_mul, hc, Units.val_one, mul_one,
      show V (-u) (g * k) = V (-u) g from hK₀ (-u) g ⟨k, k.property.1⟩]

/-- Multiplying a pointwise entire family by `|det g|^u` and reversing the parameter
keeps it pointwise entire. -/
theorem analyticAt_twistedFamily (V : ℂ → GeneralLinear (t + 1) F.Carrier → ℂ)
    (hV : ∀ (g : GeneralLinear (t + 1) F.Carrier) (u : ℂ), AnalyticAt ℂ (fun z => V z g) u)
    (g : GeneralLinear (t + 1) F.Carrier) (u : ℂ) :
    AnalyticAt ℂ (fun z =>
      (F.canonicalTopologicalData.determinantComplexPower (t + 1) z g : ℂ) * V (-z) g) u := by
  have hpos : (0 : ℝ) <
      ((F.canonicalTopologicalData.determinantNorm (t + 1) g : NNReal) : ℝ) :=
    NNReal.coe_pos.2 (pos_iff_ne_zero.2
      (F.canonicalTopologicalData.determinantNorm (t + 1) g).ne_zero)
  have hpow : AnalyticAt ℂ (fun z : ℂ =>
      (F.canonicalTopologicalData.determinantComplexPower (t + 1) z g : ℂ)) u := by
    simp_rw [PadicField.TopologicalData.determinantComplexPower_apply]
    exact AnalyticAt.cpow analyticAt_const analyticAt_id (Complex.ofReal_mem_slitPlane.2 hpos)
  have hneg : AnalyticAt ℂ (fun z : ℂ => V (-z) g) u :=
    (hV g (-u)).comp_of_eq analyticAt_id.neg rfl
  exact hpow.mul hneg

end TwoBlockSecondDeformation

open TwoBlockSecondDeformation in
/-- Entire standard-character deformation on the second lower-induced block, derived
from the published first-block inverse-character theorem by character change,
the parameter `-u` and the global twist `|det|^u`. -/
theorem twoBlockSecondWhittakerDeformation :
    TwoBlockSecondWhittakerDeformationStatement.{uF, uW} := by
  intro p _ F ψ t m h W _ _ σ hσ ℓ₀ hℓ₀ v₀
  let _ := F.canonicalTopologicalData.topology
  let _ := isTopologicalRing F
  have hη : ∀ i, IsOfWhittakerType (m i) (standardCharacter (ψ.scale (-1)) (m i)) (σ i) := by
    intro i
    rw [standardCharacter_scale_neg_one]
    exact (isOfWhittakerType_standard_iff_inverse ψ (σ i)).1 (hσ i)
  let E0 := zeroComparison F m h σ
  let ℓs : glInverseFunctionals (ψ.scale (-1)) t (twoBlockDeformedInduced F m h σ 0) :=
    _root_.Langlands.RankinSelberg.functionalsCongr
      (inverseStandardCharacter_scale_neg_one ψ t).symm
      ((Whittaker.functionalsCongr E0).symm ℓ₀)
  obtain ⟨V, hV0, hVu, hVK, hVa⟩ :=
    twoBlockWhittakerDeformation p F (ψ.scale (-1)) t m h σ hη ℓs
      (functionalsCongr_symm_val_ne_zero E0 ℓ₀ hℓ₀) (E0.symm v₀)
  refine ⟨fun u g =>
    (F.canonicalTopologicalData.determinantComplexPower (t + 1) u g : ℂ) * V (-u) g,
    fun g => ?_, fun u => ?_, exists_level_twistedFamily F V hVK,
    analyticAt_twistedFamily F V hVa⟩
  · have h1 : (F.canonicalTopologicalData.determinantComplexPower (t + 1) 0 g : ℂ) = 1 := by
      rw [PadicField.TopologicalData.determinantComplexPower_zero, MonoidHom.one_apply,
        Units.val_one]
    change (F.canonicalTopologicalData.determinantComplexPower (t + 1) 0 g : ℂ) * V (-0) g = _
    rw [h1, neg_zero, one_mul (V 0 g), hV0 g]
    exact functionalsCongr_symm_val_rep E0 ℓ₀ g v₀
  · exact secondCoefficient_of_firstCoefficient F m h ψ σ V u (hVu (-u))

end Langlands.RankinSelberg
