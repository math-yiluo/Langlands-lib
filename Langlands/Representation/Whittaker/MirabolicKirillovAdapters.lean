import Langlands.Representation.Whittaker.MirabolicModels
import Langlands.Representation.Induction.CompactQuotientProof
import Langlands.Representation.Smooth.Transfer.PullbackProof

/-! # Actual coefficient and compact-support adapters for the mirabolic model -/

noncomputable section

namespace Langlands.Whittaker

open GeneralLinear HarmonicAnalysis
open scoped BigOperators

universe uF uV

variable {F : Type uF} [CommRing F] [TopologicalSpace F] [IsTopologicalRing F]
variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The coefficient map on the actual mirabolic group, before taking smooth vectors. -/
def mirabolicAlgebraicCoefficientMap (ψ : UnitaryAdditiveCharacter F)
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (ℓ : glFunctionals ψ n ρ) :
    Representation.IntertwiningMap (ρ.comp (mirabolic n F).subtype)
      (Induction.equivariantAction (Mirabolic.upperUnipotent n F)
        (mirabolicCharacterRepresentation ψ n)) where
  toLinearMap :=
    { toFun := fun v => ⟨fun q => ℓ.val (ρ q.val v), by
        intro u q
        change ℓ.val (ρ (u.val.val * q.val) v) =
          (mirabolicCharacter ψ n u : ℂ) * ℓ.val (ρ q.val v)
        rw [map_mul, Module.End.mul_apply]
        exact ℓ.property (Mirabolic.upperUnipotentEquiv u) (ρ q.val v)⟩
      map_add' := by intro v w; apply Subtype.ext; funext q; simp
      map_smul' := by intro a v; apply Subtype.ext; funext q; simp }
  isIntertwining' s := by
    ext v q
    change ℓ.val (ρ q.val (ρ s.val v)) = ℓ.val (ρ (q.val * s.val) v)
    rw [map_mul, Module.End.mul_apply]

/-- Smoothness of the original representation lifts its actual coefficients to
the smooth induced mirabolic representation. -/
def mirabolicCoefficientMap (ψ : UnitaryAdditiveCharacter F)
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (hρ : IsSmooth ρ) (ℓ : glFunctionals ψ n ρ) :
    Representation.IntertwiningMap (ρ.comp (mirabolic n F).subtype)
      (mirabolicSmoothInduced ψ n) :=
  smoothLift (isSmooth_comp _ continuous_subtype_val hρ)
    (mirabolicAlgebraicCoefficientMap ψ ρ ℓ)

@[simp] theorem mirabolicCoefficientMap_eval (ψ : UnitaryAdditiveCharacter F)
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (hρ : IsSmooth ρ) (ℓ : glFunctionals ψ n ρ) (v : V) (q : mirabolic n F) :
    mirabolicEval ψ n (mirabolicCoefficientMap ψ ρ hρ ℓ v) q = ℓ.val (ρ q.val v) := rfl

/-- The actual invariant coefficient image in smooth induction. -/
def mirabolicCoefficientImage (ψ : UnitaryAdditiveCharacter F)
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (hρ : IsSmooth ρ) (ℓ : glFunctionals ψ n ρ) :
    Subrepresentation (mirabolicSmoothInduced ψ n) :=
  (mirabolicCoefficientMap ψ ρ hρ ℓ).range

/-- Evaluation at the identity shows that a nonzero functional has nonzero image. -/
theorem mirabolicCoefficientImage_ne_bot (ψ : UnitaryAdditiveCharacter F)
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (hρ : IsSmooth ρ) (ℓ : glFunctionals ψ n ρ) (hℓ : ℓ.val ≠ 0) :
    mirabolicCoefficientImage ψ ρ hρ ℓ ≠ ⊥ := by
  intro h
  apply hℓ
  ext v
  change ℓ.val v = 0
  have hv : mirabolicCoefficientMap ψ ρ hρ ℓ v ∈
      mirabolicCoefficientImage ψ ρ hρ ℓ := ⟨v, rfl⟩
  rw [h] at hv
  have hz : mirabolicCoefficientMap ψ ρ hρ ℓ v = 0 := hv
  have he := congrArg (fun f => mirabolicEval ψ n f 1) hz
  change ℓ.val (ρ 1 v) = 0 at he
  simpa only [map_one, Module.End.one_apply] using he

/-- Restrict a covariant ambient function with a uniform ambient open stabilizer
to the actual smooth induced mirabolic model. -/
def mirabolicSmoothRestriction (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (φ : Langlands.GeneralLinear (n + 1) F → ℂ)
    (hcov : ∀ (u : GeneralLinear.upperUnipotent (n + 1) F) (q : mirabolic n F),
      φ (u.val * q.val) = (standardCharacter ψ n u : ℂ) * φ q.val)
    (K : OpenSubgroup (Langlands.GeneralLinear (n + 1) F))
    (hK : ∀ (q k : mirabolic n F), k.val ∈ K → φ (q.val * k.val) = φ q.val) :
    MirabolicSmoothFunctions ψ n :=
  Induction.smoothFunctionOf _ _ (fun q => φ q.val)
    (fun u q => hcov (Mirabolic.upperUnipotentEquiv u) q)
    (K.comap (mirabolic n F).subtype continuous_subtype_val)
    (fun k q => hK q k.val k.property)

omit [IsTopologicalRing F] in
@[simp] theorem mirabolicSmoothRestriction_eval (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (φ : Langlands.GeneralLinear (n + 1) F → ℂ) (hcov) (K) (hK) (q : mirabolic n F) :
    mirabolicEval ψ n (mirabolicSmoothRestriction ψ n φ hcov K hK) q = φ q.val := rfl

variable [T2Space F]

/-- An ambient compact witness modulo the upper unipotent group gives compact
projected support after restriction to the closed actual mirabolic subgroup. -/
theorem mirabolicSmoothRestriction_mem_compact (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (φ : Langlands.GeneralLinear (n + 1) F → ℂ) (hcov) (K) (hK)
    (C : Set (Langlands.GeneralLinear (n + 1) F)) (hC : IsCompact C)
    (hsupp : ∀ q : mirabolic n F, φ q.val ≠ 0 →
      ∃ (u : GeneralLinear.upperUnipotent (n + 1) F)
        (c : Langlands.GeneralLinear (n + 1) F), c ∈ C ∧ q.val = u.val * c) :
    mirabolicSmoothRestriction ψ n φ hcov K hK ∈ mirabolicCompactSubrepresentation ψ n := by
  let P := mirabolic n F
  let U := Mirabolic.upperUnipotent n F
  let D : Set P := Subtype.val ⁻¹' C
  have hD : IsCompact D :=
    (Mirabolic.isClosed (F := F) (n := n)).isClosedEmbedding_subtypeVal.isCompact_preimage hC
  have hQ : Continuous (Induction.quotientMap U) := continuous_quot_mk
  apply (hD.image hQ).of_isClosed_subset
    (Induction.isClosed_quotientSupport U _ (mirabolicSmoothRestriction ψ n φ hcov K hK))
  rintro _ ⟨q, hq, rfl⟩
  obtain ⟨u, c, hc, heq⟩ := hsupp q hq
  have hcP : c ∈ P := by
    have huP : u.val ∈ P := upperUnipotent_le_mirabolic u.property
    have hid : c = u.val⁻¹ * q.val := by rw [heq]; simp
    rw [hid]
    exact P.mul_mem (P.inv_mem huP) q.property
  refine ⟨⟨c, hcP⟩, hc, ?_⟩
  apply Quotient.sound
  change QuotientGroup.rightRel U ⟨c, hcP⟩ q
  rw [QuotientGroup.rightRel_apply]
  change q.val * c⁻¹ ∈ GeneralLinear.upperUnipotent (n + 1) F
  simpa only [heq, mul_inv_cancel_right] using u.property

/-- The actual compact mirabolic function determined by an ambient Kirillov test function. -/
def mirabolicCompactRestriction (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (φ : Langlands.GeneralLinear (n + 1) F → ℂ)
    (hcov : ∀ (u : GeneralLinear.upperUnipotent (n + 1) F) (q : mirabolic n F),
      φ (u.val * q.val) = (standardCharacter ψ n u : ℂ) * φ q.val)
    (K : OpenSubgroup (Langlands.GeneralLinear (n + 1) F))
    (hK : ∀ (q k : mirabolic n F), k.val ∈ K → φ (q.val * k.val) = φ q.val)
    (C : Set (Langlands.GeneralLinear (n + 1) F)) (hC : IsCompact C)
    (hsupp : ∀ q : mirabolic n F, φ q.val ≠ 0 →
      ∃ (u : GeneralLinear.upperUnipotent (n + 1) F)
        (c : Langlands.GeneralLinear (n + 1) F), c ∈ C ∧ q.val = u.val * c) :
    MirabolicCompactFunctions ψ n :=
  ⟨mirabolicSmoothRestriction ψ n φ hcov K hK,
    mirabolicSmoothRestriction_mem_compact ψ n φ hcov K hK C hC hsupp⟩

@[simp] theorem mirabolicCompactRestriction_eval (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (φ : Langlands.GeneralLinear (n + 1) F → ℂ) (hcov) (K) (hK) (C) (hC) (hsupp)
    (q : mirabolic n F) :
    mirabolicCompactEval ψ n
      (mirabolicCompactRestriction ψ n φ hcov K hK C hC hsupp) q = φ q.val := rfl

end Langlands.Whittaker
