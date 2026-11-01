import Langlands.Global.FiniteAdelicGL.Determinant
import Langlands.Global.AdelicFunctoriality.Isomorphism
import Langlands.Global.CMConjugationGL

/-! # Arithmetic transport on actual adelic general linear groups -/

noncomputable section
universe uK uL uM uR uS

set_option autoImplicit false

namespace Langlands.Global.AdelicGLTransport

open NumberField AdelicFunctoriality

private def matrixEquiv {R : Type uR} {S : Type uS}
    [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    (n : ℕ) (e : R ≃+* S) (he : Continuous e) (hes : Continuous e.symm) :
    Matrix.GeneralLinearGroup (Fin n) R ≃ₜ* Matrix.GeneralLinearGroup (Fin n) S where
  toFun := Matrix.GeneralLinearGroup.map e.toRingHom
  invFun := Matrix.GeneralLinearGroup.map e.symm.toRingHom
  left_inv g := by
    apply Units.ext
    apply Matrix.ext
    intro i j
    exact e.symm_apply_apply (g i j)
  right_inv g := by
    apply Units.ext
    apply Matrix.ext
    intro i j
    exact e.apply_symm_apply (g i j)
  map_mul' := map_mul _
  continuous_toFun := he.generalLinearGroup_map
  continuous_invFun := hes.generalLinearGroup_map

variable {K : Type uK} {L : Type uL} {M : Type uM}
variable [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]

/-- Entrywise arithmetic transport on the actual full adelic matrix unit group. -/
def adelicEquiv (n : ℕ) (e : K ≃+* L) : AdelicGL K n ≃ₜ* AdelicGL L n :=
  matrixEquiv n (adeleEquiv e) (continuous_adeleEquiv e) (continuous_adeleEquiv_symm e)

/-- Entrywise arithmetic transport on the finite adelic matrix unit group. -/
def finiteEquiv (n : ℕ) (e : K ≃+* L) : FiniteAdelicGL K n ≃ₜ* FiniteAdelicGL L n :=
  matrixEquiv n (finiteAdeleEquiv e)
    (continuous_finiteAdeleEquiv e) (continuous_finiteAdeleEquiv_symm e)

/-- Entrywise arithmetic transport on the infinite adelic matrix unit group. -/
def infiniteEquiv (n : ℕ) (e : K ≃+* L) : InfiniteAdelicGL K n ≃ₜ* InfiniteAdelicGL L n :=
  matrixEquiv n (infiniteAdeleEquiv e)
    (continuous_infiniteAdeleEquiv e) (continuous_infiniteAdeleEquiv_symm e)

/-- Entrywise transport between the actual corresponding finite completions. -/
def localEquiv (n : ℕ) (e : K ≃+* L) (v : FinitePlace L) :
    FiniteLocalGL K n (finitePlaceEquiv e v) ≃ₜ* FiniteLocalGL L n v :=
  matrixEquiv n (finiteCompletionEquiv e v)
    (continuous_finiteCompletionEquiv e v) (continuous_finiteCompletionEquiv_symm e v)

@[simp] theorem adelicEquiv_apply (n : ℕ) (e : K ≃+* L) (g : AdelicGL K n)
    (i j : Fin n) : adelicEquiv n e g i j = adeleEquiv e (g i j) := rfl

@[simp] theorem finiteEquiv_apply (n : ℕ) (e : K ≃+* L) (g : FiniteAdelicGL K n)
    (i j : Fin n) : finiteEquiv n e g i j = finiteAdeleEquiv e (g i j) := rfl

@[simp] theorem infiniteEquiv_apply (n : ℕ) (e : K ≃+* L) (g : InfiniteAdelicGL K n)
    (i j : Fin n) : infiniteEquiv n e g i j = infiniteAdeleEquiv e (g i j) := rfl

@[simp] theorem localEquiv_apply (n : ℕ) (e : K ≃+* L) (v : FinitePlace L)
    (g : FiniteLocalGL K n (finitePlaceEquiv e v)) (i j : Fin n) :
    localEquiv n e v g i j = finiteCompletionEquiv e v (g i j) := rfl

@[simp] theorem adelicEquiv_refl (n : ℕ) :
    adelicEquiv n (RingEquiv.refl K) = ContinuousMulEquiv.refl (AdelicGL K n) := by
  apply ContinuousMulEquiv.ext
  intro g
  apply Units.ext
  apply Matrix.ext
  intro i j
  exact RingEquiv.congr_fun adeleEquiv_refl (g i j)

@[simp] theorem finiteEquiv_refl (n : ℕ) :
    finiteEquiv n (RingEquiv.refl K) = ContinuousMulEquiv.refl (FiniteAdelicGL K n) := by
  apply ContinuousMulEquiv.ext
  intro g
  apply Units.ext
  apply Matrix.ext
  intro i j
  exact RingEquiv.congr_fun finiteAdeleEquiv_refl (g i j)

@[simp] theorem infiniteEquiv_refl (n : ℕ) :
    infiniteEquiv n (RingEquiv.refl K) = ContinuousMulEquiv.refl (InfiniteAdelicGL K n) := by
  apply ContinuousMulEquiv.ext
  intro g
  apply Units.ext
  apply Matrix.ext
  intro i j
  exact RingEquiv.congr_fun infiniteAdeleEquiv_refl (g i j)

theorem adelicEquiv_trans (n : ℕ) (e : K ≃+* L) (f : L ≃+* M) :
    adelicEquiv n (e.trans f) = (adelicEquiv n e).trans (adelicEquiv n f) := by
  apply ContinuousMulEquiv.ext
  intro g
  apply Units.ext
  apply Matrix.ext
  intro i j
  exact RingEquiv.congr_fun (adeleEquiv_trans e f) (g i j)

theorem finiteEquiv_trans (n : ℕ) (e : K ≃+* L) (f : L ≃+* M) :
    finiteEquiv n (e.trans f) = (finiteEquiv n e).trans (finiteEquiv n f) := by
  apply ContinuousMulEquiv.ext
  intro g
  apply Units.ext
  apply Matrix.ext
  intro i j
  exact RingEquiv.congr_fun (finiteAdeleEquiv_trans e f) (g i j)

theorem infiniteEquiv_trans (n : ℕ) (e : K ≃+* L) (f : L ≃+* M) :
    infiniteEquiv n (e.trans f) = (infiniteEquiv n e).trans (infiniteEquiv n f) := by
  apply ContinuousMulEquiv.ext
  intro g
  apply Units.ext
  apply Matrix.ext
  intro i j
  exact RingEquiv.congr_fun (infiniteAdeleEquiv_trans e f) (g i j)

/-- Rational matrix points are transported by the original field isomorphism. -/
theorem adelicEquiv_rational (n : ℕ) (e : K ≃+* L) (g : RationalGL K n) :
    adelicEquiv n e (AdelicGL.rational K n g) =
      AdelicGL.rational L n (Matrix.GeneralLinearGroup.map e.toRingHom g) := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  exact adeleEquiv_diagonal e (g i j)

@[simp] theorem finite_adelicEquiv (n : ℕ) (e : K ≃+* L) (g : AdelicGL K n) :
    AdelicGL.finite L n (adelicEquiv n e g) =
      finiteEquiv n e (AdelicGL.finite K n g) := by
  apply Units.ext
  rfl

@[simp] theorem infinite_adelicEquiv (n : ℕ) (e : K ≃+* L) (g : AdelicGL K n) :
    AdelicGL.infinite L n (adelicEquiv n e g) =
      infiniteEquiv n e (AdelicGL.infinite K n g) := by
  apply Units.ext
  rfl

/-- Pairing the two actual factors commutes with arithmetic matrix transport. -/
theorem adelicEquiv_pair (n : ℕ) (e : K ≃+* L)
    (a : InfiniteAdelicGL K n) (b : FiniteAdelicGL K n) :
    adelicEquiv n e (AdelicGL.pair K n a b) =
      AdelicGL.pair L n (infiniteEquiv n e a) (finiteEquiv n e b) := by
  apply Units.ext
  rfl

@[simp] theorem adelicEquiv_ofFinite (n : ℕ) (e : K ≃+* L) (g : FiniteAdelicGL K n) :
    adelicEquiv n e (AdelicGL.ofFinite K n g) =
      AdelicGL.ofFinite L n (finiteEquiv n e g) := by
  change adelicEquiv n e (AdelicGL.pair K n 1 g) =
    AdelicGL.pair L n 1 (finiteEquiv n e g)
  rw [adelicEquiv_pair, map_one]

@[simp] theorem adelicEquiv_ofInfinite (n : ℕ) (e : K ≃+* L)
    (g : InfiniteAdelicGL K n) :
    adelicEquiv n e (AdelicGL.ofInfinite K n g) =
      AdelicGL.ofInfinite L n (infiniteEquiv n e g) := by
  change adelicEquiv n e (AdelicGL.pair K n g 1) =
    AdelicGL.pair L n (infiniteEquiv n e g) 1
  rw [adelicEquiv_pair, map_one]

/-- Determinants transform by the actual idele equivalence. -/
theorem determinant_adelicEquiv (n : ℕ) (e : K ≃+* L) (g : AdelicGL K n) :
    AdelicGL.determinant L n (adelicEquiv n e g) =
      ideleEquiv e (AdelicGL.determinant K n g) :=
  Matrix.GeneralLinearGroup.map_det (adeleEquiv e).toRingHom g

/-- Scalar ideles transform by the same actual idele equivalence. -/
theorem adelicEquiv_scalar (n : ℕ) (e : K ≃+* L) (z : Ideles K) :
    adelicEquiv n e (AdelicGL.scalar K n z) =
      AdelicGL.scalar L n (ideleEquiv e z) := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  change adeleEquiv e (if i = j then z.val else 0) =
    if i = j then adeleEquiv e z.val else 0
  split_ifs <;> simp only [map_zero]

/-- Projection to a corresponding finite place commutes with arithmetic transport. -/
theorem localProjection_finiteEquiv (n : ℕ) (e : K ≃+* L)
    (v : FinitePlace L) (g : FiniteAdelicGL K n) :
    FiniteAdelicGL.localProjection L n v (finiteEquiv n e g) =
      localEquiv n e v
        (FiniteAdelicGL.localProjection K n (finitePlaceEquiv e v) g) := by
  apply Units.ext
  rfl

/-- Integrality of both the matrix and its inverse is preserved and reflected. -/
@[simp] theorem localEquiv_mem_localIntegral_iff (n : ℕ) (e : K ≃+* L)
    (v : FinitePlace L) (g : FiniteLocalGL K n (finitePlaceEquiv e v)) :
    localEquiv n e v g ∈ FiniteAdelicGL.localIntegral L n v ↔
      g ∈ FiniteAdelicGL.localIntegral K n (finitePlaceEquiv e v) := by
  simp only [FiniteAdelicGL.mem_localIntegral, ← map_inv, localEquiv_apply,
    finiteCompletionEquiv_integral]

/-- The full standard integral finite adelic subgroup is preserved and reflected. -/
@[simp] theorem finiteEquiv_mem_standardIntegral_iff (n : ℕ) (e : K ≃+* L)
    (g : FiniteAdelicGL K n) :
    finiteEquiv n e g ∈ FiniteAdelicGL.standardIntegral L n ↔
      g ∈ FiniteAdelicGL.standardIntegral K n := by
  simp only [FiniteAdelicGL.mem_standardIntegral_iff_local, localProjection_finiteEquiv,
    localEquiv_mem_localIntegral_iff]
  exact ((finitePlaceEquiv e).surjective.forall
    (p := fun v : FinitePlace K =>
      FiniteAdelicGL.localProjection K n v g ∈ FiniteAdelicGL.localIntegral K n v)).symm

/-- Arithmetic field automorphisms act covariantly on the actual adelic GL group. -/
def adelicAut (n : ℕ) : (K ≃ₐ[ℚ] K) →* (AdelicGL K n ≃* AdelicGL K n) where
  toFun σ := (adelicEquiv n σ.toRingEquiv).toMulEquiv
  map_one' := congrArg ContinuousMulEquiv.toMulEquiv (adelicEquiv_refl n)
  map_mul' σ τ := congrArg ContinuousMulEquiv.toMulEquiv
    (adelicEquiv_trans n τ.toRingEquiv σ.toRingEquiv)

/-- The corresponding installable left action, without a global instance. -/
@[instance_reducible]
def adelicAction (n : ℕ) : MulDistribMulAction (K ≃ₐ[ℚ] K) (AdelicGL K n) where
  __ := MulAction.compHom (AdelicGL K n) (adelicAut n)
  smul_one σ := map_one (adelicAut n σ)
  smul_mul σ g h := map_mul (adelicAut n σ) g h

@[simp] theorem adelicAut_apply (n : ℕ) (σ : K ≃ₐ[ℚ] K) (g : AdelicGL K n)
    (i j : Fin n) : adelicAut n σ g i j = adeleAut σ (g i j) := rfl

section CM
variable [IsCMField K]

/-- General arithmetic transport specializes to the existing CM matrix operation. -/
@[simp] theorem adelicEquiv_complexConj (n : ℕ) :
    adelicEquiv n (IsCMField.complexConj K).toRingEquiv = CMConjugation.adelicConj K n := by
  apply ContinuousMulEquiv.ext
  intro g
  rfl

@[simp] theorem finiteEquiv_complexConj (n : ℕ) :
    finiteEquiv n (IsCMField.complexConj K).toRingEquiv = CMConjugation.finiteConj K n := by
  apply ContinuousMulEquiv.ext
  intro g
  rfl

@[simp] theorem infiniteEquiv_complexConj (n : ℕ) :
    infiniteEquiv n (IsCMField.complexConj K).toRingEquiv = CMConjugation.infiniteConj K n := by
  apply ContinuousMulEquiv.ext
  intro g
  rfl

end CM
end Langlands.Global.AdelicGLTransport
