import Langlands.BaseChange.DeterminantTwistFieldEquiv
import Langlands.BaseChange.DistinguishedStandardEulerPolynomials
import Langlands.BaseChange.OrbitStandardFactorSeparation
import Langlands.BaseChange.SigmaOrbitDeterminantTwist
import Langlands.Global.Factors.DistinguishedFiniteStandardEpsilon
import Langlands.Representation.RankinSelberg.FieldTransport.LocalFieldLPolynomial

/-! # Separated standard Euler factors at a distinguished completion -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u uQ uF uE uW

namespace Langlands.BaseChange

open Automorphic Automorphic.ConstantFunctions Global Global.CompletionPadic
open Global.CuspidalPairFunctionalEquation GeneralLinear HarmonicAnalysis MeasureTheory
open RankinSelberg Whittaker
open scoped PadicField.CanonicalLocalField

section Orbit

variable {F : Type u} [Field F] [TopologicalSpace F] [ValuativeRel F]
  [IsNonarchimedeanLocalField F] [CharZero F]
  {E : Type uE} [Field E] [TopologicalSpace E] [ValuativeRel E]
  [IsNonarchimedeanLocalField E] [Algebra F E] [FiniteDimensional F E] [IsModuleTopology F E]
  (σ : E ≃ₐ[F] E) {s k r : ℕ} (hr : s * (k + 1) = r + 1)
  {W₁ W : Type uW} [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W] [Module ℂ W]
  {P₁ : Representation ℂ (GeneralLinear (k + 1) E) W₁}
  {P : Representation ℂ (GeneralLinear (r + 1) E) W}

/-- A Galois-invariant smooth determinant twist of the full orbit product has
separated forward and dual standard factors. -/
theorem hasSeparatedLocalStandardFactors_twist_sigmaOrbit
    (hI : P₁.IsIrreducible) (hS : IsSupercuspidal P₁)
    (hP : Nonempty (P.Equiv ((sigmaOrbitProduct σ s (Nat.succ_pos k) P₁).comp
      (GeneralLinear.reindex (R := E) (finCongr hr)).symm.toMonoidHom)))
    (χ : Induction.SmoothCharacter ℂ Eˣ)
    (hχ : ∀ (j : ℕ) (x : Eˣ),
      χ.toMonoidHom (Units.map (σ ^ j).toRingHom.toMonoidHom x) = χ.toMonoidHom x) :
    HasSeparatedLocalStandardFactors E (twist (χ.toMonoidHom.comp determinant) P) := by
  let η := χ.toMonoidHom.comp (determinant (n := k + 1))
  have hη : IsOpen (η.ker : Set (GeneralLinear (k + 1) E)) :=
    χ.isOpen_ker.preimage ((LocalFieldData.ofInstances E).generalLinearDeterminant (k + 1)).continuous
  have hd : (determinant : GeneralLinear (k + 1) E →* Eˣ).ker ≤ η.ker := by
    intro g hg
    change χ.toMonoidHom (determinant g) = 1
    rw [MonoidHom.mem_ker.mp hg, map_one]
  exact orbitStandardFactorSeparation F E σ s k r hr W₁ W (twist η P₁)
    (twist (χ.toMonoidHom.comp determinant) P) ((isIrreducible_twist_iff η P₁).mpr hI)
    ((isSupercuspidal_twist_iff η hη hd P₁).mpr hS)
    (sigmaOrbitDeterminantTwist F E σ χ hχ s (k + 1) (r + 1) (Nat.succ_pos k) hr W₁ W P₁ P hP)

end Orbit

section Completion

local instance separationRationalGroup (K : Type u) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions K n) := Submodule.addCommGroup _
local instance separationContinuousGroup (K : Type u) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions K n) := Submodule.addCommGroup _
local instance separationSmoothGroup (K : Type u) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions K n) := Submodule.addCommGroup _
local instance separationFormsGroup (K : Type u) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (AutomorphicForms K n) := Submodule.addCommGroup _
local instance separationLocalGroup {K : Type u} [Field K] [NumberField K]
    {n : ℕ} {w : FinitePlace K} (A : LocalRealization K n w) :
    AddCommGroup A.Space := Submodule.addCommGroup _

variable {L : Type u} [Field L] [NumberField L] [CompactSpace (AdeleQuotient L)]
  {r : ℕ} {U Ud : CuspidalOperatorRealization L r}
  (Q : CuspidalSpectralPresentation.{u, uQ} U) (Qd : CuspidalSpectralPresentation.{u, uQ} Ud)
  (hQ : HasIrreducibleAdmissibleComponents Q) (hQd : HasIrreducibleAdmissibleComponents Qd)
  {Ψ : UnitaryAdditiveCharacter (Adeles L)}
  (cE : FinitePairFactorChoice Ψ Q (rankOneSpectralPresentation.{u, uQ} L)
    Qd (rankOneSpectralPresentation.{u, uQ} L)
    hQ (rankOneSpectralPresentation_hasIrreducibleAdmissibleComponents.{u, uQ} L)
    hQd (rankOneSpectralPresentation_hasIrreducibleAdmissibleComponents.{u, uQ} L))
  (w : FinitePlace L)
  {E : Type uE} [Field E] [TopologicalSpace E] [ValuativeRel E] [IsNonarchimedeanLocalField E]
  (b : E ≃+* (padicField w).Carrier)
  (hb : @Continuous E (padicField w).Carrier ‹TopologicalSpace E›
    (padicField w).canonicalTopologicalData.topology b)
  (hb' : @Continuous (padicField w).Carrier E (padicField w).canonicalTopologicalData.topology
    ‹TopologicalSpace E› b.symm)
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (P : Representation ℂ (GeneralLinear (r + 1) E) W)

private theorem inverseTranspose_map {D : Type*} [Field D] {E : Type*} [Field E]
    (f : D →+* E) {n : ℕ} (g : GeneralLinear n D) :
    inverseTranspose n E (Matrix.GeneralLinearGroup.map f g) =
      Matrix.GeneralLinearGroup.map f (inverseTranspose n D g) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [inverseTranspose_coe, Matrix.transpose_apply, ← map_inv,
    Matrix.GeneralLinearGroup.map_apply]

include hb hb' in
set_option maxHeartbeats 3200000 in
/-- Identifying a finite component with the transported representation carries
the separation of its standard Euler roots to the completed equation. -/
theorem distinguishedEulerRootSeparation_of_pullback
    (hr : 0 < r) (hu : Ud.realization.IsContragredientOf U.realization)
    (e : P.Equiv ((Q.localComponent w).representation.comp (Matrix.GeneralLinearGroup.map b.toRingHom)))
    (hsep : HasSeparatedLocalStandardFactors E P) :
    ∀ x : ℂ, x ≠ 0 → (cE.lPolynomial w).eval x = 0 →
      (cE.dualLPolynomial w).eval ((residueCardinality w : ℂ)⁻¹ / x) ≠ 0 := by
  let J := padicField w
  let T := J.canonicalTopologicalData
  let : TopologicalSpace J.Carrier := T.topology
  let : ValuativeRel J.Carrier := T.valuativeRel
  let : IsNonarchimedeanLocalField J.Carrier := T.localField
  let := borel E
  let : BorelSpace E := ⟨rfl⟩
  let := borel J.Carrier
  let : BorelSpace J.Carrier := ⟨rfl⟩
  let := borel (GeneralLinear 1 E)
  let : BorelSpace (GeneralLinear 1 E) := ⟨rfl⟩
  let := borel (upperUnipotent 1 E)
  let : BorelSpace (upperUnipotent 1 E) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient 0 E)
  let ψ := completionAdditivePullback J b hb (cE.additive w)
  let ν := completionHaarPullback J b hb hb' (cE.measure w)
  have hν := completionHaarPullback_isSelfDual J b hb hb' (cE.additive w) (cE.measure w) (cE.measure_spec w)
  let dual : AllField.LocalFactor.PadicAbelian.SelfDualHaar (LocalFieldData.ofInstances E) ψ := ⟨ν, hν⟩
  obtain ⟨ε, p, pd, hε, hp, hpd, hroot⟩ := hsep ψ dual
  let A := (Q.localComponent w).padicObject (hQ w).1 (hQ w).2
  let one := rankOneCharacter (1 : J.Carrierˣ →* ℂˣ)
  have hmap : (cE.measure w).measure = ν.measure.map b :=
    (congrArg AdditiveHaarMeasure.measure
      (HarmonicAnalysis.FieldTransport.haarMeasure_symm b.symm hb' hb (cE.measure w))).symm
  have hψ (x : E) : cE.additive w (b x) = ψ x := rfl
  have hψd (x : E) : ((cE.additive w).scale (-1)) (b x) = (ψ.scale (-1)) x := by
    change cE.additive w ((-1 : J.Carrier) * b x) = cE.additive w (b ((-1 : E) * x))
    have h : b ((-1 : E) * x) = (-1 : J.Carrier) * b x := by simp
    rw [h]
  have h1 : one.comp (Matrix.GeneralLinearGroup.map b.toRingHom) =
      rankOneCharacter (1 : Eˣ →* ℂˣ) := rfl
  have h1d : (inverseTransposePullback one).comp (Matrix.GeneralLinearGroup.map b.toRingHom) =
      inverseTransposePullback (rankOneCharacter (1 : Eˣ →* ℂˣ)) := rfl
  let ed : (inverseTransposePullback P).Equiv
      ((inverseTransposePullback A.obj.representation).comp (Matrix.GeneralLinearGroup.map b.toRingHom)) :=
    Representation.Equiv.mk e.toLinearEquiv fun g => by
      change e.toLinearEquiv.toLinearMap.comp (P (inverseTranspose (r + 1) E g)) =
        (A.obj.representation (inverseTranspose (r + 1) J.Carrier
          (Matrix.GeneralLinearGroup.map b.toRingHom g))).comp e.toLinearEquiv.toLinearMap
      rw [inverseTranspose_map]
      exact e.isIntertwining' (inverseTranspose (r + 1) E g)
  have hε' : IsPadicPairEpsilonFactor J (cE.additive w) (cE.measure w) A.obj.representation one ε := by
    apply (RankinSelberg.FieldTransport.isLocalPairEpsilonFactor_comp_iff
      b hb hb' hψ hmap A.obj.representation one ε).mpr
    exact (IsPairEpsilonFactor.congr_equiv e (equivOfRepresentationEq h1.symm)).mp hε
  have hp' : IsPadicPairLPolynomial J (cE.additive w) (cE.measure w) A.obj.representation one p := by
    apply (RankinSelberg.FieldTransport.isLocalPairLPolynomial_comp_iff
      b hb hb' hψ hmap A.obj.representation one p).mpr
    exact (AllField.RankinSelberg.IsPadicPairLPolynomial.congr_equiv
      e (equivOfRepresentationEq h1.symm)).mp hp
  have hpd' : IsPadicPairLPolynomial J ((cE.additive w).scale (-1)) (cE.measure w)
      (inverseTransposePullback A.obj.representation) (inverseTransposePullback one) pd := by
    apply (RankinSelberg.FieldTransport.isLocalPairLPolynomial_comp_iff b hb hb' hψd hmap
      (inverseTransposePullback A.obj.representation) (inverseTransposePullback one) pd).mpr
    exact (AllField.RankinSelberg.IsPadicPairLPolynomial.congr_equiv
      ed (equivOfRepresentationEq h1d.symm)).mp hpd
  obtain ⟨hF, hD⟩ := distinguishedStandardEulerPolynomials L r hr U Ud hu Q Qd hQ hQd Ψ
    cE w ε p pd hε' hp' hpd'
  have hq : residueCardinality w = (LocalFieldData.ofInstances E).residueCardinality :=
    (LocalFieldData.ofInstances E).residueCardinality_of_continuous_ringEquiv
      J.canonicalLocalFieldData b hb hb'
  rw [hF, hD, hq]
  exact hroot

variable {F : Type uF} [Field F] [TopologicalSpace F] [ValuativeRel F]
  [IsNonarchimedeanLocalField F] [CharZero F] [Algebra F E] [FiniteDimensional F E]
  [IsModuleTopology F E] (σ : E ≃ₐ[F] E)
  {s k : ℕ} (h : s * (k + 1) = r + 1)
  {W₁ : Type uW} [AddCommGroup W₁] [Module ℂ W₁]
  (P₁ : Representation ℂ (GeneralLinear (k + 1) E) W₁)
  (S : Representation ℂ (GeneralLinear (r + 1) (padicField w).Carrier) W)
  (η : (padicField w).Carrierˣ →* ℂˣ)

/-- At a finite component that realizes an unramified twist of a transported
supercuspidal orbit product, the forward and reflected dual roots are separated. -/
def DistinguishedEulerRootSeparationOfUnramifiedOrbitStatement : Prop :=
  (@Continuous E (padicField w).Carrier ‹TopologicalSpace E›
    (padicField w).canonicalTopologicalData.topology b) →
  (@Continuous (padicField w).Carrier E (padicField w).canonicalTopologicalData.topology
    ‹TopologicalSpace E› b.symm) →
  0 < r → Ud.realization.IsContragredientOf U.realization →
  P₁.IsIrreducible → IsSupercuspidal P₁ →
  Nonempty (P.Equiv ((sigmaOrbitProduct σ s (Nat.succ_pos k) P₁).comp
    (GeneralLinear.reindex (R := E) (finCongr h)).symm.toMonoidHom)) →
  (padicField w).canonicalTopologicalData.IsUnramifiedCharacter η →
  Nonempty (P.Equiv (S.comp (Matrix.GeneralLinearGroup.map b.toRingHom))) →
  Nonempty ((twist (η.comp determinant) S).Equiv (Q.localComponent w).representation) →
  ∀ x : ℂ, x ≠ 0 → (cE.lPolynomial w).eval x = 0 →
    (cE.dualLPolynomial w).eval ((residueCardinality w : ℂ)⁻¹ / x) ≠ 0

set_option maxHeartbeats 2200000 in
theorem distinguishedEulerRootSeparationOfUnramifiedOrbit :
    DistinguishedEulerRootSeparationOfUnramifiedOrbitStatement Q Qd hQ hQd cE w b P σ h P₁ S η := by
  intro hb hb' hr hUd hI hsc hOrbit hη ⟨eP⟩ ⟨eS⟩
  let J := padicField w
  let T := J.canonicalTopologicalData
  let B := J.canonicalLocalFieldData
  let D := LocalFieldData.ofInstances E
  let : TopologicalSpace J.Carrier := T.topology
  let bU := Units.mapEquiv b.toMulEquiv
  have hηopen : IsOpen (η.ker : Set J.Carrierˣ) := by
    rw [T.eq_unramifiedCharacter η hη]
    exact T.isOpen_ker_unramifiedCharacter _
  let χ : Induction.SmoothCharacter ℂ Eˣ :=
    ⟨η.comp bU.toMonoidHom, hηopen.preimage (hb.units_map b.toMonoidHom)⟩
  have hχ (j : ℕ) (x : Eˣ) :
      χ.toMonoidHom (Units.map (σ ^ j).toRingHom.toMonoidHom x) = χ.toMonoidHom x := by
    let γ := (σ ^ j : E ≃ₐ[F] E)
    have hc : Continuous γ := IsModuleTopology.continuous_of_linearMap γ.toLinearMap
    have hc' : Continuous γ.symm := IsModuleTopology.continuous_of_linearMap γ.symm.toLinearMap
    change η (bU (Units.map γ.toRingHom.toMonoidHom x)) = η (bU x)
    rw [T.eq_unramifiedCharacter η hη]
    have ho : T.ord (b (γ (x : E))) = T.ord (b (x : E)) := by
      change B.ord (b (γ (x : E))) = B.ord (b (x : E))
      rw [D.ord_of_continuous_ringEquiv B b hb hb', D.ord_of_continuous_ringEquiv B b hb hb']
      exact D.ord_of_continuous_ringEquiv D γ.toRingEquiv hc hc' x
    exact congrArg (fun z : ℤ => (η T.uniformizerUnit) ^ z) ho
  let e := (pullbackDeterminantTwistEquiv b eP η).trans
    (BinaryTensor.compEquiv eS (Matrix.GeneralLinearGroup.map b.toRingHom))
  exact distinguishedEulerRootSeparation_of_pullback Q Qd hQ hQd cE w b hb hb' _ hr hUd e
    (hasSeparatedLocalStandardFactors_twist_sigmaOrbit σ h hI hsc hOrbit χ hχ)

end Completion

end Langlands.BaseChange
