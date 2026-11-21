import Langlands.Global.AdelicBlockCompactPolynomialSections
import Langlands.Global.AdelicBlockMultiplicityCoefficients
import Langlands.Global.AdelicBlockProjectedSpecialization
import Langlands.Global.AdelicBlockSliceTensorSeed
import Langlands.Global.AdelicFiniteInfiniteOperatorTensor

/-! # A block inducing tensor with an actual nonzero infinite factor -/

noncomputable section

open scoped Classical Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1100000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 100000

universe u

namespace Langlands.Global.AdelicBlockScalarSections

open Automorphic GeneralLinear AdelicBlockParabolic AdelicBlockDeterminantCharacter
open ArchimedeanGL AdelicFiniteInfiniteOperatorTensor

variable (F : Type u) [Field F] [NumberField F] (r : ℕ) (B : BlockShape (r + 1))
variable (S : ∀ i : Fin B.length, OperatorRealization F (B.size i))
variable {A : Type u} [AddCommGroup A] [Module ℂ A]
variable (ρ : Representation ℂ (FiniteAdelicGL F (r + 1)) A)

local notation "G" => FiniteAdelicGL F (r + 1)
local notation "K" => standardInfiniteCompact F (r + 1)
local notation "W" => smoothCompactFiniteSections F B S
local notation "Wf" => FiniteSmoothRealizedSections F B S
local notation "Ops" => FreeOperatorAlgebra F (r + 1)
local notation "E" => EnvelopingAlgebra F (r + 1)

local instance multSourceFiniteGroup : AddCommGroup Wf := Submodule.addCommGroup _
local instance multSourceSmoothGroup : AddCommGroup W := Submodule.addCommGroup _
local instance multSourceInfiniteGroup : AddCommGroup (SmoothFunctions F (r + 1)) :=
  Submodule.addCommGroup _

private def finiteLeviParabolic (d : FiniteLevi F B) : AdelicBlockParabolic.Finite F B :=
  B.leviInParabolic (FiniteAdeles F) d

section Operators

variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable (ef : FiniteAdelicGL F (r + 1) → A →ₗ[ℂ] V)
variable (hr : ∀ (d g : FiniteAdelicGL F (r + 1)) (a : A), ef g (ρ d a) = ef (g * d) a)

local notation "I" => sliceTensorCoefficients F B S ef
local notation "κ" => sliceTensorCompactAction F B S ef
local notation "δ" => sliceTensorEnvelopingAction F B S ef
local notation "J" => sliceTensorSectionMap F B S ef
local notation "a₀" => blockSectionOperatorAction F r B S 0
local instance multSourceCoefficientGroup : AddCommGroup I := Submodule.addCommGroup (I)

include hr in
/-- Pairing the finite inducing tensor with the invariant infinite coefficients
intertwines every actual free adelic operator at the original parameter. -/
def sliceTensorOperatorIntertwiner :
    Representation.IntertwiningMap (tensorOperatorAction F (r + 1) ρ κ δ).toMonoidHom
      (a₀).toMonoidHom where
  toLinearMap := J
  isIntertwining' a := by
    apply LinearMap.ext
    intro t
    change J (tensorOperatorAction F (r + 1) ρ κ δ a t) = a₀ a (J t)
    induction a using FreeAlgebra.induction generalizing t with
    | grade0 c => simp only [AlgHom.commutes, Module.algebraMap_end_apply, map_smul]
    | grade1 a =>
      rcases a with (g | k) | b
      · simp only [tensorOperatorAction, FreeAlgebra.lift_ι_apply,
          blockSectionOperatorAction_finite_at_zero]
        exact sliceTensorSectionMap_finite F B S ef ρ hr g t
      · simp only [tensorOperatorAction, FreeAlgebra.lift_ι_apply, blockSectionOperatorAction_compact]
        exact sliceTensorSectionMap_compact F B S ef k t
      · simp only [tensorOperatorAction, FreeAlgebra.lift_ι_apply,
          blockSectionOperatorAction_enveloping_at_zero]
        exact sliceTensorSectionMap_enveloping F B S ef b t
    | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
    | mul a b ha hb => simp only [map_mul, Module.End.mul_apply, ha, hb]

variable {U : Type u} [AddCommGroup U] [Module ℂ U]
variable (π : Representation ℂ (FiniteLevi F B) V)
variable (σI : Representation ℂ (infiniteCompactIntersection F B) U)
variable (ce : V ⊗[ℂ] U →ₗ[ℂ] coefficientValues F B S)
variable (seed : MultiplicityCompactPolynomial (V := U) (infiniteCompactMatrixInclusion F B) σI)

local notation "X" => FullLevi F B
local notation "P" => AdelicBlockParabolic.Finite F B
local notation "KF" => FiniteAdelicGL.standardIntegral F (r + 1)
local notation "χ" => fun p : P => (parabolicHalfCharacter F B (ofFinite F B p) : ℂ)

include hr seed in
private theorem exists_tensorSource_of_seed [Nontrivial A] [π.IsIrreducible]
    (hρ : IsSmooth ρ) (hπ : IsAdmissible π)
    (hsep : Function.Injective (fun a : A => fun l : KF => ef l.val a))
    (hcov : ∀ (p : P) (g : G) (a : A),
      ef (p.val * g) a = χ p • π (B.leviProjection (FiniteAdeles F) p) (ef g a))
    (hleft : ∀ (p : P) (g : G) (a : A) (w : U) (m : X),
      (ce (ef (p.val * g) a ⊗ₜ[ℂ] w)).val m = χ p *
        (ce (ef g a ⊗ₜ[ℂ] w)).val (m * leviPair F B 1 (B.leviProjection (FiniteAdeles F) p)))
    (hcompact : ∀ (p : infiniteCompactIntersection F B) (v : V) (w : U) (m : X),
      (ce (v ⊗ₜ[ℂ] σI p w)).val m = (ce (v ⊗ₜ[ℂ] w)).val
        (m * leviPair F B (B.leviProjection (InfiniteAdeles F) p.val) 1))
    (he : Function.Injective ce) :
    ∃ (Y : Type u) (_ : AddCommGroup Y) (_ : Module ℂ Y) (_ : Nontrivial Y)
      (kAct : Representation ℂ K Y) (dAct : E →ₐ[ℂ] Module.End ℂ Y)
      (jAct : Representation.IntertwiningMap (tensorOperatorAction F (r + 1) ρ kAct dAct).toMonoidHom
        (blockSectionOperatorAction F r B S 0).toMonoidHom), Function.Injective jAct := by
  let ν (d : FiniteLevi F B) : ℂ := χ (finiteLeviParabolic F r B d)
  let shift (d : FiniteLevi F B) (g : G) : G := (finiteLeviParabolic F r B d).val * g
  have hν (d : FiniteLevi F B) : ν d ≠ 0 := Units.ne_zero _
  have hc (d : FiniteLevi F B) (g : G) : ef (shift d g) = ν d • (π d).comp (ef g) := by
    apply LinearMap.ext
    intro a
    have h := hcov (finiteLeviParabolic F r B d) g a
    have hd : B.leviProjection (FiniteAdeles F) (finiteLeviParabolic F r B d) = d :=
      B.leviProjection_section (FiniteAdeles F) d
    exact h.trans (congrArg (fun v => ν d • π v (ef g a)) hd)
  have hn : ∃ (a : A) (l : KF), ef l.val a ≠ 0 := by
    obtain ⟨a, ha⟩ := exists_ne (0 : A)
    refine ⟨a, ?_⟩
    by_contra! h
    exact ha (hsep (funext fun l => (h l).trans (map_zero (ef l.val)).symm))
  have hspan := InducedSliceEvaluation.span_values_eq_top ef π shift ν hν hc
    (show ∃ g a, ef g a ≠ 0 from by
      obtain ⟨a, l, h⟩ := hn
      exact ⟨l.val, a, h⟩)
  obtain ⟨f, hf, hfne⟩ := exists_smoothSectionFamily_of_compactPolynomial F B S ρ ef ce σI seed
    hr hleft hcompact hρ he hn
  let : Nontrivial I := nontrivial_sliceTensorCoefficients_of_seed F B S ef
    (fun k => seed.inclusion (seed.polynomial (compactMatrix F k))) ce f hf hleft hspan hfne
  let j := sliceTensorOperatorIntertwiner F r B S ρ ef hr
  have hInjective : Function.Injective j := sliceTensorSectionMap_injective F B S ef
    (InducedSliceEvaluation.slices_injective ef π shift ν hν hc (I).subtype
      (I).subtype_injective (fun a ha => hsep (funext fun l =>
        (ha l.val).trans (map_zero (ef l.val)).symm))
      (fun f => (admissibleSchur_scalarEndomorphism π hπ inferInstance f).exists))
  exact ⟨I, inferInstance, inferInstance, inferInstance, κ, δ, j, hInjective⟩

end Operators

local instance multSourceRationalGroup (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance multSourceContinuousGroup (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance multSourceFiniteSmoothGroup (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance multSourceFormsGroup (n : ℕ) : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance multSourceStableGroup (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance multSourceRealizationGroup {n : ℕ} (D : OperatorRealization F n) : AddCommGroup D.Space :=
  Submodule.addCommGroup _

variable (M : ∀ i, Subrepresentation (S i).finiteRepresentation)
local instance multSourceBlockGroup (i : Fin B.length) : AddCommGroup (M i).toSubmodule :=
  Submodule.addCommGroup _
local notation "V" => fun i : Fin B.length => Subrepresentation.toSubmodule (M i)
local notation "Vf" => (⨂[ℂ] i, V i)
set_option quotPrecheck false in
local notation "Vi" => (⨂[ℂ] i, (S i).FiniteMultiplicity (M i))
local notation "c" => groupedMultiplicityCoefficients F B S M
local notation "τ" => FiniteTensor.external (fun i => Subrepresentation.toRepresentation (M i))
local notation "σ" => infiniteMultiplicityCompactAction F B S M

variable (ef : FiniteAdelicGL F (r + 1) → A →ₗ[ℂ]
  (⨂[ℂ] i, (M i).toSubmodule))

private theorem groupedMultiplicityCoefficients_compactIntersection
    (p : infiniteCompactIntersection F B) (v : Vf) (w : Vi) (z : FullLevi F B) :
    (c (v ⊗ₜ[ℂ] σ p w)).val z =
      (c (v ⊗ₜ[ℂ] w)).val (z * leviPair F B (B.leviProjection (InfiniteAdeles F) p.val) 1) := by
  let k := infiniteCompactLeviProjection F B p
  let D : Module.End ℂ Vi := PiTensorProduct.map (fun i => (S i).finiteMultiplicityCompact (M i) (k i))
  have ht : D.lTensor Vf (v ⊗ₜ[ℂ] w) = v ⊗ₜ[ℂ] σ p w := LinearMap.lTensor_tmul Vf D v w
  exact (congrArg (fun t : Vf ⊗[ℂ] Vi => (c t).val z) ht.symm).trans
    (groupedMultiplicityCoefficients_compact F B S M k (v ⊗ₜ[ℂ] w) z)

/-- The finite parabolic covariance needed of evaluations into the actual
finite Levi coefficient tensor. -/
def HasFiniteInducingCovariance : Prop :=
  ∀ (p : AdelicBlockParabolic.Finite F B) (g : G) (a : A),
    ef (p.val * g) a = (parabolicHalfCharacter F B (ofFinite F B p) : ℂ) •
      τ (B.leviProjection (FiniteAdeles F) p) (ef g a)

variable (hl : HasFiniteInducingCovariance F r B S M ef)

include hl in
private theorem groupedMultiplicityCoefficients_parabolic
    (p : AdelicBlockParabolic.Finite F B) (g : G) (a : A) (w : Vi) (z : FullLevi F B) :
    (c (ef (p.val * g) a ⊗ₜ[ℂ] w)).val z =
      (parabolicHalfCharacter F B (ofFinite F B p) : ℂ) *
        (c (ef g a ⊗ₜ[ℂ] w)).val (z * leviPair F B 1 (B.leviProjection (FiniteAdeles F) p)) := by
  let d := B.leviProjection (FiniteAdeles F) p
  let v := ef g a
  let χ : ℂ := parabolicHalfCharacter F B (ofFinite F B p)
  let L : Vf →ₗ[ℂ] ℂ := (LinearMap.proj z).comp ((coefficientValues F B S).subtype.comp
    ((c).comp ((TensorProduct.mk ℂ Vf Vi).flip w)))
  have hl' : ef (p.val * g) a = χ • τ d v := hl p g a
  have ht : (τ d).rTensor Vi (v ⊗ₜ[ℂ] w) = τ d v ⊗ₜ[ℂ] w := LinearMap.rTensor_tmul Vi (τ d) w v
  have h := (congrArg (fun t : Vf ⊗[ℂ] Vi => (c t).val z) ht.symm).trans
    (groupedMultiplicityCoefficients_finite F B S M d (v ⊗ₜ[ℂ] w) z)
  change L (ef (p.val * g) a) = _
  calc
    L (ef (p.val * g) a) = L (χ • τ d v) := congrArg L hl'
    _ = χ * L (τ d v) := map_smul L χ _
    _ = _ := congrArg (χ * ·) h

variable (hr : ∀ (d g : FiniteAdelicGL F (r + 1)) (a : A), ef g (ρ d a) = ef (g * d) a)

include hr hl in
/-- A faithful finite inducing evaluation into actual admissible finite factors
gives the full inducing tensor with a nonzero infinite carrier. -/
theorem exists_multiplicityTensorSource [Nontrivial A]
    (hρ : IsSmooth ρ)
    (hS : ∀ i, (S i).IsIrreducible) (hm : ∀ i, M i ≠ ⊥)
    (hI : ∀ i, (M i).toRepresentation.IsIrreducible)
    (hA : ∀ i, IsAdmissible (M i).toRepresentation)
    (hsep : Function.Injective (fun a : A => fun l : FiniteAdelicGL.standardIntegral F (r + 1) => ef l.val a)) :
    ∃ (I : Type u) (_ : AddCommGroup I) (_ : Module ℂ I) (_ : Nontrivial I)
      (κ : Representation ℂ K I) (δ : E →ₐ[ℂ] Module.End ℂ I)
      (J : Representation.IntertwiningMap (tensorOperatorAction F (r + 1) ρ κ δ).toMonoidHom
        (blockSectionOperatorAction F r B S 0).toMonoidHom), Function.Injective J := by
  let : ∀ i, (M i).toRepresentation.IsIrreducible := hI
  let hschur (i : Fin B.length) (f : (M i).toRepresentation.IntertwiningMap (M i).toRepresentation) :=
    (admissibleSchur_scalarEndomorphism _ (hA i) (hI i) f).exists
  let : (τ).IsIrreducible := FiniteTensor.isIrreducible_external _ hschur
  have htA : IsAdmissible (τ) := FiniteTensor.isAdmissible_external _ hA
  have he := (groupedMultiplicityCoefficients_bijective F B S M hS hm hI hA).1
  obtain ⟨seed⟩ := exists_infiniteMultiplicityCompactSeed F B S M hm hI
  exact exists_tensorSource_of_seed (U := Vi) F r B S ρ ef hr (τ) σ c seed hρ htA hsep hl
    (groupedMultiplicityCoefficients_parabolic F r B S M ef hl)
    (groupedMultiplicityCoefficients_compactIntersection F r B S M) he

end Langlands.Global.AdelicBlockScalarSections
