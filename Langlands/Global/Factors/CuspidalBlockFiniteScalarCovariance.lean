import Langlands.Global.Factors.CuspidalBlockCompactTensorComparison
import Langlands.Global.Factors.CuspidalBlockGroupedFiniteEvaluation

/-! # Normalized finite parabolic covariance of the cuspidal coefficient pairing -/

noncomputable section

open scoped BigOperators Classical TensorProduct

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

universe u uQ

namespace Langlands.Global.CuspidalBlockInduction

open Automorphic FiniteAdelicGL GeneralLinear AdelicBlockParabolic AdelicBlockDeterminantCharacter
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)

/-- A linear coefficient pairing carries the finite vector covariance to the
scalar parabolic law when Levi action agrees with translation of the argument. -/
theorem finiteEvaluation_scalarParabolic
    {G L P K A W : Type u} [Monoid G] [Monoid L]
    [AddCommGroup A] [Module ℂ A] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G A} {τ : Representation ℂ L W}
    {leftTranslate : P → G → G} {character : P → ℂ} {levi : P → L} {compact : K → G}
    (E : FiniteEvaluationData ρ τ leftTranslate character levi compact)
    {V Z : Type u} [AddCommMonoid V] [Module ℂ V]
    (eval : Z → (W ⊗[ℂ] V) →ₗ[ℂ] ℂ) (translate : Z → L → Z)
    (htranslate : ∀ d (b : W) (c : V) z,
      eval z (τ d b ⊗ₜ[ℂ] c) = eval (translate z d) (b ⊗ₜ[ℂ] c))
    (p : P) (g : G) (a : A) (c : V) (z : Z) :
    eval z (E.evaluate (leftTranslate p g) a ⊗ₜ[ℂ] c) =
      character p * eval (translate z (levi p)) (E.evaluate g a ⊗ₜ[ℂ] c) := by
  let pair : W →ₗ[ℂ] ℂ := (eval z).comp ((TensorProduct.mk ℂ W V).flip c)
  calc
    eval z (E.evaluate (leftTranslate p g) a ⊗ₜ[ℂ] c) =
        pair (character p • τ (levi p) (E.evaluate g a)) :=
      congrArg pair (E.parabolic p g a)
    _ = character p * pair (τ (levi p) (E.evaluate g a)) := map_smul pair _ _
    _ = _ := congrArg (character p * ·) (htranslate (levi p) (E.evaluate g a) c z)

private theorem groupedFiniteLeviAction_apply
    {F : Type u} [Field F] [NumberField F] {n : ℕ} {B : BlockShape n}
    {V : FinitePlace F → Fin B.length → Type u}
    [∀ v i, AddCommGroup (V v i)] [∀ v i, Module ℂ (V v i)]
    {σ : ∀ v i, Representation ℂ (FiniteLocalGL F (B.size i) v) (V v i)}
    (D : BlockInducedReferences F B σ) (d : FiniteLevi F B)
    (b : ⨂[ℂ] i, D.BlockCoefficients i) :
    groupedFiniteLeviAction D d b =
      PiTensorProduct.map (fun i => D.blockRepresentation i (d i)) b :=
  rfl

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
variable {r k : ℕ} {m : Fin k → ℕ} (hm : ∑ i, (m i + 1) = r + 1)
variable {T : ∀ i, CuspidalOperatorRealization F (m i)}
variable (P : ∀ i, CuspidalSpectralPresentation.{u, uQ} (T i))

attribute [local instance] LocalRealization.localRealizationSpaceAddCommGroup

variable (h : ∀ i, HasIrreducibleAdmissibleComponents (P i))

local notation "B" => blockShape hm
local notation "D" => finiteReferences hm P
local notation "Gf" => FiniteAdelicGL F (r + 1)
local notation "Pf" => AdelicBlockParabolic.Finite F B
local notation "Kf" => ↥(FiniteAdelicGL.standardIntegral F (r + 1))
local notation "Vf" => (⨂[ℂ] i, BlockInducedReferences.BlockCoefficients D i)
local notation "Vi" => (⨂[ℂ] q, InfinitePlaceCoefficients T q)
local notation "value" => groupedCoefficientEvaluation hm P h

private local instance (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
private local instance {n : ℕ} (S : OperatorRealization F n) : AddCommGroup S.Space :=
  Submodule.addCommGroup _
private local instance (q : InfinitePlaceFamily.Index F) (i : Fin k) :
    AddCommGroup (InfiniteBlockCoefficient T i q) := Submodule.addCommGroup _

/-- The finite Levi action on the first coefficient factor is right
translation of the paired scalar argument. -/
theorem groupedFiniteLevi_scalar (d : FiniteLevi F B) (b : Vf) (c : Vi)
    (z : FullLevi F B) :
    value z (groupedFiniteLeviAction D d b ⊗ₜ[ℂ] c) =
      value (z * leviPair F B 1 d) (b ⊗ₜ[ℂ] c) := by
  let L := @groupedCoefficientEvaluation F _ _ _ r k m hm T P h z
  let translate := @groupedCoefficientEquiv_finite F _ _ _ r k m hm T P h d
  have ht := translate b c z
  have hx := groupedFiniteLeviAction_apply D d b
  exact (congrArg (fun w : Vf => L (w ⊗ₜ[ℂ] c)) hx).trans ht

/-- The finite evaluations in the grouped cuspidal coefficient space have
normalized parabolic covariance after pairing with the infinite coefficients. -/
def GroupedFiniteScalarCovarianceStatement : Prop :=
  ∀ {A : Type u} [AddCommGroup A] [Module ℂ A] (ρ : Representation ℂ Gf A)
    (E : @FiniteEvaluationData Gf (FiniteLevi F B) Pf Kf A Vf
      _ _ _ _ (groupedFiniteCoefficientGroup D) _ ρ (groupedFiniteLeviAction D)
      (fun p g => p.val * g) (fun p => parabolicHalfCharacter F B (ofFinite F B p))
      (BlockShape.leviProjection B (FiniteAdeles F)) Subtype.val),
    HasFiniteScalarCovariance hm P h E.evaluate

/-- The normalized vector law and scalar Levi translation imply the paired law. -/
theorem hasFiniteScalarCovariance_of_groupedFiniteEvaluation :
    GroupedFiniteScalarCovarianceStatement hm P h := by
  intro A hA mA ρ E
  let translate (z : FullLevi F B) (d : FiniteLevi F B) := z * leviPair F B 1 d
  let pairing := @groupedCoefficientEvaluation F _ _ _ r k m hm T P h
  let shift := @groupedFiniteLevi_scalar F _ _ _ r k m hm T P h
  exact finiteEvaluation_scalarParabolic E pairing translate shift

end Langlands.Global.CuspidalBlockInduction
