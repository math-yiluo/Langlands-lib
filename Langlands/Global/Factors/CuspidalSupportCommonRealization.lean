import Langlands.Automorphic.BlockTermCentralCharacter
import Langlands.Automorphic.CuspidalLeviUnitaryCoefficients
import Langlands.Automorphic.CuspidalOperatorDirectSum
import Langlands.Global.Factors.CuspidalSupportCommonFiniteCovariance
import Langlands.Global.Factors.CuspidalSupportSelectedKernel
import Langlands.Representation.TensorProduct.FiniteSupportCoordinates

/-! # A common cuspidal realization from the actual selected period -/

noncomputable section

open scoped BigOperators Classical TensorProduct Matrix.Norms.Operator

set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxHeartbeats 140000
set_option maxHeartbeats 1600000

universe u

namespace Langlands.Global

open Langlands.Automorphic Langlands.GeneralLinear ArchimedeanGL FiniteParametrizedBlockInduction
open FiniteVectors

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

attribute [local instance] subquotientRationalGroup subquotientContinuousGroup
  subquotientSmoothGroup subquotientFormGroup subquotientStableGroup subquotientRealizationGroup

local instance selectedCoefficientOperatorRing (d : ℕ) :
    Ring (automorphicOperatorAlgebra F d) := Subalgebra.toRing _

attribute [local instance 100] LieRing.ofAssociativeRing

section InitialCoefficient

variable {r c : ℕ} {m : Fin c → ℕ} (hm : ∑ i, (m i + 1) = r + 1)
  (Q : IrreducibleOperatorSubquotient F r) (S₀ : OperatorRealization F (r + 1))
  {W : Type u} [AddCommGroup W] [Module ℂ W]
  (A : automorphicOperatorAlgebra F (r + 1) →ₐ[ℂ] Module.End ℂ W)

local notation "N" => r + 1
local notation "B" => (⟨c, fun i => m i + 1, fun _ => Nat.succ_pos _, hm⟩ : BlockShape N)
local notation "Period" => TranslatedBlockConstantTerms F B S₀
local notation "P" => translatedBlockLeviRestriction F B S₀
local notation "ρ" => (AlgHom.toMonoidHom' A).comp (finiteOperator F N)
local notation "κ" => (AlgHom.toMonoidHom' A).comp (compactOperator F N)
local notation "α" => translatedBlockTermOperatorAction F B S₀
local notation "β" => blockConstantTermScalarAction F B
local notation "φ" => realizedBlockConstantTerm F B S₀

variable (q : Representation.IntertwiningMap (AlgHom.toMonoidHom' A) Q.representation)
  (j : W →ₗ[ℂ] TranslatedBlockConstantTerms F ⟨c, fun i => m i + 1, fun _ => Nat.succ_pos _, hm⟩ S₀)

/-- A selected eigenperiod with vanishing strict refinements gives the
common restored realization after projection onto one cuspidal block tuple. -/
theorem commonRealization_of_selectedPeriod
    (hq : Function.Surjective q) (hj : Function.Injective j)
    (hji : ∀ (a : automorphicOperatorAlgebra F N) (w : W), j (A a w) = α a (j w))
    (hreg : HasRegularCompactOperatorAction A) (hf : IsSmooth ρ)
    (v : W) (hv : orbitSpan (AlgHom.toMonoidHom' A) v = ⊤)
    (χ : (Fin c → Ideles F) →ₜ* ℂˣ)
    (hχ : ∀ (w : W) (z : Fin c → Ideles F),
      translatedFunctionAction β φ z (j w) = (χ z : ℂ) • j w)
    (hprincipal : ∀ a : Fin c → Fˣ, χ (fun i => diagonalUnits F (a i)) = 1)
    (href : ∀ (w : S₀.Space) (t : Finset (Fin r)), (B).cuts ⊂ t →
      finiteSmoothBlockConstantTerm F (@standardBlockWeight N t) (S₀.ambient w) = 0) :
    HasRestoredCuspidalIdentityRealization Q := by
  let ω := blockTermHeckeCharacter F B χ hprincipal
  let R := cuspidalLeviUnitaryRealization F B ω
  let μ := cuspidalLeviUnitarizingTwist F B ω
  let ν := fun i => (μ i)⁻¹
  let : ∀ i : Fin c, AddCommGroup (R i).Space := fun _ => Submodule.addCommGroup _
  let V := PiTensorProduct ℂ (fun i : Fin c => (R i).Space)
  let tensorGroup : AddCommGroup V := PiTensorProduct.instAddCommGroup
  let : Zero V := ⟨tensorGroup.zero⟩
  let D : ∀ i, CuspidalOperatorDirectSum (R i) := fun i =>
    cuspidalOperatorDirectSumOfUnitaryCentralCharacter (R i)
      (cuspidalLeviUnitaryRealization_isCuspidal F B ω i)
      (cuspidalLeviUnitaryCharacter F B ω i) (cuspidalLeviUnitaryCharacter_isUnitary F B ω i)
      (cuspidalLeviUnitaryRealization_hasCentralCharacter F B ω i)
  obtain ⟨g, hg, _⟩ := exists_unitaryCuspidalLeviCoefficients F B ω S₀ j A hji hreg.1
    χ.toMonoidHom hχ (blockTermHeckeCharacter_onIdeles F B χ hprincipal) href
  let J := ∀ i : Fin c, (D i).Index
  let T (a : J) : ∀ i, CuspidalOperatorRealization F (m i) := fun i => (D i).factor (a i)
  let p (a : J) := fun i => (D i).project (a i)
  let T₀ (a : J) := fun i => (T a i).heckeDeterminantTwist (ν i)
  let e (a : J) := projectedRestoredLeviCoefficient B R (fun i => (T a i).realization) (p a) ν g
  let e₀ (a : J) := PiTensorProduct.map (fun i => (p a i).toLinearMap)
  let E : ∀ i, (R i).Space →ₗ[ℂ] (AdelicGL F (m i + 1) → ℂ) :=
    fun i => operatorRealizationFunctionEvaluation (R i)
  have he (w : W) (b : AdelicBlockParabolic.FullLevi F B) :
      functionTensorEvaluation E (g w) b = cuspidalLeviDeterminantWeight μ b * P (j w) b := hg w b
  have hz (w : W) : g w = 0 ↔ P (j w) = 0 :=
    cuspidalLeviCoefficient_eq_zero_iff hm R μ (g w) (P (j w)) (he w)
  have hproj (a : J) (w : W) : e a w = 0 ↔ e₀ a (g w) = 0 := by
    let Eₐ := PiTensorProduct.congr (fun i => ((T a i).realization.heckeDeterminantTwistEquiv (ν i)).toLinearEquiv)
    change Eₐ (e₀ a (g w)) = 0 ↔ e₀ a (g w) = 0
    exact Eₐ.map_eq_zero_iff
  have hpart (i : Fin c) (x : (R i).Space) :
      ∃ s : Finset (D i).Index, ∀ a ∉ s, ((D i).project a).toLinearMap x = 0 := by
    obtain ⟨s, hs, _⟩ := (D i).finite_sum x
    exact ⟨s, hs⟩
  have hpoint (w : W) : {a | e a w ≠ 0}.Finite :=
    (finiteSupportTensorCoordinateMap_finite (fun i a => ((D i).project a).toLinearMap)
      hpart (g w)).subset fun a ha hz => ha ((hproj a w).mpr hz)
  have hkill (w : W) (hw : ∀ a l d, compactFiniteCoefficientEvaluation A (e a) l d w = 0) : q w = 0 := by
    have hjw : j w = 0 := by
      apply translatedBlockTerm_zero_of_compact_finite_restrictions F B S₀ (j w)
      intro l d
      let w' := κ l (ρ d w)
      have hg' : g w' = 0 := finiteSupportTensorCoordinateMap_detects
        (fun i a => ((D i).project a).toLinearMap) hpart
        (fun i x hx => CuspidalOperatorDirectSum.project_eq_zero_detects (R i) (D i) x hx)
        (g w') (fun a => (hproj a w').mp (hw a l d))
      have hact : j w' = α (compactOperator F N l) (α (finiteOperator F N d) (j w)) :=
        (hji (compactOperator F N l) _).trans
          (congrArg (fun x => α (compactOperator F N l) x) (hji (finiteOperator F N d) w))
      exact (congrArg P hact).symm.trans ((hz w').mp hg')
    have hw₀ := hj (hjw.trans j.map_zero.symm)
    exact (congrArg (fun x : W => q.toLinearMap x) hw₀).trans q.toLinearMap.map_zero
  have hcov (s : AdelicBlockParabolic.Finite F B) (w : W) :
      g (ρ s.val w) = restoringWeight hm ν s • ((B).blockTensor (fun i => (R i).finiteRepresentation))
        ((B).leviProjection (FiniteAdeles F) s) (g w) := by
    let d := (B).leviProjection (FiniteAdeles F) s
    let b : AdelicBlockParabolic.FullLevi F B := fun i => AdelicGL.ofFinite F (m i + 1) (d i)
    have hc : restoringWeight hm ν s * cuspidalLeviDeterminantWeight μ b = 1 :=
      cuspidalLeviDeterminantWeight_inv_mul hm μ b
    refine cuspidalLeviCoefficient_finiteCovariance hm R μ d (restoringWeight hm ν s)
      (g w) (g (ρ s.val w)) (P (j w)) hc (he w) ?_
    intro t
    calc
      _ = cuspidalLeviDeterminantWeight μ t * P (j (ρ s.val w)) t := he _ t
      _ = cuspidalLeviDeterminantWeight μ t *
          P (α (finiteOperator F N s.val) (j w)) t :=
        congrArg (fun x : Period => cuspidalLeviDeterminantWeight μ t * P x t)
          (hji (finiteOperator F N s.val) w)
      _ = _ := congrArg (cuspidalLeviDeterminantWeight μ t * ·)
        (translatedBlockLeviRestriction_finiteParabolic F B S₀ s (j w) t)
  have hOps (a : J) := projectedRestoredLeviCoefficient_operatorEquations B R
    (fun i => (T a i).realization) (p a) g A S₀ j μ hji he
  refine hasRestoredCuspidalIdentityRealization_of_sectionProjections hm Q A q T₀ e hq hreg hf v hv
    hpoint hkill ?_ (fun a => (hOps a).1) (fun a => (hOps a).2.1) (fun a => (hOps a).2.2)
  intro a s w
  exact finiteCovariance_projectedRestored hm ν R (T a) (p a) g ρ hcov s w

end InitialCoefficient

/-- Every irreducible automorphic operator quotient has a common restored cuspidal
coefficient realization over its own number field. -/
def CommonCuspidalRealizationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (Q : IrreducibleOperatorSubquotient F r), HasRestoredCuspidalIdentityRealization Q

/-- A proof of the common realization and the general real place parameters
implies the exact statement. -/
theorem cuspidalSupportEveryPlace_of_commonRealization
    (hModel : CommonCuspidalRealizationStatement.{u})
    (hParam : ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
      (r : ℕ) (T : CuspidalOperatorRealization F r) (v : {v : NumberField.InfinitePlace F // v.IsReal}),
      ∃ ds, T.realization.HasRealPlaceParameter v ds) : CuspidalSupportEveryPlaceStatement.{u} := by
  refine cuspidalSupportEveryPlace_of_projectedCuspidalBlocks ?_ hParam
  intro F _ _ _ r Q
  exact hasProjectedCuspidalBlockRealization_of_restoredIdentity Q (hModel F r Q)

end Langlands.Global
