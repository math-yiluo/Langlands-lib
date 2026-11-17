import Langlands.Global.RankinSelberg.UnramifiedWhittakerFactorizationProof
import Langlands.Automorphic.CuspidalWhittaker.QuotientTorus
import Langlands.Global.AdelicGLTopology

/-! # Compact-open continuity of actual cuspidal Whittaker coefficients -/

noncomputable section
universe u v
open MeasureTheory
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.RankinSelbergGlobal

local instance continuitySchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance continuitySchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

namespace CuspidalWhittakerContinuity

variable (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r : ℕ} (T : CuspidalOperatorRealization F r)

local instance : AddCommGroup (RationalInvariantFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance : AddCommGroup (StableAutomorphicFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance : AddCommGroup T.Space := Submodule.addCommGroup _

/-- The original actual function, with the compact-open topology. -/
def functionMap : T.Space →ₗ[ℂ] C(AdelicGL F (r + 1), ℂ) :=
  (ContinuousRationalFunctions.toContinuousMap F (r + 1)).comp T.realization.toContinuous

/-- The inherited topology makes the actual function realization continuous. -/
theorem continuous_functionMap : Continuous (functionMap F T) := by
  change Continuous (fun v : T.Space =>
    ContinuousRationalFunctions.toContinuousMap F (r + 1) v.val.val.val)
  exact continuous_induced_dom.comp
    (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val))

/-- Any compact-open continuous family of actual vectors has jointly continuous
Whittaker coefficients. No norm topology on a Hilbert completion is used. -/
theorem continuous_family {X : Type v} [TopologicalSpace X] (f : X → T.Space)
    (hf : Continuous (fun x => functionMap F T (f x)))
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ) :
    Continuous (fun p : X × Points F (r + 1) => cuspWhittaker F T ψ (f p.1) p.2) := by
  have hcpt := Unfolding.compactSpace_unipotentRationalQuotient F (r + 1)
  have hprob := AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F
    (Scheme F (r + 1)) (upperUnipotent F (r + 1))
  have hborel := AdelicSubgroupPoints.rationalQuotientBorelSpace F
    (Scheme F (r + 1)) (upperUnipotent F (r + 1))
  let Γ := AdelicSubgroupPoints.rationalSubgroup F (Scheme F (r + 1))
    (upperUnipotent F (r + 1))
  have hφ : ∀ (p : X × Points F (r + 1)) (b : Γ) (n : unipotentAdelic F (r + 1)),
      cuspFunction F T (f p.1) ((((b : unipotentAdelic F (r + 1)) * n :
          unipotentAdelic F (r + 1)) : Points F (r + 1)) * p.2) *
        starRingEnd ℂ (genericCharacter F r ψ (fun _ => 1)
          ((b : unipotentAdelic F (r + 1)) * n)) =
      cuspFunction F T (f p.1) ((n : Points F (r + 1)) * p.2) *
        starRingEnd ℂ (genericCharacter F r ψ (fun _ => 1) n) := by
    intro p b n
    rw [Subgroup.coe_mul, mul_assoc,
      Unfolding.cuspFunction_rational_mul F T (f p.1)
        (Unfolding.mem_rationalSubgroup_of_unipotent F b),
      Unfolding.genericCharacter_rational_mul F r ψ hψ]
  have hint : ∀ (p : X × Points F (r + 1))
      (q : AdelicSubgroupPoints.RationalQuotient F (Scheme F (r + 1))
        (upperUnipotent F (r + 1))),
      cuspFunction F T (f p.1)
          (((Quotient.out q : unipotentAdelic F (r + 1)) : Points F (r + 1)) * p.2) *
        starRingEnd ℂ (genericCharacter F r ψ (fun _ => 1) (Quotient.out q)) =
      LeftCosetSpace.lift Γ (fun n : unipotentAdelic F (r + 1) =>
        cuspFunction F T (f p.1) ((n : Points F (r + 1)) * p.2) *
          starRingEnd ℂ (genericCharacter F r ψ (fun _ => 1) n)) (hφ p) q := by
    intro p q
    conv_rhs => rw [← Quotient.out_eq q]
    rfl
  unfold cuspWhittaker generalLinearWhittakerFunction subgroupCharacterCoefficient
  simp_rw [hint]
  refine CuspidalWhittaker.continuous_integral_of_continuous_uncurry _ ?_
  have hq : IsOpenQuotientMap (Prod.map
      (id : X × Points F (r + 1) → X × Points F (r + 1)) (LeftCosetSpace.mk Γ)) :=
    IsOpenQuotientMap.id.prodMap (LeftCosetSpace.isOpenQuotientMap_mk Γ)
  rw [hq.isQuotientMap.continuous_iff]
  have hcusp : Continuous (fun p : (X × Points F (r + 1)) × unipotentAdelic F (r + 1) =>
      cuspFunction F T (f p.1.1) ((p.2 : Points F (r + 1)) * p.1.2)) := by
    have hpair : Continuous (fun p :
        (X × Points F (r + 1)) × unipotentAdelic F (r + 1) =>
        (functionMap F T (f p.1.1),
          GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)
            ((p.2 : Points F (r + 1)) * p.1.2))) :=
      (hf.comp (continuous_fst.comp continuous_fst)).prodMk
        ((GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)).continuous.comp
          ((continuous_subtype_val.comp continuous_snd).mul
            (continuous_snd.comp continuous_fst)))
    exact (AdelicGL.continuous_evaluation F (r + 1) (V := ℂ)).comp hpair
  have hc : Continuous (fun p : (X × Points F (r + 1)) × unipotentAdelic F (r + 1) =>
      cuspFunction F T (f p.1.1) ((p.2 : Points F (r + 1)) * p.1.2) *
        starRingEnd ℂ (genericCharacter F r ψ (fun _ => 1) p.2)) :=
    hcusp.mul (Complex.continuous_conj.comp
      ((Unfolding.continuous_genericCharacter F r ψ hψ.1 _).comp continuous_snd))
  exact hc.congr fun p => rfl

/-- The vector and the adelic point vary jointly in the actual coefficient. -/
theorem continuous_coefficient (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) :
    Continuous (fun p : T.Space × Points F (r + 1) => cuspWhittaker F T ψ p.1 p.2) :=
  continuous_family F T id (continuous_functionMap F T) ψ hψ

/-- The coefficient at a fixed group point is continuous in the realized vector. -/
theorem continuous_at_point (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (g : Points F (r + 1)) :
    Continuous (fun v : T.Space => cuspWhittaker F T ψ v g) := by
  have hv : Continuous (fun v : T.Space => (v, g)) :=
    continuous_id.prodMk continuous_const
  simpa only [Function.comp_def] using (continuous_coefficient F T ψ hψ).comp hv

/-- The actual Whittaker functional at a fixed point, with its inherited continuity. -/
def functionalCLM (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (g : Points F (r + 1)) :
    T.Space →L[ℂ] ℂ := by
  refine ⟨UnramifiedWhittaker.whittakerFunctional F ψ hψ T g, ?_⟩
  exact continuous_at_point F T ψ hψ g

@[simp]
theorem functionalCLM_apply (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (g : Points F (r + 1)) (v : T.Space) :
    functionalCLM F T ψ hψ g v = cuspWhittaker F T ψ v g := rfl

end CuspidalWhittakerContinuity

/-- A compact-open continuity input for the analytic multiplicity-one comparison.
It makes no claim about the smooth topology of any Hilbert globalization. -/
def CuspidalWhittakerCompactOpenContinuityStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
    (T : CuspidalOperatorRealization F r) (ψ : AddChar (Adeles F) ℂ),
    IsStandardAdditiveCharacter F ψ →
      Continuous (fun p : T.Space × Points F (r + 1) => cuspWhittaker F T ψ p.1 p.2)

/-- Compact integration proves the stated continuity of actual coefficients. -/
theorem cuspidalWhittakerCompactOpenContinuity :
    CuspidalWhittakerCompactOpenContinuityStatement.{u} :=
  fun F _ _ _ _r T ψ hψ => CuspidalWhittakerContinuity.continuous_coefficient F T ψ hψ

end Langlands.Automorphic
