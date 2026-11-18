import Langlands.Representation.Plancherel.NestedStandardIntertwiningQuotient
import Langlands.HarmonicAnalysis.SmoothWeakFubini
import Langlands.Representation.Smooth.Transfer.GroupEquivalence

/-! # Restricting the weak standard integral to an intermediate Levi -/

noncomputable section

open CategoryTheory MeasureTheory
open Langlands.Aubert.General Langlands.Induction

namespace Langlands.HarmonicAnalysis.SmoothWeakIntegral

/-- Pullback by a continuous group equivalence preserves the scalar tests
and the same representing vector. -/
theorem hasIntegral_comp_continuousMulEquiv_iff
    {X H M V : Type*} [MeasurableSpace X] [Group H] [TopologicalSpace H]
    [Group M] [TopologicalSpace M] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ M V) (e : H ≃ₜ* M) (μ : Measure X) (f : X → V) (v : V) :
    HasIntegral (ρ.comp e.toMonoidHom) μ f v ↔ HasIntegral ρ μ f v := by
  constructor
  · intro h ℓ
    exact h ⟨ℓ.val, (isSmoothVector_dual_comp_continuousMulEquiv_iff ρ e ℓ.val).mpr ℓ.property⟩
  · intro h ℓ
    exact h ⟨ℓ.val, (isSmoothVector_dual_comp_continuousMulEquiv_iff ρ e ℓ.val).mp ℓ.property⟩

end Langlands.HarmonicAnalysis.SmoothWeakIntegral

namespace Langlands.Plancherel.StandardIntertwining

universe u uV

variable {G : Type u} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U Q L N U' : Subgroup G}
  [LocallyCompactSpace L] [NonarchimedeanGroup L]
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hL : IsSemidirectDecomposition (P.subgroupOf L) (M.subgroupOf L) (U.subgroupOf L))
  (hML : M ≤ L) (hQ : IsSemidirectDecomposition Q L N)
  (hU'Q : U' ≤ Q) (hNU : N ≤ U) (hNU' : N ≤ U') (hπ : Continuous hQ.projection)
  (A : SmoothRep.{0, u, uV} ℂ M)

local notation "hUi" => hU.preimage (continuous_subtype_val : Continuous (Subtype.val : L → G))
local notation "Ai" => SmoothRep.pullback (subgroupOfContinuousEquiv hML) A
set_option quotPrecheck false in
local notation "XG" => ↥((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A)
set_option quotPrecheck false in
local notation "XL" => ↥((DynamicNormalization.leviTwistedInductionFunctor hL hUi).obj Ai)
local notation "qG" => QuotientSpace (U := U) U'
local notation "qL" => QuotientSpace (U := U.subgroupOf L) (U'.subgroupOf L)

/-- The usual induction-in-stages restriction at an ambient point removes
the outer half modulus on the intermediate Levi. -/
def NestedRestrictionFormula (c : L →* ℂˣ) (f : XG) (g : G) (φ : XL) : Prop :=
  ∀ l : L, eval (P.subgroupOf L) (leviInflatedInducingRepresentation hL hUi Ai) φ l =
    (↑(c l)⁻¹ : ℂ) • eval P (leviInflatedInducingRepresentation h hU A) f ((l : G) * g)

local instance nestedIntegralAmbientMeasurable : MeasurableSpace qG := borel _
local instance nestedIntegralAmbientBorel : BorelSpace qG := ⟨rfl⟩
local instance nestedIntegralLeviMeasurable : MeasurableSpace qL := borel _
local instance nestedIntegralLeviBorel : BorelSpace qL := ⟨rfl⟩

/-- Push forward the actual ambient quotient measure to the inner quotient. -/
def nestedQuotientMeasure (ν : Measure (QuotientSpace (U := U) U')) : Measure qL := by
  let e : qG ≃ₜ qL := nestedRadicalQuotientHomeomorph hQ hU'Q hNU hNU' hπ
  exact Measure.map (fun x : qG => e x) ν

variable (ν : Measure (QuotientSpace (U := U) U'))

local notation "νL" => nestedQuotientMeasure hQ hU'Q hNU hNU' hπ ν

/-- The weak integral of the inner restriction is the restriction of the
ambient weak integral. The inner measure is the exact pushforward. -/
theorem HasIntegral.nested_restriction
    (c : L →* ℂˣ)
    (hc : ∀ x : U'.subgroupOf L, c x.val = 1)
    {f : XG} {Jf : G → A} (hf : HasIntegral h hU U' A ν f Jf)
    (g : G) (φ : XL) (hφ : NestedRestrictionFormula h hU hL hML A c f g φ) :
    HasIntegral hL hUi (U'.subgroupOf L) Ai νL φ
      (fun l => (↑(c l)⁻¹ : ℂ) • Jf ((l : G) * g)) := by
  intro l
  let e := nestedRadicalQuotientHomeomorph hQ hU'Q hNU hNU' hπ
  let vi := (↑(c l)⁻¹ : ℂ) • Jf ((l : G) * g)
  let fi := integrand hL hUi (U'.subgroupOf L) Ai l φ
  change HarmonicAnalysis.SmoothWeakIntegral.HasIntegral
    (A.representation.comp (subgroupOfContinuousEquiv hML).toMonoidHom)
    νL fi vi
  apply (HarmonicAnalysis.SmoothWeakIntegral.hasIntegral_comp_continuousMulEquiv_iff
    A.representation (subgroupOfContinuousEquiv hML) νL fi vi).mpr
  change HarmonicAnalysis.SmoothWeakIntegral.HasIntegral A.representation
    (ν.map (e : qG → qL)) fi vi
  apply (HarmonicAnalysis.SmoothWeakIntegral.hasIntegral_map_equiv_iff
    (ρ := A.representation) e.toMeasurableEquiv ν fi vi).mpr
  have heq : (fun y : qG => fi (e y)) =
      (↑(c l)⁻¹ : ℂ) • integrand h hU U' A ((l : G) * g) f := by
    funext y
    obtain ⟨x, rfl⟩ := e.symm.surjective y
    rw [Homeomorph.apply_symm_apply]
    induction x using Quotient.inductionOn with
    | h u =>
      change eval (P.subgroupOf L) (leviInflatedInducingRepresentation hL hUi Ai) φ (u.val * l) =
        (↑(c l)⁻¹ : ℂ) •
          eval P (leviInflatedInducingRepresentation h hU A) f ((u.val : G) * ((l : G) * g))
      rw [hφ, map_mul, hc u, one_mul, Subgroup.coe_mul, mul_assoc]
  rw [show (fun y : qG => fi (e.toMeasurableEquiv y)) = _ from heq]
  exact (hf ((l : G) * g)).smul _

/-- A surjective stages restriction reflects full domain for the inner
integral, including existence in the original coefficient carrier. -/
theorem nested_domain_eq_top
    (c : L →* ℂˣ)
    (hc : ∀ x : U'.subgroupOf L, c x.val = 1)
    (R : XG →ₗ[ℂ] XL) (hR : Function.Surjective R)
    (hform : ∀ f, NestedRestrictionFormula h hU hL hML A c f 1 (R f))
    (hfull : domain h hU U' A ν = ⊤) :
    domain hL hUi (U'.subgroupOf L) Ai νL = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro φ
  obtain ⟨f, rfl⟩ := hR φ
  have hf : f ∈ domain h hU U' A ν := hfull.symm ▸ Submodule.mem_top
  obtain ⟨Jf, hJf⟩ := (mem_domain h hU U' A ν f).mp hf
  exact (mem_domain hL hUi (U'.subgroupOf L) Ai νL (R f)).mpr
    ⟨_, hJf.nested_restriction h hU hL hML hQ hU'Q hNU hNU' hπ A ν c hc 1 (R f) (hform f)⟩

end Langlands.Plancherel.StandardIntertwining
