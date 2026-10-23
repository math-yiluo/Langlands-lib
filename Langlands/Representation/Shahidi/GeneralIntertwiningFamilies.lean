import Langlands.Representation.Shahidi.IntertwiningInduced
import Langlands.Group.GL.IntegralSubgroup
import Mathlib.Topology.Algebra.Valued.LocallyCompact

/-!
# General-field families for Shahidi's intertwining integral

The flat-family predicate and scalar coefficient use the actual general-field
induced spaces. The operator reading is proved on its existing convergence
domain under the published operator's explicit hypotheses.
-/

noncomputable section

namespace Langlands.Shahidi

open GeneralLinear MeasureTheory HarmonicAnalysis SmoothWeakIntegral

universe uF uV

variable (F : Type uF) [Field F] [ValuativeRel F]

/-- The integral matrix subgroup `GL_r(O_F)`, using the specified valuation. -/
abbrev generalMaximalCompact (r : ℕ) : Subgroup (GeneralLinear r F) :=
  GeneralLinearGroup.integralSubgroup (Fin r) (ValuativeRel.valuation F).integer

variable {F} [TopologicalSpace F] [IsTopologicalRing F]
variable (abv : AbsoluteValue F ℝ) (hopen : IsOpenNormOne abv)
variable {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
variable {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
variable (π₁ : Representation ℂ (GeneralLinear m F) V₁)
  (π₂ : Representation ℂ (GeneralLinear n F) V₂)

/-- A family in the actual inductions is flat when its values on `GL_{m+n}(O_F)`
are independent of the complex parameter. -/
def IsGeneralFlatFamily (f : ∀ s : ℂ, SourceSpace abv hopen hm hn s π₁ π₂) : Prop :=
  ∀ (s t : ℂ) (k : GeneralLinear (m + n) F), k ∈ generalMaximalCompact F (m + n) →
    sourceEval abv hopen hm hn s π₁ π₂ (f s) k =
      sourceEval abv hopen hm hn t π₁ π₂ (f t) k

variable [MeasurableSpace F]

/-- The scalar integral of (0.1) tested by a smooth functional of the factor
tensor representation. Its operator interpretation requires convergence. -/
def generalIntertwiningCoefficient (μ : Measure (Matrix (Fin n) (Fin m) F))
    (f : ∀ s : ℂ, SourceSpace abv hopen hm hn s π₁ π₂)
    (g : GeneralLinear (m + n) F)
    (ℓ : SmoothDual (pairRepresentation hm hn π₁ π₂)) (s : ℂ) : ℂ :=
  ∫ a, ℓ.val (sourceEval abv hopen hm hn s π₁ π₂ (f s)
    (blockWeyl m n F * intertwiningUnipotent m n F a * g)) ∂μ

variable [MeasurableAdd₂ F] [MeasurableMul F]
  {μ : Measure (Matrix (Fin n) (Fin m) F)} [μ.IsAddLeftInvariant]
  (hcofinal : CompactOpenCofinal ((twoBlocks m n hm hn).Levi F))
  (hμ : IsModulusScaling hm hn abv μ) {π₁ π₂}

omit [ValuativeRel F] in
/-- On the convergence domain, the scalar coefficient is the smooth-dual
pairing with the actual target value, carried back by the tensor flip. -/
theorem generalIntertwiningCoefficient_eq
    (hπ₁ : IsSmooth π₁) (hπ₂ : IsSmooth π₂)
    (f : ∀ s : ℂ, SourceSpace abv hopen hm hn s π₁ π₂)
    (g : GeneralLinear (m + n) F) (ℓ : SmoothDual (pairRepresentation hm hn π₁ π₂))
    (s : ℂ) (hs : f s ∈ sourceDomain abv hopen hm hn s π₁ π₂ μ) :
    generalIntertwiningCoefficient abv hopen hm hn π₁ π₂ μ f g ℓ s =
      ℓ.val (pairFlip.symm (targetEval abv hopen hm hn s π₁ π₂
        (intertwiningInduced abv hopen hm hn s hcofinal hπ₁ hπ₂ hμ ⟨f s, hs⟩) g)) :=
  (intertwiningInduced_eval abv hopen hm hn s hcofinal hπ₁ hπ₂ hμ ⟨f s, hs⟩ g ℓ).symm

end Langlands.Shahidi
