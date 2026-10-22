import Langlands.Representation.Smooth.SmoothPart.HomDefinitions

/-! # Evaluation and naturality of smooth-part linear factorization -/

namespace Langlands

universe uR uG uV uW uU

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW} {U : Type uU}
variable [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
variable [AddCommGroup U] [Module R U]

/-- Lifting preserves the value in the original target module. -/
def SmoothHomEvaluationStatement : Prop :=
  ∀ (ρ : Representation R G V) (σ : Representation R G W) (hρ : IsSmooth ρ)
    (f : ρ.IntertwiningMap σ) (v : V),
    (smoothHomEquiv hρ σ f v : W) = f v

/-- The inverse is the pointwise inclusion of the smooth part. -/
def SmoothHomInverseEvaluationStatement : Prop :=
  ∀ (ρ : Representation R G V) (σ : Representation R G W) (hρ : IsSmooth ρ)
    (f : ρ.IntertwiningMap (smoothPart σ)) (v : V),
    (smoothHomEquiv hρ σ).symm f v = (f v : W)

/-- Lifting commutes with postcomposition after restricting the target map. -/
def SmoothHomPostcompositionStatement : Prop :=
  ∀ (ρ : Representation R G V) (σ : Representation R G W)
    (τ : Representation R G U) (hρ : IsSmooth ρ)
    (f : ρ.IntertwiningMap σ) (g : σ.IntertwiningMap τ),
    smoothHomEquiv hρ τ (g.comp f) =
      (smoothMap g).comp (smoothHomEquiv hρ σ f)

/-- Lifting commutes with precomposition between smooth source representations. -/
def SmoothHomPrecompositionStatement : Prop :=
  ∀ (ρ : Representation R G V) (σ : Representation R G W)
    (τ : Representation R G U) (hρ : IsSmooth ρ) (hτ : IsSmooth τ)
    (f : ρ.IntertwiningMap σ) (g : τ.IntertwiningMap ρ),
    smoothHomEquiv hτ σ (f.comp g) = (smoothHomEquiv hρ σ f).comp g

omit [IsTopologicalGroup G] in
/-- All four smooth-part linear factorization laws, including the required
topological-group hypothesis inside the proposition. -/
def SmoothHomLawsStatement : Prop :=
  ∀ [IsTopologicalGroup G],
    SmoothHomEvaluationStatement (R := R) (G := G) (V := V) (W := W) ∧
    SmoothHomInverseEvaluationStatement (R := R) (G := G) (V := V) (W := W) ∧
    SmoothHomPostcompositionStatement (R := R) (G := G) (V := V) (W := W) (U := U) ∧
    SmoothHomPrecompositionStatement (R := R) (G := G) (V := V) (W := W) (U := U)

end Langlands
