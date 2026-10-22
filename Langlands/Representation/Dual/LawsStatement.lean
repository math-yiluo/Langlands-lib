import Langlands.Representation.Dual.Definitions

/-! # Laws of algebraic dual maps: proposition target -/

namespace Langlands

universe uR uG uV uW uU

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW} {U : Type uU}
variable [CommRing R] [Group G]
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
variable [AddCommGroup U] [Module R U]

/-- Pullback of a functional evaluates by precomposition. -/
def DualIntertwiningEvaluationStatement : Prop :=
  ∀ (ρ : Representation R G V) (σ : Representation R G W)
    (f : ρ.IntertwiningMap σ) (ℓ : Module.Dual R W) (v : V),
    dualIntertwining f ℓ v = ℓ (f v)

/-- Duality preserves the identity intertwiner. -/
def DualIntertwiningIdentityStatement : Prop :=
  ∀ ρ : Representation R G V,
    dualIntertwining (Representation.IntertwiningMap.id ρ) =
      Representation.IntertwiningMap.id ρ.dual

/-- Duality reverses composition of intertwiners. -/
def DualIntertwiningCompositionStatement : Prop :=
  ∀ (ρ : Representation R G V) (σ : Representation R G W)
    (τ : Representation R G U) (f : ρ.IntertwiningMap σ) (g : σ.IntertwiningMap τ),
    dualIntertwining (g.comp f) = (dualIntertwining f).comp (dualIntertwining g)

/-- The equivalence on duals evaluates by precomposition. -/
def DualEquivEvaluationStatement : Prop :=
  ∀ (ρ : Representation R G V) (σ : Representation R G W)
    (e : ρ.Equiv σ) (ℓ : Module.Dual R W) (v : V), dualEquiv e ℓ v = ℓ (e v)

/-- The canonical map to the algebraic bidual is evaluation. -/
def BidualIntertwiningEvaluationStatement : Prop :=
  ∀ (ρ : Representation R G V) (v : V) (ℓ : Module.Dual R V),
    bidualIntertwining ρ v ℓ = ℓ v

/-- Evaluation into the algebraic bidual is natural in intertwiners. -/
def BidualIntertwiningNaturalityStatement : Prop :=
  ∀ (ρ : Representation R G V) (σ : Representation R G W)
    (f : ρ.IntertwiningMap σ),
    (dualIntertwining (dualIntertwining f)).comp (bidualIntertwining ρ) =
      (bidualIntertwining σ).comp f

/-- Contravariance, underlying formulas, and naturality of bidual evaluation.
The six named proposition definitions above are the complete clauses. -/
def AlgebraicDualLawsStatement : Prop :=
  DualIntertwiningEvaluationStatement (R := R) (G := G) (V := V) (W := W) ∧
  DualIntertwiningIdentityStatement (R := R) (G := G) (V := V) ∧
  DualIntertwiningCompositionStatement (R := R) (G := G) (V := V) (W := W) (U := U) ∧
  DualEquivEvaluationStatement (R := R) (G := G) (V := V) (W := W) ∧
  BidualIntertwiningEvaluationStatement (R := R) (G := G) (V := V) ∧
  BidualIntertwiningNaturalityStatement (R := R) (G := G) (V := V) (W := W)

end Langlands
