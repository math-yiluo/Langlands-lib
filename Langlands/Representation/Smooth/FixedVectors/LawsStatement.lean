import Langlands.Representation.Smooth.FixedVectors.Definitions

namespace Langlands

universe uR uG uV uW uU

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW} {U : Type uU}
variable [CommRing R] [Group G]
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
variable [AddCommGroup U] [Module R U]

/-- Pointwise, naturality, functoriality, and injectivity laws for fixed-vector maps. -/
def FixedVectorsMapLawsStatement : Prop :=
  (∀ (ρ : Representation R G V) (σ : Representation R G W)
      (f : ρ.IntertwiningMap σ) (K : Subgroup G) (v : V),
      v ∈ fixedVectors ρ K → f v ∈ fixedVectors σ K) ∧
  (∀ (ρ : Representation R G V) (σ : Representation R G W)
      (f : ρ.IntertwiningMap σ) (K : Subgroup G) (v : fixedVectors ρ K),
      (fixedVectorsMap f K v : W) = f (v : V)) ∧
  (∀ (ρ : Representation R G V) (σ : Representation R G W)
      (f : ρ.IntertwiningMap σ) (K : Subgroup G),
      (fixedVectors σ K).subtype.comp (fixedVectorsMap f K) =
        f.toLinearMap.comp (fixedVectors ρ K).subtype) ∧
  (∀ (ρ : Representation R G V) (K : Subgroup G),
      fixedVectorsMap (Representation.IntertwiningMap.id ρ) K = LinearMap.id) ∧
  (∀ (ρ : Representation R G V) (σ : Representation R G W)
      (τ : Representation R G U) (g : σ.IntertwiningMap τ)
      (f : ρ.IntertwiningMap σ) (K : Subgroup G),
      fixedVectorsMap (g.comp f) K =
        (fixedVectorsMap g K).comp (fixedVectorsMap f K)) ∧
  (∀ (ρ : Representation R G V) (σ : Representation R G W)
      (f : ρ.IntertwiningMap σ),
      Function.Injective f → ∀ K : Subgroup G, Function.Injective (fixedVectorsMap f K))

/-- Evaluation and inverse compatibility for fixed-vector equivalences. -/
def FixedVectorsEquivalenceLawsStatement : Prop :=
  ∀ (ρ : Representation R G V) (σ : Representation R G W)
    (e : ρ.Equiv σ) (K : Subgroup G),
    (∀ v : fixedVectors ρ K, (fixedVectorsEquiv e K v : W) = e (v : V)) ∧
    (∀ w : fixedVectors σ K, ((fixedVectorsEquiv e K).symm w : V) = e.symm (w : W)) ∧
    (fixedVectorsEquiv e K).toLinearMap = fixedVectorsMap e.toIntertwiningMap K ∧
    (fixedVectorsEquiv e K).symm = fixedVectorsEquiv e.symm K


/-- The coherent algebraic laws for restriction to subgroup-fixed vectors. -/
def FixedVectorsLawsStatement : Prop :=
  FixedVectorsMapLawsStatement (R := R) (G := G) (V := V) (W := W) (U := U) ∧
  FixedVectorsEquivalenceLawsStatement (R := R) (G := G) (V := V) (W := W)

end Langlands
