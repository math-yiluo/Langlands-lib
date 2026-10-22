import Langlands.Representation.Smooth.SmoothPart.Definitions

/-! # Smooth-part maps and the smooth equivalence: proposition target -/

namespace Langlands

universe uR uG uV uW uU

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW} {U : Type uU}
variable [CommRing R] [Group G] [TopologicalSpace G]
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
variable [AddCommGroup U] [Module R U]

/-- Restriction to smooth vectors is compatible with inclusion, identities,
and composition; the equivalence for an already smooth action is the inclusion. -/
def SmoothPartFunctorialityStatement : Prop :=
  ∀ [IsTopologicalGroup G],
    (∀ (ρ : Representation R G V) (σ : Representation R G W)
      (f : ρ.IntertwiningMap σ),
      (smoothInclusion σ).comp (smoothMap f) = f.comp (smoothInclusion ρ)) ∧
    (∀ ρ : Representation R G V,
      smoothMap (Representation.IntertwiningMap.id ρ) =
        Representation.IntertwiningMap.id (smoothPart ρ)) ∧
    (∀ (ρ : Representation R G V) (σ : Representation R G W)
      (τ : Representation R G U) (f : ρ.IntertwiningMap σ) (g : σ.IntertwiningMap τ),
      smoothMap (g.comp f) = (smoothMap g).comp (smoothMap f)) ∧
    (∀ (ρ : Representation R G V) (hρ : IsSmooth ρ) (v : smoothVectors ρ),
      smoothEquiv hρ v = (v : V))

end Langlands
