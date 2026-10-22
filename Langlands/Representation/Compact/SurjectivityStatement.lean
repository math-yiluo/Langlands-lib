import Langlands.Representation.Compact.Definitions

namespace Langlands.Compact

universe uG uV uW

/-- A surjective intertwiner of smooth complex representations induces a
surjection on compact-open fixed vectors. This is a proposition target. -/
def FixedVectorSurjectivity : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (W : Type uW) [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W),
    IsSmooth ρ → IsSmooth σ →
    ∀ (K : OpenSubgroup G), IsCompact (K : Set G) →
    ∀ f : ρ.IntertwiningMap σ, Function.Surjective f →
      Function.Surjective (fixedVectorMap ρ σ f K.toSubgroup)

end Langlands.Compact
