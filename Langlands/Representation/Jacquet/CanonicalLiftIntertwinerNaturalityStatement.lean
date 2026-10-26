import Langlands.Representation.Jacquet.CanonicalLiftDefinitions

/-!
# Canonical Jacquet lift naturality under representation intertwiners

This internal statement concerns the existing normalized compressed actions,
their all-power stable images, and the actual unnormalized Jacquet quotient.
The inverse-lift assertion is conditional on the two quotient restrictions
being bijective.
-/

noncomputable section

namespace Langlands.Jacquet

universe uG uV uW

/-- Intertwiners preserve stable images and the actual quotient square, and
commute with inverse lifts whenever both restricted quotient maps are bijective. -/
def CanonicalLiftIntertwinerNaturalityStatement : Prop :=
  ∀ {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (hρ : IsSmooth ρ) (hσ : IsSmooth σ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (g : G) (f : ρ.IntertwiningMap σ),
    (∀ v : fixedVectors ρ K.toSubgroup,
      v ∈ stableImage ρ hρ K hK g →
      fixedVectorsMap f K.toSubgroup v ∈ stableImage σ hσ K hK g) ∧
    ∀ (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N),
      (∀ v : fixedVectors ρ K.toSubgroup,
        fixedJacquetMap σ N M hMN K.toSubgroup
            (fixedVectorsMap f K.toSubgroup v) =
          fixedVectorsMap (map N M hMN f) (K.toSubgroup.comap M.subtype)
            (fixedJacquetMap ρ N M hMN K.toSubgroup v)) ∧
      ∀ (hρbij : Function.Bijective (stableImageJacquetMap ρ hρ K hK g N M hMN))
        (hσbij : Function.Bijective (stableImageJacquetMap σ hσ K hK g N M hMN))
        (j : fixedVectors (action ρ N M hMN) (K.toSubgroup.comap M.subtype)),
        f (stableImageToRepresentation ρ hρ K hK g
            ((LinearEquiv.ofBijective (stableImageJacquetMap ρ hρ K hK g N M hMN)
              hρbij).symm j)) =
          stableImageToRepresentation σ hσ K hK g
            ((LinearEquiv.ofBijective (stableImageJacquetMap σ hσ K hK g N M hMN)
              hσbij).symm
                (fixedVectorsMap (map N M hMN f) (K.toSubgroup.comap M.subtype) j))

end Langlands.Jacquet
