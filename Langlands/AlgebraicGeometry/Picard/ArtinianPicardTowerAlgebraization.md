# Algebraization and the original residue bundle of the Picard source tower

The definition
`PicardGroupoid.ArtinianPicardTowerAlgebraization.effectiveBundle`
chooses an actual line bundle on the original relative space over the
unchanged limiting quotient ring. `effectiveComparison` compares its entire
formal restriction system with `ArtinianPicardTowerFormalSystem.system`,
respecting every specified adjacent transition. `effectiveResidueIso`
identifies its actual closed-point fibre with the original residue bundle.

The inputs are a commutative base ring `k`, a field `K` with `Algebra k K`,
a commutative Noetherian local `k`-algebra `R` complete for its maximal ideal,
a surjective `k`-algebra map `ε : R →ₐ[k] K`, a proper flat morphism
`f : X ⟶ Spec k`, an actual bundle `M` on the relative `K`-fibre, and an
initial `ArtinianPicardSourceStep.Stage ε f M`. All types use the same
arbitrary universe `u`. No finite-type assumption is needed here.
The construction preserves the limiting quotient ring, augmentation and
scalar map of the supplied tower.

The residue identification uses the specified residue isomorphism of a chosen
tower stage. Pulling the stage bundle first to its adic test and then to the
residue field gives the same relative scheme map as the stage augmentation.
The two projections of the relevant pullback prove this equality.
Line-bundle pullback composition then gives the actual residue isomorphism.
No residue compatibility of the independently chosen tower transition
isomorphisms is required for this comparison.

Properness is preserved by base change to the unchanged limiting ring.
Its published completeness and Noetherian local instances allow the published
`properFormalLineBundleEffectivity` theorem to algebraize the formal system.
The existing actual evaluation comparison transports the formal residue
identification to the effective bundle. The closed point is the spectrum of
the original limiting augmentation.

The provenance is internal assembly of the published tower, formal evaluation
and proper effectivity results. Existence of the supplied source and the full
formally versal point-fibre lifting predicate remain separate obligations;
this construction by itself does not prove `FiniteTypeFormalVersalBundleStatement`.
