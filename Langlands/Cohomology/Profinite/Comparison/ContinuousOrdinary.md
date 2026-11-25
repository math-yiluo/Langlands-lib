# The two comparisons with continuous cohomology agree on cocycles

`Langlands/Cohomology/Profinite/Comparison/ContinuousOrdinary.lean`, namespace
`Langlands.ProfiniteCohomology`.

Let `G` be a locally compact topological group and `X` a topological representation of `G` over
`k` with the discrete topology whose underlying representation is smooth. Mathlib's continuous
cohomology `continuousCohomology n X` (homogeneous continuous cochains, nested continuous functions)
is compared with two other models:

- the foundations' isomorphism `isoContinuousCohomology X n` from the cochain model
  `cohomology (underlyingRep X) n` (locally constant inhomogeneous cochains): its inverse reads a
  homogeneous cochain `σ` as the inhomogeneous cochain `(g₁, …, gₙ) ↦ σ(1, g₁, g₁g₂, …, g₁⋯gₙ)`;
- the Library's comparison `Langlands.Continuous.continuousToOrdinary X n` with Mathlib's
  `groupCohomology` of the abstract group (`Langlands/Cohomology/Continuous/CochainComparison.lean`),
  which evaluates a homogeneous cochain at the same tuple of partial products
  (`continuousToOrdinaryCochains_apply`).

**Theorem** (`isoContinuousCohomology_hom_comp_continuousToOrdinary`). The foundations' comparison
followed by the Library's is the map `toGroupCohomology (underlyingRep X) n` induced by the inclusion
of locally constant cochains into all inhomogeneous cochains: on a cocycle `z` of the cochain model,
the composite is the class of `z` itself in `groupCohomology`.

For a discrete group `G` the Library's comparison is invertible
(`Continuous.continuousToOrdinary_isIso`), and its inverse is the foundations' isomorphism after
`isoGroupCohomology⁻¹` (`isoContinuousCohomology_hom_continuousToOrdinary_inv`). This is how the
Library's relative classes (Mathlib's `groupCohomology` of finite Galois groups, on which the local
invariant is computed) are read in the cochain model
(`Langlands/GaloisCohomology/Field/RelativeInflation.lean`).

## Declarations

`{k G : Type u} [CommRing k] [TopologicalSpace k] [Group G] [TopologicalSpace G]
[IsTopologicalGroup G] [LocallyCompactSpace G]`, `X : TopRep.{u} k G`, `[DiscreteTopology X]
[IsSmoothRep (underlyingRep X)]`.

```lean
theorem nestedEval_eq_nestedHomeomorph (X : TopRep.{u} k G) (m : ℕ) (a : resolutionX X m)
    (x : Fin m → G) :
    Continuous.nestedEval X m a x = nestedHomeomorph X m a x
theorem continuousToOrdinaryCochains_homogeneousEquiv (n : ℕ)
    (φ : locallyConstantCochains (underlyingRep X) n) (x : Fin n → G) :
    ((Continuous.continuousToOrdinaryCochains X).f n).hom (homogeneousEquiv X n φ) x = φ.1 x
theorem cochainsIsoHomogeneousCochains_hom_comp_continuousToOrdinaryCochains :
    (cochainsIsoHomogeneousCochains X).hom ≫ Continuous.continuousToOrdinaryCochains X =
      cochainsι (underlyingRep X)
theorem isoContinuousCohomology_hom_comp_continuousToOrdinary (n : ℕ) :
    (isoContinuousCohomology X n).hom ≫ Continuous.continuousToOrdinary X n =
      toGroupCohomology (underlyingRep X) n
theorem continuousToOrdinary_isoContinuousCohomology_hom_apply (n : ℕ)
    (x : cohomology (underlyingRep X) n) :
    (Continuous.continuousToOrdinary X n).hom ((isoContinuousCohomology X n).hom.hom x) =
      (toGroupCohomology (underlyingRep X) n).hom x
theorem isoContinuousCohomology_hom_continuousToOrdinary_inv [DiscreteTopology G] (n : ℕ)
    (y : groupCohomology (underlyingRep X) n) :
    haveI := Continuous.continuousToOrdinary_isIso X n
    (inv (Continuous.continuousToOrdinary X n)).hom y =
      (isoContinuousCohomology X n).hom.hom ((isoGroupCohomology (underlyingRep X) n).inv.hom y)
```

## Proofs

The Library's evaluation `Continuous.nestedEval` and the foundations' `nestedHomeomorph` are defined
by the same recursion on the nesting (`f ↦ f (x₀)` then the tail), so they agree pointwise. The
foundations' isomorphism sends a locally constant cochain `φ` to the invariant nested function with
values `homogeneousFun φ (x) = x₀ · φ(x₀⁻¹x₁, …, xₙ₋₁⁻¹xₙ)`; at the partial products of `g` this is
`φ(g)` (`Fin.partialProd_zero`, `Fin.partialProd_right_inv`). Hence the composite of the two cochain
maps is the inclusion `cochainsι`, and on homology the two `mapHomologyIso` factors cancel. For a
discrete group the inverse statement follows by applying the injective Library comparison.

## Source and licence

New file.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition, chapter I,
  §2: the isomorphism between homogeneous and inhomogeneous cochains,
  `x(σ₀, …, σₙ) ↦ y(σ₁, …, σₙ) = x(1, σ₁, σ₁σ₂, …, σ₁⋯σₙ)`, with inverse
  `y ↦ σ₀ y(σ₀⁻¹σ₁, …, σₙ₋₁⁻¹σₙ)`, p. 14.
