# Split-torus domination of split solvable groups

Author: Worker 755.

This module proves `IsSplitSolvableGroupScheme.hasPointedSplitTorusDomination`:
over a field `k`, every `G` with `IsSplitSolvableGroupScheme G` satisfies
the Library's `HasPointedSplitTorusDomination G` (module
[`Rational.TorusDominationBaseChange`](TorusDominationBaseChange.md)): there
are a split torus `P` over `k` and a morphism of schemes `p : P.X ⟶ G.X`
over `Spec k` that is dominant and sends the identity point of `P` to the
identity point of `G`. It is a helper for
[`SplitSolvableExtensionStructure`](SplitSolvableExtensionStructure.md),
where the domination is fed to the Library's
`splitTorusDominatedSolvableQuotient`. No definition from the literature is
introduced.

## Elementary constructions

In namespace `HasPointedSplitTorusDomination`, for group schemes over
`Spec k`:

- `isDominant_of_comp_eq_id`: a morphism `m` of schemes over `Spec k` with a
  right inverse `r` (`r ≫ m = 𝟙`) is dominant.
- `of_dominant`: a dominant `p : P.X ⟶ H.X` from a split torus `P`, not
  necessarily pointed, already gives `HasPointedSplitTorusDomination H`.
  With `c = p(1)`, compose `p` with right translation `x ↦ x c⁻¹`, which is
  dominant because right translation by `c` is a right inverse.
- `of_range_id_eq_bot`: a trivial group is dominated by the constant map
  from the rank-zero split torus `splitTorus _ PEmpty`.
- `of_iso_gm`: a group isomorphic to `G_m` is a split torus dominated by its
  identity.
- `gaExponentHom` (definition, `Fin 1 →₀ ℕ` to `PUnit → ℤ`, `d ↦ (d 0 : ℤ)`)
  and `gaExponentHom_injective`; `gaLaurentInclusion R` (definition) is the
  induced map of monoid algebras `k[t] → k[t, t⁻¹]`, from the coordinate
  algebra of the one-dimensional vector group to that of the rank-one
  diagonalizable group, and `gaLaurentInclusion_injective` says it is
  injective.
- `isSplitTorus_diagonalizable_punit`: the rank-one diagonalizable group is a
  split torus.
- `of_isVectorGroup`: a one-dimensional vector group `V` has a pointed
  split-torus domination. `Spec` of the injective inclusion
  `k[t] → k[t, t⁻¹]` is dominant
  (`SplitTorusQuotientFactor.isDominant_spec_map_of_injective`); compose
  with the isomorphism `vectorCoordinatesIso` and apply `of_dominant`.
- `of_elementary`: the two previous cases, for
  `SplitSolvable.IsElementaryQuotient V`.

`SplitSolvablePicard.smooth_of_elementary`: an elementary quotient is
smooth over `k`.

## Induction along a series

`hasPointedSplitTorusDomination_of_hasSeries`: for every `n`, every `H`
affine over `k` with `SplitSolvable.HasSeries n H` has a pointed split-torus
domination. Length zero is `of_range_id_eq_bot`. For a step with kernel
`j : N ⟶ H` and quotient `q : H ⟶ V`:

1. `N` (affine as a closed subgroup) is dominated by induction, and `V` by
   `of_elementary`; both are smooth, hence reduced
   (`SmoothReducedProof.isReduced_of_smooth_over_field`), so the Library's
   `HasPointedSplitTorusDomination.tensor` dominates `N × V`.
2. `SplitSolvablePicard.exists_section_of_hasSeries` (module
   [`SplitSolvablePicardSection`](SplitSolvablePicardSection.md)) gives a
   scheme section `σ` of `q`.
3. The multiplication morphism `m : N × V → H`, `(x, v) ↦ j(x) σ(v)`, has
   the right inverse `h ↦ (n₀(h), q(h))`, where `n₀(h)` is the point of `N`
   with `j(n₀(h)) = h σ(q(h))⁻¹` (it lies in the kernel of `q`; the Library's
   `SplitUnipotentAffineTorsor.exists_comp_eq_of_comp_eq_one`). Hence `m`
   is dominant, and `of_dominant` applied to the dominating map of `N × V`
   followed by `m` dominates `H`.

`IsSplitSolvableGroupScheme.hasPointedSplitTorusDomination` applies this to
the series and affineness contained in `IsSplitSolvableGroupScheme G`.
