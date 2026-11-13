# Minimality of the successor of a Picard source stage

This internal module proves the universal property of the published successor
`ArtinianPicardSourceStep.Stage.next`: the successor test is the largest
quotient ring of the canonical elementary source extension over which the old
pointed family lifts, that is, the quotient by the least admissible equation
ideal. Every surjective test arrow `τ` from the source extension to a test
`C'` over which the old family lifts factors as a test arrow from the
successor test to `C'`. All declarations are in the namespace
`Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianPicardSourceMinimality`.

## Inverse test arrows

For a commutative ring `k` and a field `K` with a `k`-algebra structure, let
`q : A ⟶ B` be an arrow of the published augmented Artinian tests
`ArtinianTest k K` whose algebra map is bijective.

- `invOfBijective q hq : B ⟶ A` is the test arrow of the inverse algebra
  isomorphism. It respects augmentations because `q` does.
- `invOfBijective_comp` and `comp_invOfBijective`: it is a two-sided inverse
  of `q`.
- `pointedMap_comp`: for test arrows `a ≫ b = c`, the published pointed
  spectrum maps satisfy `pointedMap b ≫ pointedMap a = pointedMap c`.

## Setting

Let `R` be a Noetherian local `k`-algebra with a surjective augmentation
`ε : R → K`, let `f : X ⟶ Spec k` be flat and proper, let `M` be an actual line
bundle on the base change of `X` to the residue point, and let `s` be a
published `Stage ε f M`: an actual test `s.test` with a surjective
presentation `s.cover : R → s.test` and an actual pointed family `s.family`.
The published canonical source extension `s.sourceTest` is the quotient of `R`
by `m · ker s.cover`. Its projection from `R` is `s.sourceProjection`, and its
elementary reduction to `s.test` is `s.sourceReduction`.

The module uses the elementary and residue-module instances on the kernel of
`s.sourceReduction` that `ArtinianPicardSourceStep` itself uses. Statements here
then agree syntactically with `Stage.quotient_lift_iff`. With independently
constructed instances the comparison is defeq but too expensive for the
kernel.

Fix a test `C'`, a test arrow `τ : s.sourceTest ⟶ C'` and `ρ : C' ⟶ s.test`
with `τ ≫ ρ = s.sourceReduction`.

## The kernel quotient of `τ`

- `toAlgHom_sourceReduction_eq_zero`: an element killed by `τ` is killed by
  `s.sourceReduction`.
- `kernelSubspace τ`: the `K`-subspace of the kernel of `s.sourceReduction`
  consisting of the elements killed by `τ`. It is closed under the residue
  action because that action is multiplication by any lift of the scalar
  (published `augmentation_smul`).
- `subspaceIdeal_kernelSubspace`: the published ideal `subspaceIdeal` of this
  subspace is the kernel of the algebra map of `τ`.
- `kernelLift : ElementaryKernelSubspaceQuotient.test _ (kernelSubspace τ) ⟶ C'`
  is the arrow induced by `τ` on the published subspace quotient test (the
  published `quotientLift`).
- `kernelLift_bijective`: its algebra map is bijective when `τ` is surjective
  (published `quotientLift_injective` and `quotientLift_surjective`).
- `projection_kernelLift`: the subspace projection followed by `kernelLift` is
  `τ`.
- `kernelLift_comp`: `kernelLift ≫ ρ` is the published subspace reduction
  `ElementaryKernelSubspaceQuotient.reduction`.

## Minimality

- `exists_next_factor`: if the published obstruction subspace
  `s.obstructionSubspace` lies in `kernelSubspace τ`, there is a test arrow
  `ψ : (s.next).test ⟶ C'` with `ψ ∘ (s.next).cover = τ ∘ s.sourceProjection`
  and `ψ ≫ ρ = s.reduction`. The successor test is the subspace quotient by the
  obstruction subspace. The inclusion of subspaces gives an inclusion of their
  ideals, hence the published `quotientFactor`, and `ψ` is that factor followed
  by `kernelLift`.
- `exists_kernelQuotient_lift`: if `τ` is surjective and some actual pointed
  family `Z` over `C'` restricts along `ρ` to `s.family`, then some pointed family
  over the kernel quotient test restricts along the subspace reduction to
  `s.family`. Namely, restrict `Z` along the inverse of `kernelLift`. The
  composite of this inverse with the subspace reduction is `ρ` by
  `kernelLift_comp`, and `PseudofunctorPointedTransport.exists_restrict_of_comp`
  combines the two restrictions.
- `exists_next_factor_of_extension`: under the same hypotheses, `τ` factors
  through the successor test as in `exists_next_factor`. By
  `exists_kernelQuotient_lift` and the published `Stage.quotient_lift_iff`, the
  obstruction subspace lies in `kernelSubspace τ`.

## Provenance

Internal. This is the minimality of the hull construction in the proof of
Stacks Project Lemma 90.13.4 (Tag 06IW, Chapter 90 Formal Deformation Theory):
the next quotient of the source is the largest quotient ring over which the
family lifts, the quotient by the smallest admissible ideal (compare Stacks
Lemma 90.13.3, Tag 06SZ). Thus every admissible surjection `τ` from the source
extension to `C'` factors from `(s.next).test` to `C'`. Here minimality of the
ideal is expressed through the published obstruction criterion
`Stage.quotient_lift_iff`, not through an infimum of ideals.
