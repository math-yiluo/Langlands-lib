# Same-source torus lifts through split unipotent kernels

This internal deduction applies the actual split-unipotent torus-cocycle
conjugator to the difference cocycle of two homomorphisms with equal
quotient maps. Its entry constructs an actual rational point of the
represented kernel conjugating the first map to the second. The field and
the common universe `u` are arbitrary.

Every construction and conjugacy result retains these three explicit
proposition parameters from `TorusUnipotentCocycle`:

- `RelativeRoot.SplitUnipotentStableVectorSubgroupStatement`;
- `RelativeRoot.TorusVectorActionLinearizationStatement`;
- `SplitUnipotentAffineTorsorStatement`.

They are not proved here. The split-quotient proposition is not an
additional parameter: the preceding induction uses the proved
smooth-affine surjective-image split-series theorem.

## The actual kernel point

Fix group homomorphisms `n : N → G` and `q : G → Q` with the represented
range of `n` equal to the represented range of the actual kernel
inclusion of `q`. Assume that the underlying arrow of `n` is monic and
that `N` is smooth, connected and affine over the field. Retain both
`IsUnipotent N` and `RelativeRoot.IsSplitUnipotent N`.

Let `H` be any torus over the field and let `i₀,i₁ : H → G` be any
homomorphisms with `i₀ ≫ q = i₁ ≫ q`. Neither map is assumed to be
injective, closed, smooth or maximal. In particular trivial maps and
noninjective cocharacters are included, and `H` need not be split.

`QuotientHomCocycle.splitUnipotentTorusConjugator` applies
`RelativeRoot.torusUnipotentCocycleConjugator` to the existing actual
difference cocycle
`QuotientHomCocycle.cocycle n q hn i₀ i₁ hi`, for conjugation on `N`
along `i₀`. This produces a morphism `v : Spec k → N`. The accompanying
`splitUnipotentTorusConjugator_conjugates` theorem gives the equality

```text
i₀ ≫ (G.innerIso (v ≫ n.hom.hom)).hom = i₁.
```

The proof uses the exact coboundary equation from the induction and
`QuotientHomCocycle.cocycle_eq_coboundary_iff`. The latter already identifies
the difference-cocycle convention with this direction of conjugation.
Thus the equality is one of actual group-scheme morphisms and holds
after every scheme test, including nonreduced tests.

`splitUnipotentTorusConjugator_mem_kernel` places the conjugating point
in the original represented kernel range, using the explicit range
equality. `homConjugate_of_isTorus_split_unipotent_kernel` packages the
displayed equality as `HomConjugate i₀ i₁`.
`subgroupConjugate_of_isTorus_split_unipotent_kernel` packages the same
point as `SubgroupConjugate i₀ i₁` with the identity source isomorphism.

For these core constructions, no affineness or smoothness assumption is
imposed on `G` or `Q`, and `q` need not be a quotient cover. Only its
explicit represented-kernel equality is used.

## The represented fppf-quotient interfaces

The final two theorems specialize to an affine ambient group `G`, a
closed inclusion `n : N → G` with smooth connected unipotent split
source, and a represented fppf quotient
`hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range n) q`.
Closedness supplies monicity and affineness of `N`; the last field of
`hq` supplies the required exact kernel-range equality.

The theorem
`homConjugate_of_isTorus_fppf_split_unipotent_kernel_of_structuralStatements`
then proves `HomConjugate i₀ i₁` for the same arbitrary torus maps with
equal quotient maps.
`subgroupConjugate_of_isTorus_fppf_split_unipotent_kernel_of_structuralStatements`
gives the corresponding subgroup conjugacy. These interfaces require no
smoothness or affineness hypothesis on `Q`, no smoothness or connectedness
hypothesis on `G`, and no maximality premise on either source map.

## Provenance and remaining obligations

The file is an internal composition of the actual difference-cocycle
construction, its exact conjugacy comparison, and the preceding
conditional unipotent-cocycle dimension induction. No new
literature-derived structural result is assumed or claimed.

The three proposition parameters remain proof obligations. Splitness
of the unipotent kernel is also explicit; it is not inferred from
smoothness and connectedness over an arbitrary field. The file does
not construct homomorphic torus lifts, replace a conjugacy in the
quotient by a same-source equality, or prove the host maximal-torus
conjugacy theorem.
