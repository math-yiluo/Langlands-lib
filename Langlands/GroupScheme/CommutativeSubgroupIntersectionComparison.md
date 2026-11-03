# Comparison with actual commutative intersection representatives

Let `f : T → P` and `r : R → P` be actual closed subgroup maps over an
arbitrary base scheme, with `T` commutative. The construction retains an
explicit monomorphism instance for `r`, as required by
`commutativeSubgroupIntersection`. Suppose a commutative group scheme `S`
has a closed map `sT : S → T` and satisfies

```text
range (sT ≫ f) = range f ∩ range r
```

on every test scheme. `commutativeSubgroupIntersectionRepresentativeIso`
is an actual group-scheme isomorphism from the canonical commutative
intersection to `S`. Its composite with `sT` is the first canonical
projection. If a supplied `sR : S → R` satisfies `sT ≫ f = sR ≫ r`, its
composite with `sR` is the second canonical projection. The inverse satisfies
both projection equations and is the canonical pullback lift of the supplied
pair. These comparisons use the entire subgroup functor, including
nonreduced and nonaffine tests.

Over a field, if `sR` is a maximal torus of `R`, then the canonical
intersection's second projection is also a maximal torus.
`isMaximalTorus_commutativeSubgroupIntersectionSnd_of_baseChange_representative`
applies the same argument after any extension of fields in the same universe
and reflects maximality to the original field. Its hypotheses retain
closedness of both original maps, closedness of the supplied extension-field
map to the base-changed `T`, maximality of the supplied map to the base-changed
`R`, the actual composite equality, and the full extension-field range
equality.

This is an internal categorical construction. The canonical intersection and
the supplied common map are monomorphic representatives of the same subgroup
functor: the latter is closed by composition of `sT` with `f`. The existing
`SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy` supplies their
isomorphism and ambient composite equation. Cancellation of the monomorphisms
`f` and `r` proves the two projection identities. The inverse identities
follow from the isomorphism laws, and the pullback universal property
identifies the inverse with the canonical lift. Maximality is transported
with `IsMaximalTorus.iso_comp`; the extension-field corollary uses the actual
intersection comparison and maximality reflection from
`CommutativeSubgroupIntersectionBaseChange`.

No radical, intersection torus, or Levi existence theorem is proved here.
The geometric hypothesis that the full intersection admits such a maximal
torus representative remains necessary. In particular, equality only on
geometric points does not satisfy the range hypothesis.
