# Factoring actual homogeneous quotients through group quotients

Author: Worker 1478.

This internal construction works over an arbitrary base scheme `S : Scheme.{u}`.
Let `f : G ⟶ H` be an actual group-scheme homomorphism, let `F` be a subgroup
functor of `G`, and let `q : G.X ⟶ Q` be an actual relative morphism whose
fibers satisfy, on every relative scheme test `T`,

```lean
a ≫ q = b ≫ q ↔ a⁻¹ * b ∈ F.carrier T
```

Assume the image of the full scheme-theoretic kernel inclusion `kernelι f`
lies in `F`. If two points have the same image under `f`, their difference
`a⁻¹ * b` is killed by `f`, hence lies in the full kernel and then in `F`.
`comp_eq_of_groupQuotient_eq` therefore proves that they have the same image
under `q`. If `f.hom.hom.left` is an effective epimorphism, `desc` applies the
existing relative effective-epimorphism descent construction to produce an
actual `H.X ⟶ Q`. `fac_desc` gives the equation `f.hom.hom ≫ desc = q`;
`desc_unique` proves uniqueness among relative maps satisfying that equation.

For any supplied homomorphism `j : K ⟶ H`, the equality
`F = (SubgroupFunctor.range j).comap f` implies the kernel containment above:
a point killed by `f` maps to the identity, which belongs to the range of `j`.
This is `kernel_le_of_comap` and requires no monomorphism assumption on `j`.

Now assume the underlying map of `f` is quasi-compact, flat and surjective,
and the relative map underlying `j` is a monomorphism. Suppose again that
`F` is exactly the full preimage of the range of `j`. For any actual relative
map `r : H.X ⟶ Q` with `f.hom.hom ≫ r = q`,
`fibers_of_factorization` proves the exact equivalence

```lean
a ≫ r = b ≫ r ↔ a⁻¹ * b ∈ (SubgroupFunctor.range j).carrier T
```

for every relative scheme `T` and every pair `a b : T ⟶ H.X`.
The proof pulls back `f` twice to obtain a single fpqc cover `v : V ⟶ T`
on which both points lift. The equation for `q` and the full preimage
hypothesis give the desired equivalence over `V`. Equality descends because
`v` is an epimorphism. Membership in the range of `j` descends using the
existing represented-subgroup descent theorem, whose monomorphism hypothesis
is supplied explicitly. Restriction of subgroup membership gives the other
direction. `desc_fibers` specializes this result to the canonical `desc`.
The tests remain arbitrary, including nonaffine and nonreduced schemes.
The argument does not assume that `f` lifts either point on the original test.

The provenance is internal: the scheme kernel and its point equivalence,
relative effective-epimorphism descent, fpqc pullbacks and composition,
represented-subgroup descent, and naturality of multiplication and inverse.
This unit supplies a factorization and all-test fiber argument for a possible
split-radical reduction. It does not construct a split-radical quotient or
its subgroup image, prove that an image is pseudo-parabolic, or assert
smoothness of the descended projection. It proves no unconditional local
sections or rational-lifting theorem.
