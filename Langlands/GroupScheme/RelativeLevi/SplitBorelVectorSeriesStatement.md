# Statement: a split Borel with an affine vector-series kernel

Worker 670.

`HasSplitBorelVectorSeries t` is a proposition about a specified homomorphism
`t : 𝔾_m^I → G` over `Spec R`. It asserts the existence of group schemes `B₀`
and `K` and homomorphisms

`i₀ : B₀ → G`, `j : K → B₀`, `q : B₀ → 𝔾_m^I`, `t₀ : 𝔾_m^I → B₀`

with the following properties:

- `i₀` is a relative Borel subgroup of `G`.
- `j` is a closed subgroup and `K` is affine over `Spec R`.
- `t₀ ≫ i₀ = t` and `t₀ ≫ q = 𝟙`: the given torus factors through this Borel
  and is a section of the quotient.
- `q` is flat, surjective and locally of finite presentation, and the range of
  its actual scheme kernel equals the range of `j` on every test scheme.
  These are precisely `RelativeRoot.IsFppfQuotient (range j) q`; surjectivity
  on each original group of rational points is not required.
- For some natural number `n`, `HasAffineVectorSeries n K` holds. This is the
  published finite recursive series of closed subgroup kernels and actual
  fppf quotients that are finite-dimensional vector groups. Its zero case says
  that the identity range is the trivial subgroup functor.

`SplitBorelVectorSeriesStatement.{u}` asserts this structure for every
commutative ring `R : Type u` and every split reductive datum in
`SplitBorelZariskiLocalConjugacyStatement`: a reductive group, a finite
coordinate split torus included as a closed subgroup and maximal on every
residue fibre, a fibrewise root datum on its coordinate lattices, and root
weight spaces free of rank one over `R`. Its quantifiers and four splitting
hypotheses are identical to that target. This module defines these two
propositions and proves neither.

The structural statement is the affine specialization of the split Borel
construction in Brian Conrad, *Reductive group schemes* (2014), registered as
`conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
Page numbers below are both printed and one-based PDF page numbers.
Theorem 5.1.13, pp.143–145, constructs the closed semidirect product
`T ⋉ U` from a positive system of roots, with `U` a product of root groups as
a scheme. The proof of Corollary 5.2.13(1), pp.158–159, identifies the
corresponding dynamic parabolic as a Borel and its centralizer factor as `T`.
Projection to `T`, transported to the specified coordinate torus, gives `q`,
and the torus inclusion gives `t₀`; its kernel is `U`. Projection from this
smooth split extension is an fppf cover with the asserted actual kernel.
The root-group product makes `U` affine over the base.

Proposition 5.1.16(2), pp.147–148, filters `U` by closed subgroups indexed by
positive root heights, with successive quotients powers of `𝔾_a`.
There are finitely many roots, so the descending filtration terminates.
Reading its successive quotient maps recursively gives
`HasAffineVectorSeries n K`, including any zero-dimensional quotient.
The free root-space hypothesis supplies the root-group trivializations.
This records the grouped vector quotients directly rather than requiring a
choice of one-dimensional refinement.

The source assumes a nonempty base. The statement also includes the zero
ring: over the empty scheme all group schemes and their morphisms are
uniquely isomorphic, the relative fibre conditions are vacuous, and the
kernel has a length-zero series. No connectedness of the base or of the
kernel's total space, and no local, Noetherian or reduced condition, is
imposed. In particular, the internal series predicate deliberately avoids
the total-space connectedness required by `RelativeRoot.HasSplitSeries`.

This statement isolates a structural input to local Borel conjugacy. It
does not assert that an arbitrary Borel already contains the specified
torus and does not assert Zariski-local conjugacy. Constructing the witnesses
from the split data remains a separate proof obligation.
