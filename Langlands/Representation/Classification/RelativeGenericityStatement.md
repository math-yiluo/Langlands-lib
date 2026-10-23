# Generic real parameters for nested standard GL Levis

Author: Worker 19.

`Langlands.GLRelativeGenericParameterStatement` is a derived type-A
specialization of Silberger 1978, Lemma 5.2. It states openness and density
of the generic real parameters used before the relative Jacquet multiplicity
comparison. It is a proposition definition, not a proof.

## Actual coordinates and genericity

Let `B` and `C` be positive ordered block shapes of the same positive rank
`n`. The hypothesis says that every block of `B` lies inside a block of `C`:
if two standard matrix coordinates have the same `B` block index, they have
the same `C` block index. Thus `B` describes the fine Levi `M` and `C` the
coarse Levi `M''`. This is an actual condition on their standard coordinate
partitions, not a supplied group, root datum, or classification result.

A vector `v₀ : Fin B.length → ℝ` gives the fine determinant exponents.
A parameter `t : Fin C.length → ℝ` gives the coarse determinant exponents.
Both become vectors on the full diagonal torus by repeating the relevant
entry at each coordinate in its block. Write their difference as

```
x_t(a) = v₀(blockIndex B a) - t(blockIndex C a).
```

`IsRelativeGenericParameter B C v₀ t` is the conjunction of these two
explicit conditions:

1. `t` is injective. Its entries on distinct coarse blocks are distinct,
   so it is regular for the relative roots of GL_n.
2. Every permutation `w` of `Fin n` preserving the fine block equivalence
   relation in both directions and satisfying `x_t(w a) = x_t(a)` for
   every coordinate `a` belongs to the published subgroup `blockWeyl C`.
   Membership in that subgroup means that `w` preserves each coarse block.

The partition condition on `w` allows exchange of whole fine blocks of
the same size and arbitrary permutations within them. These are the lifts
to the full symmetric group of `W(G/A)`. The within-fine-block permutations
act trivially on both repeated exponent vectors, since the fine partition
refines the coarse one. Quotienting by them therefore gives precisely the
relative action. Among these lifts, membership in `blockWeyl C` says that
the relative Weyl element is in `W(M''/A)`. The Lean predicate uses actual
permutations and block indices directly; it does not assume a Weyl-group
identification theorem or introduce an abstract Weyl action.

The statement quantifies every such pair of block shapes and every `v₀`.
It asserts that the displayed generic set is both open and dense in
`Fin C.length → ℝ`, equipped with its usual finite product topology.
Openness is in the entire parameter space, not merely in the regular
locus. Positive rank is explicit. A single coarse block has no regularity
walls; every permutation belongs to its block Weyl group, so its generic
set is the entire parameter space.

## Original source and derivation

The original is Allan J. Silberger, *The Langlands quotient theorem for
p-adic groups*, Math. Ann. 236 (1978), 95–104: section 1, pp.95–96, for
real exponent spaces and Weyl groups; the setup following Proposition 5.1
and Lemma 5.2 with its proof, pp.99–100. Literature ID
`provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`;
retained PDF SHA-256
`4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`.
PDF page 1 is printed p.95. The full article was read previously; the
setup and proof on pp.99–100 were reread for this contribution, and p.99
was also inspected in its page image. No source errata file is present in
the current Library.

Silberger calls a regular `ν''` generic when `ν₀ - ν''` is fixed by no
member of `W(G/A)` outside `W(M''/A)`, and proves that these parameters
form an open dense set. The repeated-coordinate model above is the GL_n
specialization of this definition. Determinant exponents are used here;
block-scalar exponents would multiply the fine entry by its block size.
On the full diagonal torus the Weyl action is ordinary permutation of
coordinates. Using `w` rather than its inverse in the fixed-vector equation
does not change a stabilizer.

Here is the finite-dimensional derivation of the asserted generalization.
If `w` does not preserve every coarse block, choose a coordinate `a` with
`blockIndex C (w a) ≠ blockIndex C a`. The fixed-vector equation at `a`
imposes

```
t(blockIndex C (w a)) - t(blockIndex C a)
  = v₀(blockIndex B (w a)) - v₀(blockIndex B a).
```

This is a proper affine hyperplane in the coarse parameter space, because
the two coarse indices differ. The full fixed set of `w` is closed and
contained in that hyperplane. There are only finitely many permutations.
Regularity excludes finitely many additional proper hyperplanes
`t(i) = t(j)` with `i ≠ j`. Consequently the complement of the generic
set is a finite union of closed sets with empty interior, and the generic
set is open and dense. This supplies a mathematical derivation, not an
implemented Lean proof.

The article fixes `ν₀` through a preceding cuspidal/discrete-series setup.
For this elementary lemma the same hyperplane argument works for every
real `v₀`, so the Lean statement deliberately generalizes that parameter.
It does not generalize the hypotheses of Lemmas 5.3 or 5.6. The common
central direction is unrestricted: adding a constant to all coarse
coordinates shifts `x_t` by a constant and changes none of its stabilizers.
No field or representation carrier occurs in this finite combinatorial
statement.

## Normalization and remaining obligations

Genericity is distinct from positivity. For an upper block parabolic the
regular positive chamber has strictly decreasing determinant exponents.
Injectivity here allows every regular chamber, as in Lemma 5.2, and is
not a replacement for strict decrease in the quotient theorem. Likewise,
genericity must not replace the all-regular-positive conclusion of Lemma
5.6. Silberger's positive twist at parameter `-i ν''` corresponds to
positive absolute-determinant powers. The present predicate only tests
the stabilizer of `ν₀ - ν''`; negating the whole vector leaves that
stabilizer unchanged. It constructs no induction or Jacquet functor and
changes no normalization convention.

The open-dense claim still needs a Lean proof. The representation-level
multiplicity equalities, opposite-Jacquet comparisons, recovery of inducing
data and cosocle counts remain separate statement and proof obligations.
No quotient existence, temperedness, multiplicity or classification
conclusion is assumed or asserted in this pair.
