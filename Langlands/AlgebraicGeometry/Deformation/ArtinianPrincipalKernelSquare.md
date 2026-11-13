# The self fibre product of a principal elementary surjection

This internal algebra module supplies the ring-level input for the lifting step
of Stacks Lemma 90.13.2. For an elementary surjection `q : A → B` of
augmented Artinian tests whose kernel is a one-dimensional `K`-vector space,
the self fibre product `A ×_B A` is also the fibre product `A ×_K K[ε]` of the
augmentation of `A` with the dual-number augmentation. It also factors every
elementary surjection with nonzero kernel through such a principal one. All
declarations are in the namespace
`Langlands.AlgebraicGeometry.Deformation.ArtinianTest.PrincipalKernel`.

Throughout, `k` is a commutative ring and `K` a field with a `k`-algebra
structure. `A`, `B` are objects of the published `ArtinianTest k K`,
`q : A ⟶ B` is a test arrow, and `Kernel q` is the published kernel ideal
`ElementaryKernel.Kernel q`, viewed as a subtype of `A`. `Pullback.algebra q q`
is the published subalgebra of pairs `(a, a')` with `q a = q a'`.

## The dual-number map

- `augArrow A`: the augmentation of `A` as a test arrow to the residue test
  (an abbreviation of the published `ArtinianChartVersality.augmentationArrow`,
  shared through `Deformation/ArtinianAugmentationArrow`).
- `augmentation_fst_eq_snd`: the two coordinates of a compatible pair have the
  same augmentation.
- `diff q x`: the difference `a' - a` of a compatible pair `x = (a, a')`, as an
  element of `Kernel q`. `diff_val` gives its value.

The remaining declarations of this part assume an additive isomorphism
`c : Kernel q ≃+ K` with `c (a • x) = ε_A(a) * c x` for `a` in `A` and `x` in the
kernel. Here `a • x` is the multiplication of the ideal by `A`, and `ε_A` is
the augmentation of `A`. So `c` identifies the kernel with `K`, as a module
through the augmentation. Such a `c` exists exactly when the kernel is a
one-dimensional `K`-vector space (`principalEquiv` below).

- `diff_mul`: `c (diff (x y)) = ε_A(a) c(diff y) + c(diff x) ε_A(b)` for
  `x = (a, a')` and `y = (b, b')`. It follows from
  `a'b' - ab = a'(b' - b) + b(a' - a)`, the semilinearity of `c`, and
  `ε_A(a') = ε_A(a)`.
- `dualMap q c hc : Pullback.algebra q q →ₐ[k] DualNumber K` sends
  `(a, a')` to `(ε_A(a), c(a' - a))`. `dualMap_fst` and `dualMap_snd` give its
  components. Multiplicativity is `diff_mul`.
- `comparison q c hc`: the ring map from `Pullback.algebra q q` to the
  published pullback algebra of `augArrow A` and the dual-number augmentation
  `dualReduction k K`, sending `x` to `(a, dualMap x)`.
- `comparison_bijective`: it is bijective. Injectivity holds because `c` is
  injective. The preimage of `(a, d)` is `(a, a + c⁻¹(d.snd))`.
- `isPullback_dual`: in commutative rings, the square formed by the first
  projection `A ×_B A → A`, `dualMap`, the augmentation `ε_A : A → K` and the
  dual-number augmentation `K[ε] → K` is a pullback square. The proof
  transports the published `Pullback.ring_isPullback` for `augArrow A` and
  `dualReduction k K` along the ring isomorphism given by `comparison`.
- `dualArrow q c hc hq`: for elementary `q`, the actual test arrow from
  `Pullback.test q q` to `dualNumbers k K` with algebra map `dualMap`.
  `toAlgHom_dualArrow` records this.

## Principal first steps

This part assumes `Fact (IsElementarySurjection q')` and uses the published
residue-field module structure `residueModule` on `Kernel q'`. It also uses
the published subspace quotients `ElementaryKernelSubspaceQuotient.projection`
and `.reduction` of a `K`-subspace `W` of the kernel.

- `projectionKernelEquiv q' W`: the kernel of `projection q' W : A ⟶ A/W` is
  `W`, additively. Its elements are the elements of the ideal
  `subspaceIdeal q' W`.
- `projectionKernelEquiv_smul`: it carries `a • x` to `ε_A(a) • x`.
- `principalEquiv q' ε₀ hε₀`: for a nonzero kernel vector `ε₀`, the kernel of
  the projection to `A/(K ε₀)` is identified with `K`. It is
  `projectionKernelEquiv` followed by the inverse of Mathlib's
  `LinearEquiv.toSpanNonzeroSingleton`. `principalEquiv_smul` gives the
  semilinearity required above.
- `finrank_reduction_add_one`: the kernel of the remaining step
  `reduction q' (K ε₀) : A/(K ε₀) ⟶ B` has dimension one less than the kernel
  of `q'`. The proof uses the published `quotientKernelEquiv` and Mathlib's
  `Submodule.finrank_quotient_add_finrank` and `finrank_span_singleton`.

## Provenance

Internal. These are the algebraic identities behind the isomorphism
`A ×_B A ≅ A ×_K K[I]` used in the proof of Stacks Project Lemma 90.13.2
(Tag 06IU), specialized to a one-dimensional kernel `I`. They also give the
standard reduction of elementary surjections to ones with one-dimensional
kernel.
