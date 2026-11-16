# Geometric kernels of supplied coroot quotients

This internal construction normalizes the actual coroot quotient under base
change and proves semisimplicity of its full kernels over all field-valued
points of any supplied affine pinned model. Everything is uniform in the
universe `u`. The coefficient ring is arbitrary.

For an `AffinePinnedModel M`, suppose
`q : M.group ⟶ (corootQuotient (CommRingCat.of M.ring) M.rootDatum).toGrp`
is supplied and satisfies
`M.inclusion ≫ q = corootProjection (CommRingCat.of M.ring) M.rootDatum`.
The main conclusions are:

- `isSemisimple_corootQuotientBaseChangeKernel`: for every field algebra
  `k` over `M.ring`, the full kernel of the normalized pulled-back map is
  semisimple.
- `isSemisimple_corootQuotientKernel_fieldPoint`: for every field `k` and
  actual morphism `b : Spec k ⟶ M.base`, the actual pullback
  `(baseChange b).obj (kernel q)` is semisimple.
- `isSemisimple_corootQuotient_geometricKernel`: at every point `s` of
  `M.base`, the full kernel of
  `(baseChange (geometricPoint M.base s)).map q` is semisimple.

The finite coordinate and root types, reductivity, fibrewise maximality and
full fibrewise root datum come from `M`. A decidable equality on the finite
coordinate type is used to express the explicit projection and can always be
chosen classically. No condition on the characteristic, nonemptiness or
reducedness of the coefficient ring is imposed. No smoothness or surjectivity
premise for `q` is used.

For any `b : Spec R' ⟶ Spec R` and finite coordinate root datum `P`,
`corootProjection_baseChange_square` proves that the base change of the
actual coroot projection commutes with the canonical split-torus and
diagonalizable comparison isomorphisms. The proof evaluates both sides on
every test scheme and every character of `cocenterLattice P`. The published
point formulas for the projection and both comparisons reduce the equality
to naturality of the actual group-scheme base-change point equivalence.
`corootProjection_baseChange` rewrites this square with normalized source.

`corootQuotientBaseChangeHom b P q` is the base change of `q` followed by
`Diagonalizable.baseChangeIso b (cocenterLattice P)`. The restriction lemma
shows that its composite with the normalized coordinate torus inclusion is
exactly `corootProjection R' P`. The definition
`corootQuotientKernelBaseChangeIso` constructs the actual group-scheme
isomorphism

```text
(baseChange b).obj (kernel q)
  ≅ kernel (corootQuotientBaseChangeHom b P q).
```

It composes the published kernel/base-change isomorphism with the kernel
comparison of the commutative square whose source comparison is the identity
and whose target comparison is the canonical diagonalizable isomorphism.
Both sides are entire scheme kernels, retaining all infinitesimal points.

Over a field algebra, reductivity of `M` gives connected reductivity of its
actual pullback. Fibrewise maximality gives maximality of the normalized
coordinate torus, and its closed inclusion provides the required
monomorphism. The model's full fibrewise root datum specializes to the exact
field realization of `M.rootDatum`. The normalized restriction identity then
allows `isSemisimple_kernel_of_corootProjection` from `CorootQuotientKernel`
to apply. That field theorem identifies the full kernel with the actual
derived subgroup before using field semisimplicity.

For an arbitrary field-valued point `b`, `Spec.preimage b` supplies the
original coefficient-algebra structure on the field. `Spec.map_preimage`
identifies its algebra base map with `b`. The kernel comparison transports
the preceding semisimplicity result to the actual fibre of `kernel q`.
At a geometric point, the inverse kernel/base-change isomorphism transports
this to the full kernel of the geometric-fibre homomorphism.

The provenance is internal: this unit combines the field coroot-kernel
criterion, the model's actual fibrewise interfaces, canonical split-torus
and diagonalizable base-change comparisons, kernel-square transport and
semisimplicity invariance. It does not construct `q`, prove its relative
smoothness or surjectivity, or discharge relative semisimple perfectness.
The unconditional relative derived-group existence target remains a
separate assembly obligation.
