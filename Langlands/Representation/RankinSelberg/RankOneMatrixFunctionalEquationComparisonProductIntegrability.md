# Compact support and product integrability for unipotent averaging

This internal helper proves genuine product integrability for a group
Schwartz–Bruhat test at `u*g` times an arbitrary ambient matrix
Schwartz–Bruhat test at `g`, with continuous scalar weights. It also restricts
an ambient test supported on invertible matrices to a group test and proves
the corresponding canonical p-adic Haar integral exchange.

All declarations are in
`Langlands.RankinSelberg.CompactWhittakerSynthesis`.

## Compactness over a topological field

The general section uses a Hausdorff topological division field `K` and an
arbitrary matrix size `r`, including zero.

`isCompact_matrixDetRestriction` starts with compact subsets `S` of `GL_r(K)`
and `T` of the full matrix space. It proves compactness of the actual group
set consisting of `g` whose underlying matrix belongs to `T` and whose
determinant belongs to the determinant image of `S`. That image is compact
and avoids zero. Thus `T` intersected with its determinant preimage is a
compact set of invertible matrices. The published embedding
`isEmbedding_generalLinear_val` lifts it to a compact group set.

`hasCompactSupport_group_matrix_product` takes a closed subgroup `H` of
`GL_r(K)` whose elements have determinant one, a group test `φ`, and an
arbitrary full-matrix test `Φ`. It proves compact support of
`(u,g) ↦ φ(u*g) * Φ(g.val)` on `H × GL_r(K)`. On its nonzero locus, `u*g`
lies in the support of `φ`, so the determinant of `g` belongs to the compact
determinant image used above. This bounds `g` in a compact group set.
The identity `u = (u*g)*g⁻¹` then bounds `u` in a compact ambient group set.
Closedness of `H` lifts this bound to a compact subset of `H`; the product
of the two compact bounds contains the integrand's support.

`integrable_weighted_group_matrix_product` assumes second countability of
`GL_r(K)` and the Borel measurable spaces of `H` and `GL_r(K)`. For any
supplied measures `μH` and `μG` finite on compact sets, with `μG` s-finite,
and continuous weights `a : H → ℂ`, `b : GL_r(K) → ℂ`, it proves genuine
Bochner integrability of
`(u,g) ↦ a(u) * φ(u*g) * Φ(g.val) * b(g)` for `μH.prod μG`.
Multiplying by the weights preserves compact support. The integrand is
continuous, so the compact-support integration theorem applies to the
product measure. No Haar assumption is needed for this general result.

`matrixTestOnGroup` restricts a full-matrix test to the actual group,
assuming its ambient topological support lies in the range of `Units.val`.
The same embedding proves compactness of the support preimage; continuity
of `Units.val` preserves local constancy. `matrixTestOnGroup_apply` records
that the value is exactly `Φ(g.val)`.

## Canonical p-adic specialization

For every prime and canonical `F : PadicField`, the final section installs
the canonical field topology, valuative relation, local-field and Hausdorff
instances. It uses the published canonical GL second countability and local
compactness, and the closed upper-unipotent subgroup's second countability
and local compactness. Both measurable spaces are the actual Borel spaces.
These instances supply the needed finiteness on compact sets and
sigma-finiteness of the fixed Haar measures.

`integrable_unipotent_group_matrix_product` proves, for every supplied
unitary additive character `ψ`, every `n : ℕ`, group test `φ`, full-matrix
test `Φ`, and `s : ℂ`, integrability of

```text
(u,g) ↦ standardCharacter(ψ,n,u)⁻¹ * φ(u*g) * Φ(g.val)
          * determinantWeight(abv,g,s)
```

against the unchanged product
`(unipotentHaar F.Carrier n).prod (generalLinearHaar F.Carrier n)`.
Here `abv` is the normalized absolute value from the canonical data. The
inverse character and determinant weight are continuous, and upper-unipotent
elements have determinant one.

`integrable_unipotent_matrix_product` replaces `φ(u*g)` by
`Φ₁((u*g).val)` for a full-matrix first test `Φ₁` whose ambient topological
support lies entirely in the invertible locus. It applies the preceding
theorem to `matrixTestOnGroup Φ₁`. The second test `Φ` still has no such
restriction.

`integral_unipotent_matrix_swap` applies Fubini to this genuine product
integrability and exchanges the iterated `u` and `g` integrals of precisely
the same weighted function, with the same two Haar measures and no scalar
factor.

These specializations include `n = 0`. They impose no nontriviality or
conductor normalization on `ψ`, no restriction on `s`, and no additive Haar
measure or self-duality assumption.

## Provenance and scope

This is an internal derivation from the published underlying-matrix
embedding, canonical p-adic group topology and countability certificates,
upper-unipotent determinant identity, continuous standard character and
determinant weight, together with Mathlib compactness, compact-support
integrability and Fubini. No original-literature assertion is introduced.
It supplies a product-integrability prerequisite for the host task; no
Fourier comparison, matrix functional equation, or gamma equation is
assumed or proved here.
