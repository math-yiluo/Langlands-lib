# A separating line bundle over an algebraically closed field

`Langlands.GroupScheme.algebraicallyClosedSeparatingLineBundle` proves the entire
published proposition
`Langlands.GroupScheme.AlgebraicallyClosedSeparatingLineBundleStatement.{u}`.
For every field `K : Type u` with `IsAlgClosed K` and every actual commutative
group object `G` over `Spec K`, smoothness, properness and geometric connectedness
give an actual line bundle `L` on `G.X.left` satisfying the unchanged predicate
`Langlands.AlgebraicGeometry.Picard.SeparatesPointsAndTangents G.X.hom L`.
Thus its complete linear system is base-point free on rational points, separates
distinct rational points, and separates every nonzero dual-number tangent vector
at every rational point.

## Implemented proof

The entry theorem applies
`SeparatingLineBundle.algebraicallyClosedSeparatingLineBundle_of_square` to the
published exact theorem `Langlands.GroupScheme.fieldTheoremOfTheSquare`.
There is no square or seed premise in its type.

The supporting module `SeparatingLineBundle.Assembly` obtains a finite section
seed at the unit from the published theorem
`Langlands.GroupScheme.algebraicallyClosedSectionSeedExistence`.
Write its line bundles and sections as `L i` and `s i`, indexed by `Fin n`.
Every section vanishes at the unit; each is nonzero somewhere; together they
detect all other rational points and all nonzero tangent vectors at the unit.
The resulting line bundle is

```text
famBundle n (fun i ↦ (L i ⊗ L i) ⊗ L i).
```

For each `i` and rational points `a, b`, apply the square theorem twice.
With `c = (a * b)⁻¹`, this identifies the tensor product of the three translated
line bundles with `(L i ⊗ L i) ⊗ L i`.
Transport the tensor product of their pulled-back sections through this
isomorphism, and take the finite tensor product over `i`.
The helper module `SeparatingLineBundle.TensorFamily` constructs those finite
products and proves their vanishing and nonvanishing rules.

The assembly proves each clause of `SeparatesPointsAndTangents`.

- For base-point freeness at `d`, choose each pair `a, b` so that `s i` is
  nonzero at `a*d`, `b*d` and `(a*b)⁻¹*d`. Such pairs exist by irreducibility
  and the published rational-point density result. Their product section is
  nonzero at `d`.
- For distinct points `x, y`, some seed section is nonzero at `x⁻¹*y`.
  In that factor choose `a = x⁻¹`; choose the other parameters so that no factor
  vanishes at `y`. The product section vanishes at `x` and is nonzero at `y`.
- For a nonzero tangent vector at `x`, translation by `x⁻¹` gives a nonzero
  tangent vector at the unit. Choose a seed section detecting it and again set
  `a = x⁻¹` in that factor. The remaining translated sections are nonzero at
  `x`, so they generate along the tangent source. Tensor cancellation reduces
  nonvanishing along the tangent vector to the detecting seed section.

The assembly derives irreducibility from the published
`irreducibleSpace_of_smooth_of_isProper`; smoothness supplies local finite type.
The seed and square theorems have exactly the geometric hypotheses required
here. All inputs are imported by their current Library Lean names.

## Source and scope

This is the section form of the construction in J. S. Milne,
*Abelian Varieties*, author revision January 2, 2022, Theorem 7.1, pp.10–11,
using Theorem 6.7 and Remark 6.9, p.10. The registered source is
`milne-abelian-varieties-1986-author-2022`, SHA256
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`.
Milne uses the divisor `3 Σ Z_i` and triple translates with sum zero.
Here the corresponding objects are tensor cubes of line bundles and products
of translated sections. Their pullbacks reverse Milne's sign convention for
translated zero loci; this is explained in the assembly companion.
The complete retained author errata
`milne-abelian-varieties-1986-errata-2026-10-25` were consulted; their corrections
are incorporated into the retained author version and none concerns Theorem 7.1.
The supporting companions describe the implemented section argument, including
the tensor cancellation needed for tangent separation.

The proof retains arbitrary universes and characteristics. It allows `n = 0`:
the empty tensor product is the trivial line bundle, and its unit section gives
base-point freeness; the seed clauses rule out distinct rational points and
nonzero tangent vectors. This covers dimension zero without a positive
dimension hypothesis. The proof uses no projectivity or ample-existence theorem.

## Authorship

Worker 899 of the previous instance authored the recovered finite tensor and
conditional assembly proofs. Worker 2441 recovered and checked those modules,
updated their companions, and supplied the final application of the published
square theorem and this entry pair. The square proof is published separately
and is reused by import.
