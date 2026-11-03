# A closed upper triangular embedding for a smooth connected solvable group

Worker 1485.

`Langlands.GroupScheme.SolvableTriangularEmbeddingStatement.{u}` is a
Prop-valued statement at arbitrary universe `u`. No proof is supplied.

For every algebraically closed field `k : Type u` and every group scheme
`H` over `Spec (CommRingCat.of k)`, assume exactly:

- `Smooth H.X.hom`;
- `IsAffineHom H.X.hom`;
- `ConnectedSpace H.X.left`;
- `IsSolvableGroupScheme H`.

The conclusion is the existence of `N : ℕ` and a group scheme homomorphism

```lean
j : H ⟶ GeneralLinear.blockParabolicScheme (Fin N) (CommRingCat.of k)
  (fun i => -(i.val : ℤ))
```

with `IsClosedSubgroup j`. The latter is the existing predicate saying
that the underlying scheme morphism `j.hom.hom.left` is a closed immersion.
The dimension and embedding are existential conclusions.

## Literature correspondence

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (2017), source `milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`:

- Theorem 16.30 (Lie–Kolchin), printed pp.334–335, one-based PDF pages
  350–351: a smooth connected solvable algebraic group over an
  algebraically closed field is trigonalizable.
- Proposition 16.2(a)⇔(c), printed pp.324–325, one-based PDF pages
  340–341: trigonalizability is equivalent to being isomorphic to an
  algebraic subgroup of the upper triangular group `T_N` for some `N`.
  Its proof explicitly obtains a closed immersion.
- Proposition 16.34(c)⇔(d), printed p.336, one-based PDF page 352:
  for a smooth connected algebraic group over an algebraically closed
  field, solvability of its abstract group of rational points is
  equivalent to solvability of the algebraic group.

The statement is a derived combination of these results with the
following encodings.

Milne works with affine group schemes of finite type over a field. Here
smoothness implies local finite presentation, hence local finite type;
an affine morphism is quasi-compact, so `H` is of finite type. Thus no
extra finite type hypothesis is needed.

The Library predicate `IsSolvableGroupScheme H` is solvability of the
abstract group of `AlgebraicClosure k`-valued points of the base change
of `H` to that algebraic closure. Since `k` is algebraically closed,
the canonical field map `k → AlgebraicClosure k` is an isomorphism.
Transporting points along this isomorphism and applying
Proposition 16.34(c)⇔(d) gives precisely Milne's solvability hypothesis
under the stated smoothness and connectedness assumptions.

The existing concrete scheme `GeneralLinear.blockParabolicScheme n R e`
is cut out in `GL_n` by the matrix entries `x_ij` with `e i < e j`.
For `n = Fin N` and `e i = -(i.val : ℤ)`, this inequality is equivalent
to `j.val < i.val`. Its equations therefore set exactly the entries
strictly below the diagonal to zero, identifying it with Milne's
upper triangular invertible matrix group `T_N`, over every test
algebra. Its published representability also identifies its points on
every test scheme over `Spec k` with those upper triangular matrices.
Consequently Proposition 16.2(c) gives a closed immersion into this
specific concrete group scheme. The changes of basis and identification
of a finite-dimensional vector space with `k^(Fin N)` are absorbed into
the existential choice of `j`.

The complete official author errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` was read. It contains no
correction to Theorem 16.30, Proposition 16.2 or Proposition 16.34. Its
correction on printed p.324 replaces “diagonalizable” with
“trigonalizable” in the chapter's introductory paragraph.

The Lean module imports the existing predicates from
`Langlands.GroupScheme.Absolute.Borel` and the concrete block scheme
through `Langlands.GroupScheme.Dynamic.GeneralLinearDecomposition`.
The literature correspondence above is explanatory; it does not
formalize the Lie–Kolchin theorem or the solvability comparison.
