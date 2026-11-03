# Proper images in homogeneous spaces of solvable groups

Worker 1351.

`Langlands.GroupScheme.SolvableOrbitProperImageFiniteStatement.{u}` is a
definition returning `Prop`. It states a derived finite-image form of Milne,
*Algebraic Groups* (2017), Theorem 17.1 and Corollary 17.2, printed
pp.352–353 (one-based PDF pp.368–369). This module supplies no proof.

For every algebraically closed field `k : Type u`, put
`S = Spec (CommRingCat.of k)`. The acting group is an actual
`G : GroupScheme S`, smooth and affine over `S`, with connected underlying
space and the unchanged published predicate `IsSolvableGroupScheme G`.
Smoothness gives local finite type, and affineness gives quasi-compactness,
so this is a finite-type group. There is no restriction on the characteristic
or on `u`. Solvability refers to the abstract group of algebraic-closure
points in `Absolute.Borel`; no split series or structural theorem is
supplied as an extra premise.

The target `O : Over S` is reduced and separated, locally of finite type
and quasi-compact over `S`. It carries an actual `a : SchemeAction G O`
and a rational section `x : Over.mk (𝟙 S) ⟶ O`. The transitivity premise is

```lean
∀ y : Over.mk (𝟙 S) ⟶ O,
  ∃ g : Over.mk (𝟙 S) ⟶ G.X, a.act g x = y
```

This is transitivity on rational points of the supplied scheme and action.
It does not assert transitivity over every test scheme or assume a smooth
stabilizer. In particular, no quotient model is an input. The section `x`
ensures that `O` is nonempty. The proposition concludes, for every relative
scheme `Z` proper over `S` and every actual relative morphism `j : Z ⟶ O`,

```lean
(Set.range j.left).Finite
```

Here the range is the image on all underlying scheme points. `Z` need not
be reduced, connected, smooth or nonempty, and `j` need not be an immersion
or equivariant. The conclusion is finite image, rather than finiteness of
`Z` or a claim that `j` is a finite morphism.

The source correspondence is derived as follows. Over an algebraically
closed field, finite-type closed points are rational. The orbit-map
discussion following Proposition 1.65, printed pp.26–27 (PDF pp.42–43),
identifies a rationally transitive reduced target with the reduced orbit of
`x`: its orbit map is surjective, and the reduced structure on that image
is the given one on `O`. Corollary 17.2 then rules out a
positive-dimensional complete subscheme in `O`. To obtain the stated
finite-image formulation, a map from a proper scheme to the separated
scheme `O` is proper, and its closed image with reduced structure is
proper over the field. Reduction does not change the underlying image.
The image is therefore a complete zero-dimensional finite-type scheme;
its underlying point set is finite. This also covers reducible and
nonreduced `Z`. Milne's completeness and proper-image conventions are in
A.75 and A.76, printed p.583 (PDF p.599), especially A.75(b),(d) and
A.76(b),(e).

The published point-group solvability predicate is a reformulation of
Milne's scheme-theoretic solvability for smooth affine groups, using
Propositions 6.20(b), 6.21 and 6.30 and Corollary 6.31, printed
pp.130–132 (PDF pp.146–148). The proof of this statement must establish
any such comparison and homogeneous-space geometry it uses. This
explanation does not import them as assumptions or claim they are
already proved in Lean.

This statement is a prerequisite for `SolvableProperFixedPointStatement`.
Taking `Z = O` and `j = 𝟙 O` when `O` is proper yields finiteness of the
underlying orbit, to which `SchemeAction.isFixed_of_finite` applies.
Closed-orbit existence and the general solvable fixed-point theorem
remain separate proof obligations. The statement does not use Borel
conjugacy, a general linear group specialization, or a theorem depending
on the fixed-point conclusion.

The registered original is `milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The complete official errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`,
was checked. Its entries do not change Theorem 17.1 or Corollary 17.2.
