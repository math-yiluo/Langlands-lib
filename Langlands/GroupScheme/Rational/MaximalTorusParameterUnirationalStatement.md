# Unirationality of the same actual maximal-torus parameter scheme

Author: Worker 1614.

`Langlands.GroupScheme.MaximalTorusParameterUnirationalStatement.{u}` is
a proposition definition at arbitrary universe `u`. For every field
`k : Type u`, every smooth connected affine group scheme `G` over
`Spec k`, and every maximal torus `j₀ : T₀.toGrp ⟶ G`, it asserts
`PointTopology.IsUnirational k Q` for every actual scheme `Q` and morphism
`q : G.X ⟶ Q` satisfying the published predicate
`IsMaximalTorusParameter j₀ q`.

The conclusion uses the published definition from
`Langlands.AlgebraicGeometry.PointTopology.UnirationalDensity`. It requires
a finite coordinate type `ι`, a nonempty open subscheme `U` of the actual
affine space `𝔸(ι; Spec k)`, and an actual morphism over `Spec k` from `U`
to this very `Q`, with dense underlying image. Both the parameter predicate
and the conclusion refer to the same input `Q`; its supplied projection
`q` retains all the predicate's geometric and conjugation properties.
The statement imposes no infinitude, perfection, reductivity, splitness or
characteristic hypothesis and assumes no rationality theorem.

The source is SGA 3, Tome II, Exposé XIV, Théorème 6.1, in the retained
Gille–Polo December 2008 recomposition, `Expo14.pdf`, one-based PDF
pages 25–27, printed pages 221–223 (original marginal pages 335–338).
For a smooth algebraic group over any field, the theorem states rationality
of the scheme of maximal tori, identified with the scheme of Cartan
subgroups. Its proof treats infinite and finite fields separately.
Rationality gives a birational parametrization by finite-dimensional
affine space; restricting to a nonempty domain of definition gives the
dominant actual morphism required by `IsUnirational`. Corollaire 6.4,
PDF page 27, adds an infinite-field assumption for rational-point density.
That assumption is absent from the present unirationality target.

Here is the source specialization to the supplied quotient interface.
The group in the statement is an algebraic group: affineness gives
quasi-compactness and separatedness, and smoothness supplies local finite
presentation over the field. Exposé XII, Corollaire 1.10, `Expo12.pdf`,
PDF page 6, printed page 124 (original page 188), represents the functor of
maximal tori and identifies it, once `T₀` is chosen, with the quotient
`G/N_G(T₀)`. The local conjugacy input is XII, Théorème 1.7(c),
PDF pages 4–5, printed pages 122–123. Over a field its locally constant
rank condition is automatic.

To explain why an arbitrary supplied `Q,q` has that same meaning, put
`N = torusNormalizer j₀`. Since `j₀` is a closed torus inclusion, this
published all-test normalizer is the normalizer subgroup functor of
`T₀`. The parameter predicate says, for every scheme test `U` and every
`g,h : U ⟶ G.X`, that `q(g) = q(h)` exactly when `g⁻¹h ∈ N(U)`.
Thus its kernel relation is the right-coset relation, naturally on all
tests and their refinements. Moreover `q` is smooth, surjective and
quasi-compact, hence faithfully flat and quasi-compact. Every section of
`Q` lifts after that cover's base change. Descent therefore identifies its
represented sheaf with the quotient sheaf `G/N`; the all-test relation
ensures that local lifts have exactly the required equivalence relation.
The representable quotient in XII 1.10 and `Q` represent the same sheaf,
so Yoneda gives an isomorphism over `k`. Transporting a parametrization
along this isomorphism gives a morphism into the original `Q`.

These descent and parametrization paragraphs explain the mathematical
derivation of this statement from the source. The Lean module only
defines the proposition; it proves neither the quotient identification
nor the unirationality assertion. Existence of a suitable `Q,q` and a
proof of this exact proposition remain separate obligations.

The retained source is registered as
`sga3-exposes-xi-xii-xiv-gille-polo-2008`, in
`literature/Grothendieck - SGA 3 Exposes XI, XII and XIV (Gille-Polo provisional recomposition, December 2008)/`.
The original French text was read at the cited locations. The mirrored
PDFs are [Exposé XII](https://wstein.org/sga/SGA3/Expo12.pdf) and
[Exposé XIV](https://wstein.org/sga/SGA3/Expo14.pdf).
