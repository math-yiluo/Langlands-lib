# Multiplicity freeness of products of distinct supercuspidal data

`Langlands.Classification.DistinctCuspidalProductMultiplicityFree` is a
Prop-valued definition stating Zelevinsky's Proposition 2.1(c) for the Library's
actual upper normalized induction. It supplies a statement target, with no
proof of that proposition.

The original source is A. V. Zelevinsky, *Induced representations of reductive
p-adic groups II. On irreducible representations of GL(n)*, Annales scientifiques
de l'École Normale Supérieure (4) **13** (1980), 165–210, §2.1, Proposition
2.1(c), printed p.176 / retained PDF page 13. The registered source is
`zelevinsky-1980-induced-ii`, SHA-256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
The finite-length background is Proposition 1.4, printed p.171 / PDF page 8;
the product notation is recalled in §1.8 and cuspidal classes are specified in
§1.10, printed p.174 / PDF page 11.

Zelevinsky fixes a finite subset `R` of irreducible cuspidal isomorphism classes,
allowing the classes to belong to different positive-rank general linear
groups. For each ordering `λ` of `R`, the representation `π(λ)` is the normalized
product of those classes in that order. Proposition 2.1(c) says that each of its
composition factors occurs with multiplicity one. Parts (a) and (b) obtain this
from multiplicity-one cuspidal Jacquet factors and detection of each simple
constituent; this file states only the resulting product assertion.

The Lean proposition has parameters an arbitrary prime `p`, an actual p-adic
field `F : PadicField.{uF} p`, and any compatible realization
`T : F.TopologicalData`. It quantifies over every positive total rank `n`, every
`B : BlockShape n`, and actual irreducible supercuspidal objects `A i` on the
blocks. The block shape already includes positivity of every block rank and
their sum being `n`. Supercuspidality and irreducibility are properties of the
bundled factors; they are not supplied conclusions of a theorem.

The input distinctness hypothesis is injectivity of
`i ↦ ⟨B.size i, (A i).isoClass⟩` into
`Σ d : ℕ, SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := d)`.
Its finite image is exactly a finite set of cuspidal classes occurring once
each, and the block indices give an ordering of that image. The rank coordinate
keeps classes for different groups distinct. Classes of the same rank may be
related by a nontrivial determinant twist; injectivity imposes no twist
separation. Actual representatives are used to form the product.

The product is precisely
`(T.normalizedProductInductionFunctor B).obj (fun i => (A i).obj)`.
This published functor uses the standard upper block parabolic, the positive
half-modulus normalization, the external tensor product of the factors, and
right translation. The factor-carrier universe `uV` is independent of the field
universe `uF`; the induced carrier lies in `Type (max uF uV)`.

The conclusion asserts existence of a natural number `m` and
`s : ObjectRepFiltration P.obj m`. This existing filtration starts at zero and
ends at the whole actual induced representation `P`. The conjunct
`s.HasSimpleFactors` makes every actual successive quotient irreducible and
nonzero. The remaining conjunct says that a `Nonempty` actual
`Representation.Equiv` between the graded factors at indices `i` and `j` forces
`i = j`. Thus each simple isomorphism class occurs at most once in the series.
The published `Langlands.jordanHolderSeriesComparison` in
`Filtration.JordanHolderComparisonProof` matches any two such simple series by
a bijection of indices and actual equivariant quotient isomorphisms. It follows
that this multiplicity condition is independent of the chosen composition
series. That comparison explains the formulation; it is not an extra hypothesis
or an imported proof of Proposition 2.1(c).

A finite composition series allows nonsplit extensions. The conclusion asserts
no semisimplicity or direct-sum decomposition of `P`. The one-block case is
included, and no finite-dimensionality, chosen constituent, pre-existing
composition series, or theorem-valued input is assumed. Only the published
supercuspidal, actual induction, and actual filtration definitions are imported;
no generic support construction or classification theorem is introduced.
