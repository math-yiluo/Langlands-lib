# Norm-one presentations for simply connected inner type A

Author: Worker 165.

`Langlands.GroupScheme.InnerTypeANormOneStatement.{u}` is a prerequisite
statement for the family-(i) part of the local rank-one classification.
It asserts the classical identification over an arbitrary field; it does
not prove that identification or the local classification.

For actual `d : TitsIndexData G`, `d.HasInnerTypeA n` means all of:

- `n > 0`;
- there is a bijection from every actual simple vertex `d.Vertex` to
  `Fin n` carrying every actual integral Cartan pairing to
  `CartanMatrix.A n`;
- every element of the full absolute Galois group acts as the identity
  on every simple vertex through `d.star`.

Here the actual Mathlib matrix `CartanMatrix.A n` has `n` rows and
columns. Its diagonal entries are 2, entries between consecutive indices
are minus 1, and all other entries are zero. Thus `n` is the absolute
rank and the intended diagram is `A_n`. The imported Mathlib docstring
calls this matrix `A_{n-1}`; the present convention follows its actual
`Fin n` indices and formula. The condition compares all Cartan entries,
not only adjacency or a freely chosen type label. Its full-star condition
is Tits's definition of inner type. It places no constraint on the
zero-restriction vertices, so it includes arbitrary split rank and
anisotropic groups. The predicate contains no algebra, norm map,
classification conclusion or supplied group isomorphism.

The statement quantifies over `K : Type u` with `Field K`, and a group
scheme `G` over `Spec K` with affine structure morphism and locally of
finite type. Given actual index data `d`, a natural number `n`, algebraic
simple connectedness of `G`, absolute almost-simplicity of `G`, and
`d.HasInnerTypeA n`, it asserts the existence of `A : Type u` with a ring
structure, a `K`-algebra structure, finite dimensionality, centrality and
simplicity, such that its reduced degree is `n + 1` and there is an actual
isomorphism `G ≅ CentralSimpleUnits.normOne K A` over `Spec K`.

`normOne K A` is the published kernel group scheme of the actual reduced
norm on the unit group. The isomorphism is in the category of group
schemes, rather than an isomorphism only of rational-point groups.
`Langlands.CentralSimple.reducedDegree K A` is the natural square root of
`Module.finrank K A`; the published central-simple dimension theorem
makes the stated degree equivalent to dimension `(n + 1)^2`. The
existential algebra need not be a division algebra: a split group of
type `A_n` uses a matrix algebra of size `n + 1`.

The field is arbitrary. There is no valuation, topology, local-field,
perfectness or characteristic restriction. The universe `u` is arbitrary
and common to `K` and `A`. The extra `LocallyOfFiniteType` instance is the
one required by the published actual index interface; it does not impose
an additional mathematical restriction on the semisimple groups under
consideration.

## Source and convention comparison

The registered source is J. Tits, *Classification of algebraic semisimple
groups*, Proc. Sympos. Pure Math. 9 (1966), 33–62,
`tits-1966-classification-algebraic-semisimple`, proceedings PDF SHA-256
`962203f9e47e9c3c43fc1049a38e28c751aa42beb7ee5250a095a132e215a5d4`.
The relevant original passages are:

- Section 2.3, printed p.39 / PDF p.44: the index uses the actual simple
  roots, their Dynkin diagram, zero-restriction subset and full star
  action. Inner type means trivial star action.
- Table II explanations, printed pp.54–55 / PDF pp.59–60, and the type
  `1A_n` entry on printed p.55 / PDF p.60: a representative is
  `SL_{r+1}(D)` for a central division algebra `D` of degree `d`, with
  `d(r+1) = n+1`. This description applies over arbitrary fields; the
  special-field rows are separate refinements and are not used here.
- Sections 1.5.4–1.5.5, printed p.38 / PDF p.43, and 3.1.1, printed p.45 /
  PDF p.50: central isogeny classes and the simply connected member, with
  the field structure on central quotients.

The source explicitly describes one representative of each strict
isogeny class and writes its abstract group of rational points. The Lean
statement asks for the simply connected algebraic group in that class,
expressed using the actual group scheme `SL_1(A)`, with
`A = Matrix (Fin (r+1)) (Fin (r+1)) D` in the description. This algebra has
degree `d(r+1) = n+1`. Passing from that presentation to the supplied
simply connected `G` is part of the statement's mathematical proof
obligation; no rational-point-only comparison is substituted for it.
The statement does not assert uniqueness of `A` or compatibility of an
isomorphism with a chosen pinning.

The predicate `HasInnerTypeA` is the direct formal expression of the
source's actual diagram and full-action definition using the existing
Library index and Mathlib Cartan matrix. The local proof program still
needs to determine which actual groups have this type, to prove this
identification, and to prove the matrix norm-one split-rank formula.
Only after those inputs are proved does the constructed
`CentralSimpleNormOneDivisionModel` bridge force the binary model from
split rank one. The remaining families and the exclusion of exceptional
and trialitarian indices are separate obligations.
