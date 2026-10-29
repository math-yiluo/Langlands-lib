# Bounded pushout target for positive-polyradius rational intersections

Author: Worker 965.

`Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation.RationalIntersection.BoundedPushoutStatement`
is a proposition definition (a `def` returning `Prop`). It states that the
actual all-products quotient of the published `GeneralizedAffinoid.RationalIntersection`
module, with its fixed constructed restriction maps, is the pushout of the two
original weighted rational quotients over the coefficient algebra, tested
against bounded maps into complete ultrametric normed commutative algebras.
This module does not prove the proposition; a separate proof task will name it.

## Quantified data

The proposition quantifies over:

- a normed field `K : Type u` with `[IsUltrametricDist K]` and
  `[CompleteSpace K]`;
- `A : PresentedAffinoidAlgebra K`, with presentation map
  `presentationMap K A` written as a bar;
- tuple lengths `m n : ℕ` and arbitrary positive polyradii
  `s : PositivePolyradius (Fin m)` and `t : PositivePolyradius (Fin n)`;
- scalar representatives `g h : GeneralizedTateAlgebra A.polyradius K`,
  `f : Fin m → GeneralizedTateAlgebra A.polyradius K` and
  `k : Fin n → GeneralizedTateAlgebra A.polyradius K`;
- the explicit hypotheses `hf : GeneratesUnitIdeal K A g f` and
  `hk : GeneratesUnitIdeal K A h k`, which mean exactly
  \((\bar g,\bar f_0,\ldots,\bar f_{m-1})=A\) and
  \((\bar h,\bar k_0,\ldots,\bar k_{n-1})=A\) as ideals of \(A\).

Coefficient completeness is required because the imported restrictions
`leftMap` and `rightMap` are constructed only under `[CompleteSpace K]` and
the two generation hypotheses; those hypotheses are their actual arguments.

## The three algebras and the fixed maps

All names below are the imported published declarations; nothing is
redefined here.

- \(B\) is `algebra K A s g f`, the original scalar weighted rational quotient
  for \((s,g,f)\), with structural map `baseMap K A s g f : A → B`.
- \(C\) is `algebra K A t h k`, the original scalar weighted rational quotient
  for \((t,h,k)\), with structural map `baseMap K A t h k : A → C`.
- \(D\) is `Algebra K A s t g h f k`, the actual all-products quotient: the
  scalar rational quotient with denominator \(gh\), all numerators \(F_aH_b\)
  of the denominator-extended tuples \(F=(g,f_0,\ldots)\),
  \(H=(h,k_0,\ldots)\), and product radii \(S_aT_b\) with
  \(S=(1,s_0,\ldots)\), \(T=(1,t_0,\ldots)\). Its structural map is
  `base K A s t g h f k : A → D`.
- `leftMap K A s t g h f k hf hk : B → D` and
  `rightMap K A s t g h f k hf hk : C → D` are the already constructed
  contractive bounded \(K\)-algebra maps. They send the original base
  classes to `base` and the original fraction coordinates to the product
  coordinates \(Z_{i+1,0}\) and \(Z_{0,j+1}\) respectively.

The original loci are \(U=\)`locus K A s g f` and \(V=\)`locus K A t h k` in
the actual `BanachSpectrum A`. The imported `intersectionHomeomorph`
identifies the spectrum of \(D\) with \(U\cap V\); these loci do not occur
in the proposition and are named only for the comparison below.

## Asserted conclusion

After the common quantifiers, the proposition is the conjunction of three
clauses.

1. `(leftMap K A s t g h f k hf hk).comp (baseMap K A s g f) = base K A s t g h f k`.
2. `(rightMap K A s t g h f k hf hk).comp (baseMap K A t h k) = base K A s t g h f k`.
3. For every `E : Type v` with `[NormedCommRing E] [NormedAlgebra K E]
   [IsUltrametricDist E] [CompleteSpace E]`, and all bounded \(K\)-algebra
   maps `α : BoundedAlgHom K B E` and `β : BoundedAlgHom K C E` satisfying
   `α.comp (baseMap K A s g f) = β.comp (baseMap K A t h k)`, there exists
   exactly one `θ : BoundedAlgHom K D E` with
   `θ.comp leftMap = α` and `θ.comp rightMap = β`.

Clauses 1 and 2 are exactly the imported theorems
`leftMap_comp_baseMap` and `rightMap_comp_baseMap`; they are restated so
that the proposition displays the full commutative square
\(A\to B\to D\), \(A\to C\to D\) whose universality clause 3 asserts. A
private development check confirmed that these two theorems discharge
clauses 1 and 2 verbatim. Clause 3 is the actual new content.

The agreement hypothesis in clause 3 is an equality of bounded algebra
maps \(A\to E\); by extensionality it is equivalent to
\(\alpha(\operatorname{baseMap}_B(a))=\beta(\operatorname{baseMap}_C(a))\) for
every \(a\in A\). Uniqueness of \(\theta\) is among all bounded
\(K\)-algebra maps \(D\to E\) satisfying both composition equations.

## Conventions and retained generality

A `BoundedAlgHom` is a \(K\)-algebra homomorphism whose underlying ring map
satisfies Mathlib's `RingHom.IsBounded`: there is a real \(c>0\) with
\(\|\varphi(x)\|\le c\|x\|\) for every \(x\). Neither the given maps
\(\alpha,\beta\) nor the asserted \(\theta\) need be contractions, and no
operator bound for \(\theta\) is specified.

The target universe `v` is independent of the coefficient universe `u`.
The target \(E\) need not be affinoid, need not satisfy \(\|1\|=1\), and may
be the zero ring. No factorization, extension operator, universal-property
certificate, coordinate values, or fractional monomial bounds are hypotheses;
the existence and uniqueness of \(\theta\) must be derived from the two given
bounded maps alone.

There is no hypothesis that \(m\) or \(n\) is positive, that \(A\) or any
quotient is nonzero, that the valuation of \(K\) is nontrivial, that the radii
lie in the value group, or that the radii are ordered or bounded by one.

## Relation to the spectral-image factorization property

This statement is not the affinoid-domain universal property of Berkovich's
Definition 2.2.1 for the intersection \(U\cap V\) of the two original loci.
That property tests against a single map from the base: for a bounded map
\(\psi:A\to E\) whose induced spectrum map has image in \(U\cap V\), it
asserts unique factorization through \(D\). Its test hypotheses are weaker,
so it is the stronger property for the targets it covers. Producing that
factorization requires deriving invertibility of \(\psi(\bar g),\psi(\bar h)\)
and bounds on the fractions from spectral containment, that is, a
spectral-radius argument.

Here, by contrast, the test data are two maps already defined on the
rational quotients \(B\) and \(C\). The images of the original fractions
under \(\alpha\) and \(\beta\), and their norm control, come directly from the
boundedness of \(\alpha\) and \(\beta\). No spectral containment, spectral
radius, or power-bound condition occurs in the proposition, and none is
identified with a weighted norm bound. Clause 3 is the universal property of
the commutative square of clauses 1 and 2 as a pushout of
\(B\leftarrow A\to C\), tested against all complete ultrametric normed
commutative \(K\)-algebras in universe `v` with bounded maps.

## Provenance

This is an internal derived target, not a theorem quoted from a source.
Its context is Berkovich, *Non-archimedean analytic spaces* (Trieste
lectures, 2009):

- Definition 2.1.6(i), printed/PDF page 8: weighted restricted series
  \(A\{r^{-1}T\}\) with norm \(\max_\nu\|a_\nu\|r^\nu\);
- Definition 2.1.11, printed/PDF page 8: affinoid morphisms are bounded
  homomorphisms;
- Exercise 2.2.2(ii), printed/PDF page 9: rational domains and their quotient
  presentation \(A\{p^{-1}T\}/(gT_i-f_i)\);
- Exercise 2.2.2(iii), printed/PDF page 9: intersections of rational domains
  are rational domains.

The all-products presentation of the intersection, the restriction maps, and
the common-target pushout formulation are internal constructions of the
imported `GeneralizedAffinoid.RationalIntersection` module and of this target.
The source assumes no common zeros of the generators in the spectrum; the
imported quotients and this statement use the explicit algebraic
`GeneratesUnitIdeal` hypotheses instead, without asserting equivalence of the
two conditions. Definition 2.2.1, printed/PDF page 9, is cited only to
distinguish its stronger factorization property, which remains a separate
obligation, as do comparisons with iterated relative rational quotients,
independence of the chosen representatives, structure sheaves, analytic
sites, and the Harris tower.

The registered original is `berkovich-2009-trieste-analytic-spaces`, PDF
SHA256 `8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.

## Proposed proof route

This paragraph is guidance for the later proof task, not part of the
statement. Apply the published bounded extension property
`RationalPresentation.boundedExtension` to \(D\), its unit-generated tuple
`generatesUnitIdeal K A g h f k hf hk`, the base map
\(\varphi=\alpha\circ\operatorname{baseMap}_B\), and the tuple
\(b_{ab}=\alpha(Y_a)\beta(W_b)\), where \(Y_0=W_0=1\) and \(Y_{i+1}\), \(W_{j+1}\)
are the original fractions. The fraction equations transported by
\(\alpha\) and \(\beta\), together with the agreement hypothesis, give
\(\varphi(\overline{gh})b_{ab}=\varphi(\overline{F_aH_b})\); boundedness of
\(\alpha,\beta\) and the original fraction norm bounds give the
product-radius monomial bounds. The two composition equations then follow
from base uniqueness on \(B\) and \(C\) under `hf` and `hk`, and
uniqueness of \(\theta\) from base uniqueness on \(D\).
