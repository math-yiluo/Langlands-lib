# Multisegment and special-block Langlands classification statements

Authors: Worker 34 and Worker 126. Worker 34 implemented the statements;
Worker 126 contributed the source and dependent-type audit incorporated here.

This module states the socle classification of Zelevinsky (1980), Theorem 6.1
and §§6.3–6.5, the special-head classification of Rodier (1982), §4.3 Theorem 3,
and the essentially square-integrable block form of Henniart (2002), §2.8.
Every declaration is a proposition-valued definition. No classification theorem
is proved or assumed by this module.

## Objects and conventions

Fix a prime `p`, a finite p-adic extension `F : PadicField p`, and a compatible
realization `T : F.TopologicalData`. Put `ν = |det|`, using the residue-normalized
absolute value. All representations are smooth complex representations.
Products are the actual `T.normalizedProductInductionFunctor` from the standard
upper block parabolic, acting by right translation. Henniart §2.5 (pp.594–595)
specifies normalized upper induction; Rodier §§1.2 and 2.1 (pp.202–203) specify
right translation and the upper parabolic.

A segment is the published positive-length sequence
`[ρ, νρ, …, ν^(m−1)ρ]` based on a supercuspidal isomorphism class. Its degree is
`m` times the rank of `ρ`. A multisegment is a finite multiset of these segments,
including multiplicities. `IsOrdering` means equality with the multiset of a
`Fin r` family. `IsPrecedenceOrdered` means exactly
`∀ i j, i < j → ¬ (Δ i).Precedes (Δ j)`.

`SegmentProductDatum n` carries actual segments, their degree sum equal to `n`,
and actual block representations. It contains no full-product constituent.
`HasSegmentSocles` requires the blocks to be the irreducible socles of the
increasing cuspidal segment products; `HasSegmentHeads` requires their
irreducible heads. These are Zelevinsky's `⟨Δ⟩` and `⟨Δ⟩ᵗ`, respectively
(§§3.1 and 9.1), and Rodier's `Z(Δ)` and `L(Δ)` (§3.4, Proposition 9, and §4.1).

The published `IsIrreducibleSocle` relation asserts an actual injective
intertwiner and equality of the images of all irreducible embeddings.
`IsIrreducibleHead` asserts an actual surjective intertwiner and equality of
the kernels of all irreducible quotient maps. Thus the existence clauses state
uniqueness as a subobject or quotient object, not only uniqueness of an
isomorphism class. The weaker `IsZelevinskySubrepresentation` and
`IsLanglandsQuotient` relations require the appropriate ordered blocks and an
irreducible embedding or quotient, without image/kernel uniqueness.

A multisegment relation `a.IsZelevinskySocle π` or `a.IsLanglandsHead π` asserts
that some datum with multisegment `a` has the relevant constituent. Its definition
does not assume independence of this witness. The universal datum statements
below assert existence for every permitted ordering and every actual block
representative. Their classification statements supply independence.

## Declaration and source map

All names in this table are in `Langlands.Classification`. The source labels
are expanded with exact registered bytes below.

| Declaration | Assertion | Source or derivation |
| --- | --- | --- |
| `MultisegmentNonprecedenceEnumeration` | Every multisegment has a nonprecedence enumeration whose degree sum is its degree. | Ze80 §6.5, p.189; the degree identity is bookkeeping for the published multiset degree. |
| `MultisegmentConstituentDataExistence` | Every multisegment has ordered actual segment-socle data and ordered actual segment-head data, of its degree. | Derived combination of Ze80 §§3.1, 6.5, 9.1: enumeration and existence of individual segment constituents. No full-product constituent is assumed. |
| `OrderedMultisegmentSocleExistence` | Every permitted product of segment socles has an irreducible socle. | Ze80 Theorem 6.1(a), p.188; §§6.2–6.3 give its proof route. |
| `OrderedMultisegmentSocleProductIndependence` | Ordered socle products with the same multisegment are isomorphic as full representations. | Ze80 Proposition 6.4(2), p.189; actual representatives are transported by the induction functor. |
| `OrderedMultisegmentSocleClassification` | Any irreducible subrepresentations of two permitted products are isomorphic iff their multisegments agree. | Ze80 Theorem 6.1(a,b); uniqueness in (a) permits the weaker subrepresentation hypotheses. |
| `MultisegmentSocleExistence` | Every multisegment has a socle realization at its degree. | Ze80 §§6.1(a), 6.5, using enumeration and individual block existence. |
| `MultisegmentSocleExhaustion` | Every irreducible smooth representation of rank `n` is such a socle, and the parameter's degree equals `n`. | Ze80 Theorem 6.1(c) and §6.5. |
| `MultisegmentSocleClassification` | Two socle realizations at the same rank are isomorphic iff their multisegments are equal. | Ze80 Theorem 6.1(b) and §6.5. |
| `OrderedMultisegmentHeadExistence` | Every permitted product of segment heads has an irreducible head. | Ro82 §4.3 Theorem 3(a), p.211. |
| `OrderedMultisegmentHeadClassification` | Any irreducible quotients of two permitted products are isomorphic iff their multisegments agree. | Ro82 Theorem 3(a,b), pp.211–212; uniqueness permits the weaker quotient hypotheses. |
| `MultisegmentHeadExistence` | Every multisegment has a head realization at its degree. | Ro82 Theorem 3(a), with Ze80 enumeration and segment-head existence. |
| `MultisegmentHeadExhaustion` | Every irreducible smooth representation of rank `n` is such a head, and the parameter's degree equals `n`. | Ro82 Theorem 3(c), p.212. |
| `MultisegmentHeadClassification` | Two head realizations at the same rank are isomorphic iff their multisegments agree. | Ro82 Theorem 3(b), expressed as multiset equality. |
| `MultisegmentConstituentRepresentativeInvariance` | Each multisegment relation is invariant under an actual isomorphism of its output. | Internal derived assertion: compose the injective/surjective constituent intertwiners with the isomorphism and its inverse, preserving images or kernels. |
| `SquareIntegrableLanglandsHeadExistence` | Every positive-rank datum of essentially square-integrable blocks with weakly decreasing unitary exponents has an irreducible head. | H02 §2.8, p.596. |
| `SquareIntegrableLanglandsQuotientUniqueness` | Any two irreducible quotients of the same such product are isomorphic. | H02 §2.8, consequence of its unique irreducible quotient. |
| `SquareIntegrableLanglandsExhaustion` | Every positive-rank irreducible smooth representation is the head of such genuine block data. | H02 §2.8, surjectivity of the nonzero free commutative monoid on essentially square-integrable classes. |
| `SquareIntegrableLanglandsClassification` | Irreducible quotients of two such data are isomorphic iff their blocks match up to permutation, rank equality and actual isomorphism. | H02 §2.8, the bijection and independence of the permitted ordering. |

`MultisegmentClassificationTheorems F T` is the conjunction of these eighteen
clauses. `PadicMultisegmentClassificationTheorems` quantifies it over every
prime, finite p-adic extension, and compatible realization. These bundles add
no hypothesis and do not turn the statements into proofs.

## Order translation

The no-earlier-precedes-later condition is the same in Ze80 Theorem 6.1(a)
and Ro82 Theorem 3(a). The former uses segment socles; the latter uses segment
heads. Neither passage reverses this segment order. Within an individual
segment both constituents are defined from the increasing cuspidal product.

H02 §2.8 instead orders the essentially square-integrable blocks by weakly
decreasing unitary exponent. These ordering conditions are not equivalent.
For a segment written `[ν^aρ₀, …, ν^bρ₀]` with unitary supercuspidal base `ρ₀`,
the special head has unitary exponent `(a+b)/2`. Equivalently, for a base `ρ`
and length `m`, it is `α(ρ) + (m−1)/2`. For linked segments, precedence means
that both endpoints increase strictly, so the mean increases. Decreasing
special-block exponents therefore imply nonprecedence.

Conversely, to compare a nonprecedence ordering with H02's ordering, sort by
these exponents. Any adjacent inversion is unlinked: if it were linked, its
increasing means would force the forbidden precedence. Unlinked special-head
factors commute up to isomorphism. The source inputs for that step are Ze80
Theorem 9.7(a), which makes both two-factor products irreducible, and Theorem
1.9, which gives equal composition factors, followed by associativity for
larger products. Theorem 1.9 alone does not give general product isomorphism.
This explains the relation between the two source forms; no sorting proof or
special-head exponent theorem is implemented here. The segment-head clauses
are sourced directly to Ro82 Theorem 3, independently of that proof route.

## Block comparison, representatives and boundary ranks

`SquareIntegrableLanglandsDatum` contains the actual blocks, their
irreducibility and essential square-integrability, chosen unitary-exponent
witnesses, and the antitone condition. Existence of a quotient is not a field.
The comparison in `SquareIntegrableLanglandsClassification` is

```lean
∃ e : Fin d.shape.length ≃ Fin d'.shape.length,
  ∀ i, ∃ h : d.shape.size i = d'.shape.size (e i),
    Nonempty ((h ▸ d.blocks i) ≅ d'.blocks (e i))
```

The finite equivalence preserves multiplicities. The equality `h` transports
one block through the family `k ↦ SmoothRep ℂ (GeneralLinear k F.Carrier)`;
the isomorphism then compares representations of the same group. Forms,
exponent witnesses and proofs are not compared. This is H02's unordered family
of isomorphism classes, rather than equality of auxiliary datum structures.
The uniqueness of the unitary exponent is an underlying theorem, not an
extra equality imposed on chosen witnesses.

The multisegment clauses include the empty multiset and rank zero. Ze80 §6.5
explicitly assigns the identity representation of `G₀` to the empty socle
parameter. For the head clauses the empty case is an elementary extension:
the empty tensor product and its normalized induction to the trivial group
are the one-dimensional trivial representation. This is derived provenance,
not a claim that Ro82 separately states an empty-head theorem. Positive segment
degrees force a rank-zero datum to be empty. The four square-integrable clauses
explicitly require `0 < n`, matching H02's nonzero monoid and nonempty list;
positive block sizes then force at least one block.

## Published dependencies and remaining proof obligations

The sole direct import is `Classification/LanglandsData`. Its published
transitive definitions provide:

- `Classification/Segments`: supercuspidal classes, segments, multisegments,
  degree, precedence, ordering and individual constituent relations;
- `Classification/ConstituentRelations`: irreducible subrepresentation, quotient,
  socle and head on actual intertwining maps;
- `Classification/Tempered` and `Classification/Essential`: the analytic
  essential square-integrability predicate and unitary-exponent data;
- `Induction/BlockFactors`: actual normalized tensor-product induction and its
  functorial action on block isomorphisms;
- the smooth representation category and the p-adic field/topology interfaces.

The published `Classification/SegmentConstituentStatement` supplies individual
segment-existence proposition targets for future proofs. It is not imported as
a proof or assumed hypothesis. Other mathematical inputs for future proofs
include nonperiodicity of positive norm twisting on supercuspidal classes
(to identify source set-segments with the stored beginning/length data),
segment constituent uniqueness and representative transport, and the source
classification theorems themselves. No theorem is made true by a data constructor.

Ro82 lists Bernstein's square-integrable converse, tempered classification,
and the Langlands quotient theorem as proof inputs. Those references are not
proofs supplied by this file; the upstream proof-source gaps remain. In
particular, Ze80 §9.17 is explicitly a conjecture in that original and is not
used to justify quotient classification. There is no assertion here of
product irreducibility, genericity, square-integrability of segment heads,
tempered induction or the strict tempered regular-chamber theorem. Twist,
contragredient and central-character compatibilities form a separate statement
unit. This module neither assumes nor proves their conclusions.

## Universes

The field carrier lies in `Type uF`. Set `U = max uF uV`, with `uF` and `uV`
independent. Multisegments and both data types are instantiated at
`.{max uF uV, uF}`; all cuspidal carriers, actual blocks, induced products and
output representations consequently lie in `Type U`. Induction is closed in
this universe since `max uF U = U`. Exhaustion therefore does not require
shrinking an arbitrary irreducible input to a smaller carrier universe.
There is no finite-dimensionality assumption. Every local declaration has
outer telescope `{p} [Fact p.Prime] (F : PadicField p) (T : F.TopologicalData)`
and returns `Prop`; the all-fields aggregate itself has type `Prop`.

## Registered originals

- **Ze80:** A. V. Zelevinsky, *Induced representations of reductive p-adic
  groups II. On irreducible representations of GL(n)*, Ann. Sci. ENS (4) 13
  (1980), 165–210. ID `zelevinsky-1980-induced-ii`; PDF SHA-256
  `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
  Main locators: §§3.1 (pp.180–181, PDF17–18), 6.1–6.5 (pp.188–189,
  PDF25–26), 9.1 (p.197, PDF34). Order-comparison inputs: Theorem 1.9
  (p.174, PDF11), Theorem 9.7(a) (p.199, PDF36).
- **Ro82:** F. Rodier, *Représentations de GL(n,k) où k est un corps p-adique*,
  Séminaire Bourbaki, exposé 587, Astérisque 92–93 (1982), 201–218.
  ID `rodier-1982-gln`; PDF SHA-256
  `389a9155f59022f5f5403bf568216f66b407b6d47e98221d115dcd85e076c8fc`.
  Main locator: §4.3 Theorem 3(a–c), pp.211–212 (PDF12–13).
  Conventions: §§1.2, 2.1, 3.4 Proposition 9, and 4.1.
- **H02:** G. Henniart, *Une caractérisation de la correspondance de Langlands
  locale pour GL(n)*, Bull. Soc. Math. France 130 (2002), 587–602.
  ID `henniart-2002-characterization`; PDF SHA-256
  `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.
  Main locator: §2.8, p.596 (PDF10); conventions and special heads:
  §§2.5–2.6, pp.594–595 (PDF8–9).
