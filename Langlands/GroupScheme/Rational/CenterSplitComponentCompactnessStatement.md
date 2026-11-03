# Compactness of the actual scheme-center point quotient

Author: Worker 101.

This module states WST-CEN-01. Both declarations are `Prop`-valued definitions;
neither is a proof of compactness. The point quotient and topology come from
`CenterSplitComponent`, whose interface design benefited from Worker 207.

## Exact target

Fix an actual field `F` with `ValuativeRel F`, `TopologicalSpace F`, and
`IsNonarchimedeanLocalField F`. For an actual group scheme `M` over `Spec F`,
`hM : IsConnectedReductive M`, a commutative group scheme `A`, an actual
homomorphism `i : A.toGrp ⟶ M`, and `hi : IsSplitComponent i`,
`CenterSplitComponentCompactness M hM A i hi` asserts

```text
CompactSpace (schemeCenterPoints M / centralRationalPointImage i
  hi.isCentralSplitTorus.isCentral).
```

The displayed slash denotes `QuotientGroup`, named `CentralPointQuotient` in
Lean. Its numerator is the full all-test scheme-center functor evaluated at
`Spec F`. Its denominator is the range of the actual homomorphism
`a ↦ ⟨rationalPoints.map i a, hi.isCentralSplitTorus.isCentral _ a⟩`.
In particular, its elements have actual preimages in `A(F)`.
No reduction, smoothening, identity component, or replacement by the radical
occurs in the numerator.

The definition obtains `IsAffineHom M.X.hom` from `hM`, and then
`IsAffine M.X.left` by `isAffine_of_isAffineHom`. It explicitly selects
`centralPointQuotientTopology`: the quotient topology of the subgroup topology
on `schemeCenterPoints M` inherited from `rationalPointTopology F M.X`.
Compactness therefore refers to this fixed topology, not to a freely chosen
instance. `CenterSplitComponentCompactnessStatement.{u}` universally quantifies
all these data, including `F : Type u`. It has no compactness premise and no
characteristic, splitting, tameness, or residue-characteristic restriction.

`IsConnectedReductive` retains geometric reductivity, rather than only
pseudo-reductivity over an imperfect field. `IsSplitComponent` retains both
all-test centrality and maximality among actual central split subtori.
The general target applies to any actual representing standard Levi satisfying
these predicates. Identifying such an `M_J` with the shared `standardLevi`
functor is a separate algebraic prerequisite; the present declaration does not
choose a different group in its place.

## Original-source passages

The target is derived from the following original passages and the point
comparison described below. None of the torus passages alone identifies the
point quotient in this target.

- Kaletha--Prasad, *Bruhat--Tits Theory: A New Approach* (2023), source
  `kaletha-prasad-2023-bruhat-tits-new-approach`: Definition 2.2.1, Remark 2.2.2
  and Fact 2.2.3, printed p.70 / PDF p.101, define boundedness, describe the
  affine analytic topology and equate closed bounded sets with compact sets
  over locally compact fields. Theorem 2.2.9, printed pp.71--73 / PDF
  pp.102--104, gives boundedness of the rational points of an anisotropic
  connected reductive group and its locally compact consequence. The proof
  of Proposition 2.2.12, printed pp.73--74 / PDF pp.104--105, uses a central
  split torus and an anisotropic factor with finite schematic intersection.
  It supplies no automatic surjectivity or finite-index theorem on rational
  points for a general isogeny.
- Kaletha--Prasad, *Corrections and additions*, version 1 November 2024,
  source `kaletha-prasad-2024-corrections`, PDF pp.24--25: Section 2.2 assumes
  the field Henselian throughout; Lemma 2.2.5 additionally requires a
  separable extension or a discrete valuation. Nonarchimedean local fields
  meet these field conditions. The positive valuation corrections to
  Sections 2.5(b) and 2.6(d) were also checked; this target uses no valuation
  sign convention.
- Milne, *Algebraic Groups* (2017), source `milne-2017-algebraic-groups`,
  Section 19.b, printed p.400 / PDF p.416: the full center of a reductive
  group is of multiplicative type; its largest subtorus is the radical, and
  the center need not be smooth or connected. Definition 12.17, printed
  p.236 / PDF p.252, retains subgroups and quotients of multiplicative type.
  Theorem 12.23, Corollary 12.24 and Notation 12.29, printed pp.240--241 /
  PDF pp.256--257, give the Galois character-module description, exact
  sequences, and the largest torus with finite scheme quotient.
  Exercises 12-5 and 12-6, printed p.252 / PDF p.268, describe anisotropy
  and the split/anisotropic torus decomposition.
- Milne, Theorem 5.14 and Proposition 5.18, printed pp.102--103 / PDF
  pp.118--119, supply algebraic quotients by normal subgroups, with affine
  quotient in the affine case. Definition 5.20 and Propositions 5.24--5.25,
  printed pp.104--105 / PDF pp.120--121, distinguish point cosets from
  quotient-scheme points and describe the fibers. Corollary 5.27 identifies
  the quotient map as a torsor. Example 2.72, printed p.61 / PDF p.77,
  identifies flat cohomology for `G_m` with the Picard group, supplying the
  split-torus torsor route to rational lifts and Zariski local triviality.
- Renard, *Représentations des groupes réductifs p-adiques*, 9 July 2026
  edition, source `renard-2026-representations-groupes-reductifs-padiques`:
  V.2.1, printed p.104 / PDF p.110, defines the center points, central
  maximal split torus and embedding-independent point topology; V.2.2,
  printed p.105 / PDF p.111, gives the almost-direct torus decomposition;
  V.2.6, printed p.108 / PDF p.114, states finiteness of `G/(⁰G A_G)` and
  compactness of `⁰G ∩ Z(G)`. These explain the consumer input. The
  present target keeps the full scheme center explicitly, including the
  nonsmooth data that require care in interpreting the notation in V.2.1.

The complete official Milne errata snapshot of 2 November 2026, source
`milne-2017-algebraic-groups-errata-2026-11-02`, was read. Its listed
corrections do not change the particular center, character classification,
quotient, or torsor passages used here.

## Route and retained proof obligations

A prospective proof first represents the full center by its actual
multiplicative-type group `Z` and forms the algebraic quotient `C = Z/A`.
The character-module classification and maximality of `A` must show that the
largest torus `C_t` is anisotropic. Kaletha--Prasad 2.2.9 then makes `C_t(F)`
compact. The finite scheme quotient `C/C_t` must be retained: its finite
set of rational points controls the number of cosets of `C_t(F)` in `C(F)`.
Together with the point topology of the closed inclusion, this gives the
route to compactness of the full `C(F)`, including its residual component
and nonsmooth scheme data.

The separate point bridge is essential. The actual map `q : Z → C` is an
`A`-torsor, with `A` a split torus. Triviality of such torsors over a field
gives rational lifts. Zariski local trivializations, and their compatibility
with the canonical point topology, give the quotient-topology comparison.
One must prove that `ker q(F)` is precisely the actual image of `i(F)` in
the numerator, and construct the resulting homeomorphism
`CentralPointQuotient i hi.isCentralSplitTorus.isCentral ≃ₜ C(F)`.
These algebraic and topological comparisons are proof obligations, not
assumptions in either Lean declaration.

This route does not infer a finite rational-point cokernel from an isogeny:
an inseparable power map in equal characteristic can have infinite-index
image. It also does not identify `(Z/A)(F)` with `Z(F)/A(F)` by definition.
Until the bridge is proved, the Lean target remains exactly the quotient of
actual rational-point groups. Equality of these center points with the
abstract center of `M(F)` is the separately named
`RationalCenterComparisonStatement`, not a premise of this compactness target.
