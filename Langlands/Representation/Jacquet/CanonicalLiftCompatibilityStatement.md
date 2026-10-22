# Compatibility of actual stable-image canonical Jacquet lifts

This module states two compatibility targets for the existing constructions in
`CanonicalLiftDefinitions` and `BlockIwahoriDefinitions`. All three declarations
are transparent Prop-valued definitions in `Langlands.Jacquet`. This module
proves neither target and installs no abstract canonical-lift object.

## Parameters and hypotheses

The declarations retain every prime `p` with `[Fact p.Prime]`, every
`F : PadicField.{uF} p`, supplied `T : F.TopologicalData`, every natural rank
`n`, every `B : GeneralLinear.BlockShape n`, and every complex module
`V : Type uV`. The field and representation universes are independent.
Each clause installs exactly `T.topology` and
`T.generalLinearTopologicalGroup n`, so its open subgroups and smoothness use
the actual general linear group with the supplied topology.

Each clause quantifies over every actual representation
`ρ : Representation ℂ (GeneralLinear n F.Carrier) V` and
`hAdmissible : IsAdmissible ρ`, using `hρ := hAdmissible.1` as its smoothness
witness. Compactness is supplied separately from openness. All factorization
hypotheses use the published `B.HasBlockIwahoriFactorization T` predicate:
ordered multiplication of the actual lower, Levi, and upper intersections,
together with the conjugation containments for every weakly contracting tuple.
This is the existing stronger weak-chamber specialization of the source's
strict-chamber condition; it is not redefined here.

All scalar tuples have type `Fin B.length → F.Carrierˣ`. The published
`B.IsStrictlyContracting T` predicate requires normalized absolute value less
than one for every forward ratio `a_i/a_j`, with `i < j`. Thus the radical
being contracted is the actual upper radical
`N := B.unipotentSubgroup F.Carrier`. Its Jacquet quotient is the existing
ambient type `Coinvariants ρ N`.

## Tuple independence

`BlockStableImageTupleIndependenceClause F T B V` quantifies over an actual
compact open subgroup `K`, its compactness witness `hK`, its block Iwahori
factorization, and two independently chosen strictly contracting tuples `a`
and `b`. It asserts

```lean
stableImage ρ hρ K hK (B.blockScalar F.Carrier a) =
  stableImage ρ hρ K hK (B.blockScalar F.Carrier b)
```

This is equality of submodules of the same `fixedVectors ρ K.toSubgroup`.
For a tuple `a`, that submodule is exactly the infimum of the ranges of all
natural powers of `compressedAction ρ hρ K hK (B.blockScalar F.Carrier a)`.
Compression applies the actual representation action and then the existing
normalized compact average. Neither a chosen inverse nor a chosen lift is
part of the clause.

## Nested-subgroup averaging

`BlockStableImageNestedAverageClause F T B V` quantifies over compact open
subgroups `K1` and `K0`, their respective compactness witnesses `hK1` and
`hK0`, the inclusion `K1 ≤ K0`, and factorization hypotheses for both. Choose
independent strictly contracting tuples `a1` and `a0`, and arbitrary vectors
`w1` and `w0` in their respective existing stable-image carriers. Their
ambient images are exactly

```lean
v1 := stableImageToRepresentation ρ hρ K1 hK1
  (B.blockScalar F.Carrier a1) w1
v0 := stableImageToRepresentation ρ hρ K0 hK0
  (B.blockScalar F.Carrier a0) w0
```

The clause asserts the implication

```lean
Jacquet.mk ρ N v1 = Jacquet.mk ρ N v0 →
  Compact.averageMap ρ hρ K0 hK0 v1 = v0
```

The premise compares classes in the same ambient `Coinvariants ρ N`, rather
than in the possibly different compact-Levi fixed-vector codomains. The
conclusion is equality in `V`, with normalized averaging over the **larger**
subgroup `K0`. The common-class premise is essential: the clause does not
claim that averaging an arbitrary smaller-subgroup stable lift preserves its
Jacquet class. It also does not assert existence of `w0` for every `w1`.

`BlockCanonicalLiftCompatibilityStatement F T B V` is precisely the
conjunction of these two clauses. Admissibility, compactness, the published
factorization and strict-contraction predicates, and, in the second clause,
subgroup inclusion and equality of quotient classes are all the mathematical
hypotheses. Core canonical-lift bijectivity, generalized-kernel equality,
stabilization, and these compatibility conclusions are not premises.

There are no positive-rank, nonempty-block, proper-parabolic, or nonzero-module
conditions. Rank zero, empty and one-block shapes, and the zero representation
are retained. The strict inequalities are vacuous when the block shape has
at most one block, as in the published predicate.

## Source and derived provenance

Bill Casselman, *Introduction to admissible representations of p-adic groups*,
Chapter III: *Induced representations and the Jacquet module*, revision
April 29, 2019, section 5, pages 6–7: the canonical complement following
Lemma III.5.4, Proposition III.5.5, and especially Lemma III.5.7. The operator
and factorization conventions occur in section 4 and III.5.1–III.5.3,
pages 5–6. Registered source `casselman-2019-jacquet-module`, SHA256
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.
Retained original:
`/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter III - Induced representations and the Jacquet module--2019.pdf`.
The original pages 5–7 were read; no separate project errata file was found.
The page 7 correction retracts an earlier argument over general Noetherian
coefficient rings. These targets use the field `ℂ`.

The first clause is an explicitly derived formulation of choice independence.
The source calls the sufficiently high power image a canonical complement,
but does not state two-tuple equality in the implemented all-power-submodule
syntax. An intended proof would combine commuting normalized compressed
chamber operators, finite-dimensional stabilization from admissibility, and
identification of their common generalized kernel with the Jacquet kernel.
These are proof dependencies to establish, not hypotheses of this statement
or results proved by this module.

Casselman's operator `τ_a` is an unnormalized coset sum. Its comparison with
the implemented normalized compression requires the positive finite
subgroup-index factor. A nonzero scalar factor preserves ranges and kernels
of corresponding powers; stabilization would then identify the implemented
intersection of all ranges with the source's sufficiently high power image.
This comparison is not silently asserted as an existing Lean theorem.

The second clause is a derived specialization of III.5.7, which explicitly
assumes `K1 ⊆ K0` and representatives with the same Jacquet image and averages
the first over `K0` to obtain the second. Using independent tuples requires
the choice independence expressed in the first clause, in addition to the
operator translation just described. The ambient quotient comparison requires
no identification between normalized and unnormalized Levi actions.

No proof of these clauses, normalized-Jacquet conversion, pairing construction,
nondegeneracy, or duality is included. The previously published core
canonical-lift statement supplies separate proof targets; it is not imported
or used as theorem evidence or a premise here.
