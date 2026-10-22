# Segment products and generic multisegments

Author: Worker 118.

This module states Zelevinsky's segment-product irreducibility and generic
classification results as proposition definitions. It proves none of the
classification assertions. All representations, segment classes, induction
functors, constituent relations, characters and functionals are the actual
published Library constructions.

## Conventions and domains

Let `F : PadicField p` be an actual finite extension of the p-adic field, with
`Fact p.Prime`, and let `T : F.TopologicalData` be any compatible topological
realization. Coefficients are the actual complex numbers. The group is
`GeneralLinear (n + 1) F.Carrier`, for arbitrary natural `n`: every positive
finite rank, including rank one, is covered. Rank zero is outside this unit
because the published standard Whittaker character uses positive rank.
There is no finite-dimensionality assumption on the representation carrier.

Write `ν = |det|`, using the residue-normalized absolute value
`|varpi| = q^(-1)`. The product in `SegmentProductDatum.induced` is the actual
`normalizedProductInductionFunctor` for the upper block parabolic, acting by
right translation and with covariance factor `δ_P^(1/2)`. For a segment
`Δ = [ρ, ν^(m-1)ρ]`, `HasSegmentSocles` uses the unique irreducible subobject of
the increasing product, Ze80's `⟨Δ⟩` in §3.1. `HasSegmentHeads` uses its unique
irreducible quotient object, Ze80's special representation `⟨Δ⟩^t` in §9.1.
Both are relations on supplied representations, not constructors with assumed
existence. The imported `SegmentConstituentStatement` already states their
existence and uniqueness; this unit does not restate or assume those results.

Every product datum includes an actual finite segment family, the degree sum
equal to the ambient rank, and actual smooth block representations. Product
criteria impose no precedence ordering. `multisegment.IsUnlinked` says that no
two members are linked, using the published support-union/noncontainment
definition from Ze80 §4.1. A segment is never linked to itself, so this condition
permits repetitions. Multiset equality retains those repetitions.

Each `ψ : UnitaryAdditiveCharacter F.Carrier` is a continuous, nontrivial
unit-circle-valued additive character. It is quantified, not chosen. The
standard character on the actual upper-unipotent subgroup is
`u ↦ ψ(∑ i, u[i,i+1])`. `Whittaker.HasFunctional` means that there exists a
nonzero complex-linear functional `ℓ` satisfying
`ℓ(π(u)v) = ψ(∑ i, u[i,i+1]) * ℓ(v)`. There is no topology on the carrier
or continuity assumption on `ℓ`. In rank one the unipotent group and its
character are trivial, as established by the imported construction.

`Whittaker.IsGeneric` additionally requires irreducibility and admissibility.
Consequently arbitrary, possibly reducible special-head products satisfy
only the nonzero-functional assertion; the generic assertion for those products
is equivalent to nonlinkage. The admissibility in this reformulation is
supported by BZ77 Theorem 2.5, not by an extra assumption on the product.

Universes `uF` and `uV` are independent. In the local product criteria
and the `Z(a)` criterion, supercuspidal bases have carriers in
`Type uV`, and segment constituents and induced products have carriers in
`Type (max uF uV)`, as required by the published induction construction.
For exhaustion and its unordered uniqueness clause, both the representations
being classified and supercuspidal
bases have carriers in `Type (max uF uV)`; induction remains in that universe.
Thus exhaustion does not require a representation in a larger universe to
have supercuspidal support represented in a smaller one. No resizing theorem
or unproved choice of a classification representative is used.

## Declaration and source correspondence

All declarations are in `Langlands.Classification`.

| Declaration | Actual assertion | Original source |
| --- | --- | --- |
| `SegmentSocleProductIrreducibility` | For any datum with segment socles, its induced representation is irreducible iff its multisegment is unlinked. | Ze80 Theorem 4.2, p.184. |
| `SegmentHeadProductNondegeneracy` | For every allowed `ψ`, every product of special heads has an actual nonzero standard Whittaker functional, without an irreducibility hypothesis. | Ze80 Theorem 9.7(a), p.199; §9.8. |
| `SegmentHeadProductIrreducibility` | A product of special heads is irreducible iff its segments are pairwise nonlinked. | Ze80 Theorem 9.7(a), pp.198–199; §§9.8–9.9. |
| `SegmentHeadProductGenericity` | For every allowed `ψ`, a product of special heads is generic iff its multisegment is unlinked. | Derived formulation of Ze80 9.7(a), with BZ77 Theorem 2.5 for admissibility. |
| `GenericSegmentProductExhaustion` | A smooth representation is generic iff it is genuinely isomorphic to an unlinked product of special heads. | Ze80 Theorem 9.7(b), p.199, and §9.10, p.201; the reverse implication uses 9.7(a). |
| `GenericSegmentProductUniqueness` | Two unlinked products of special heads are isomorphic iff their segment multisets are equal. | Ze80 Theorem 9.7(b) and §9.10. |
| `ZelevinskySocleGenericity` | If `π` satisfies `a.IsZelevinskySocle`, it is generic iff every member of `a` has length one. | Ze80 §9.10, first sentence, p.201, following Theorem 8.1, p.195. |
| `SegmentGenericTheorems` | Conjunction of the seven preceding clauses for `F,T`. | Internal packaging, with no additional mathematical assertion. |
| `PadicSegmentGenericTheorems` | The conjunction for every prime, p-adic field and compatible topological realization. | The preceding sources specialized to finite p-adic extensions. |

`Nonempty (π ≅ π')` uses actual categorical isomorphisms in `SmoothRep`, hence
invertible equivariant complex-linear maps. The reverse direction of uniqueness
includes independence of ordering and block representatives for these
irreducible special-head products. In §9.10 the product for the unlinked
multisegment is identified with the unique nondegenerate `⟨a(φ)⟩`, which gives
this direction as well as the uniqueness of the unordered multiset.

`a.IsZelevinskySocle π` means that some precedence-ordered enumeration of `a`,
with actual segment socles as blocks, has `π` as its unique irreducible socle.
Existence, enumeration independence and the full bijective classification for
this relation belong to the separate multisegment installment. Here the
criterion applies to any representation satisfying the existing relation.
Length one is deliberately not replaced by nonlinkage: singleton segments can
be linked, while a single segment of length greater than one is an unlinked
family whose `Z` constituent is not generic.

## Translation of nondegeneracy

Ze80 uses the top derivative to define nondegeneracy. BZ77 §4.7, p.455,
defines it by nonvanishing of the rank-th derivative; §3.5 and §4.3 define
the derivatives. BZ77 §1.8(b), p.444, constructs character localization as
the quotient by the span of `π(u)v - θ(u)v`. Composition in §1.9(c) identifies
the top derivative with localization at the standard nondegenerate unipotent
character; Ze80 §8.3, p.196, explicitly makes this identification in its
Whittaker discussion. A nonzero such complex quotient is equivalent to the
existence of a nonzero linear form annihilating these relations, exactly the
published `Whittaker.HasFunctional`. This explains the translation of the
source assertion without asserting a derivative construction or its comparison
theorem in this module. No multiplicity-one or dimension-one conclusion is
included.

## Published dependencies and remaining obligations

At authoring, the imported files are in Library commit
`9bcf0d658a507ac3b07db1ef643b50bd98c4bcff`. They are imported by Lean name:

- `Classification.LanglandsData`, with its imported `Classification.Segments`,
  `Tempered` and `ConstituentRelations`, supplies the actual product and
  multisegment relations and `normalizedProductInductionFunctor`.
- `Classification.SegmentConstituentStatement` supplies the already published
  segment constituent existence and uniqueness statement targets.
- `Whittaker.GeneralLinear`, with `Whittaker.Algebraic`,
  `HarmonicAnalysis.Basic` and `Group.GL.UpperUnipotent`, supplies actual allowed
  additive characters, the actual matrix subgroup, functionals and genericity.

The Lean dependency graph imports no draft or future multisegment statement.
Mathematical proofs remain obligations: the product criteria, nondegeneracy,
exhaustion, unordered uniqueness, the `Z(a)` criterion, admissibility, and the
comparison between derivatives and Whittaker functionals. The latter uses
character localization, transitivity and linear duality as described above.
The full multisegment theorem and segment-constituent statements are also
statement-level inputs until proved. No use is made of Ze80's duality conjecture
in §9.17, the omitted square-integrability converse in §9.3, or a stand-in
classification predicate. Whittaker uniqueness and JPSS theory remain outside
this unit.

## Retained originals and reading extent

- A. V. Zelevinsky, *Induced representations of reductive p-adic groups II.
  On irreducible representations of GL(n)*, Ann. Sci. ENS (4) 13 (1980),
  165–210. Registered source `zelevinsky-1980-induced-ii`, SHA-256
  `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
  Directly read printed pp.181–185 and 195–201 (PDF pp.18–22, 32–38),
  including Theorems 4.2, 8.1 and 9.7 and the full §9.10.
  Retained file:
  `/home/taskhub/central-library/Zelevinsky--Induced representations of reductive p-adic groups II, irreducible representations of GL(n)--1980.pdf`.
- I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
  p-adic groups I*, Ann. Sci. ENS (4) 10 (1977), 441–472.
  Registered source `bernstein-zelevinsky-1977-induced-i`, SHA-256
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
  Directly read §§1.8–1.9, 2.1–2.5, 3.5, 4.1–4.7 and the surrounding
  printed pp.444–448, 452–455 and 457–460. The relevant source assertions
  are localization and composition, admissibility, and nondegeneracy via the
  top derivative. Retained file:
  `/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.

No separate errata note for either source was present in the supplied public
notes. This is a statement contribution, not a new proof of the cited results.
