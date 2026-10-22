# Restriction and finite-index induction of complex Weil representations

Worker 25 states five related proposition definitions, conjoined in
`Langlands.Weil.RepresentationRestrictionInduction`. Each uses actual Mathlib
representations, carriers, and invertible linear intertwiners. None is an
assumption or a supplied proof. The group and carrier universes are independent.

## Actual induction and reciprocity

`Representation.IndV H.subtype ρ` is the quotient of
`ℂ[G] ⊗[ℂ] V` by the diagonal `H`-coinvariant relations. Mathlib's
`Representation.ind` equips that quotient with the actual `G` action:
`g` sends `[x ⊗ v]` to `[x*g⁻¹ ⊗ v]`. These conventions produce the
usual induced representation. No new induction object, representation record,
or finite-dimensionality certificate is assumed.

`RepresentationInductionReciprocity` uses the generator inclusion
`IndV.mk H.subtype ρ 1`. For every `H`-intertwiner `f : V → U`, it asks
for a unique `G`-intertwiner out of the actual induced space whose composite
with that inclusion is `f`. On generators the resulting map sends
`[x ⊗ v]` to `σ(x⁻¹)(f(v))`. The inverse in this formula matches
Mathlib's right-translation induction convention. This is the explicit
universal form of Frobenius reciprocity, with no index or dimension
restriction; Mathlib's `Rep.indResHomEquiv` provides the underlying
existing construction. No claim of uniqueness of a merely abstract
equivalence of hom-spaces is substituted for this generator condition.

## Declaration and source map

| Proposition | Content and hypotheses | Source and derivation |
| --- | --- | --- |
| `RepresentationRestriction` | Restriction along a continuous group homomorphism with `J ≤ φ⁻¹(I)` preserves ordinary continuity, open inertia kernel, finite inertia/whole image, unramifiedness, and isomorphism; it commutes with sum, tensor and dual and pulls back determinants. | Tate section 2.1, printed pages 9–10/PDF18–19, uses restriction. The listed compatibilities are derived by composing the action homomorphism and, for open inertia kernels, the continuous subgroup map `J → I`. |
| `RepresentationInductionFiniteness` | For finite-index `H`, the actual induced carrier is finite-dimensional with rank `[G:H]*dim V`; finite whole image and semisimplicity are preserved and reflected. Restriction to a finite-index subgroup also preserves and reflects semisimplicity. | Tate section 2.1, page 10/PDF19, uses finite-index induction and restriction. The dimension, image and semisimplicity facts are explicitly derived general representation theory over `ℂ`, not additional claims attributed verbatim to Tate. |
| `RepresentationInductionTopology` | An open finite-index subgroup suffices for preservation/reflection of usual continuity. For normal `I`, open restricted kernels and finite inertia images are preserved/reflected. Unramifiedness is preserved/reflected only when additionally `I ≤ H`. | Tate section 2.1, pages 9–10/PDF18–19, and section 4.1.2(a), page 20/PDF29. The explicit open-subgroup and normal-inertia assumptions isolate the local structural hypotheses needed for these derived comparisons. |
| `RepresentationInductionReciprocity` | Unique intertwiner extending each supplied subgroup intertwiner along the actual generator map. | Tate section 2.1, page 10/PDF19, states the usual Frobenius reciprocity; Mathlib's actual induction and `Rep.indResHomEquiv` give the precise implementation convention. |
| `RepresentationInductionCompatibility` | Actual representation equivalences for sums, tensor projection, duals, isomorphism transport, character twisting and transitivity through a finite-index subgroup chain. | Tate section 2.1, page 10/PDF19, and section 2.3.1 and its proof, page 11/PDF20, use induction, transitivity and `Ind(ρ ⊗ Res χ) ≅ Ind(ρ) ⊗ χ`. The tensor and dual variants are the usual derived finite-index linear algebra. |

The finite-dimensionality of `IndV` is a conclusion in the finiteness target,
not a typeclass hypothesis. Ranks use `Module.finrank`, including rank zero.
The finite-index assumption is explicit, so the natural-valued subgroup index
is not being used for an infinite-index subgroup.

Semisimplicity means that every invariant subspace has an invariant
complement. For the finite-index assertions, one can pass to the normal
finite-index core, apply the finite-dimensional Clifford argument to
restrictions, and average a projection over the finite quotient in
characteristic zero. The identity coset is a subgroup-stable summand of
the restricted induced representation, which gives reflection for induction.
No irreducibility assertion for restriction or induction is made.

Continuity always uses the usual finite-dimensional complex endomorphism
topology, expressed by `moduleTopology ℂ (Module.End ℂ V)`. In the topology
target it is also put on the actual induced endomorphism space; the separate
finiteness target establishes that this is finite-dimensional. An open
finite-index subgroup gives a finite coset model with continuous operator
entries, and the identity-coset inclusion gives the reverse implication.

The inertia subgroup is explicitly normal for induction. On a finite set of
coset representatives, its action uses a finite permutation and conjugates
of `I ∩ H`; normality makes these conjugates compatible with that same
restricted inertia action. This yields the finite-image comparison and,
with `H` open, the open-kernel comparison. The additional `I ≤ H` clause
for unramifiedness prevents the false assertion that induction from any
unramified representation is unramified: inertia can otherwise permute
the cosets nontrivially.

## Dependency and specialization boundary

Tate, *Number theoretic background*, Corvallis Part II (1979):

- Section 2.1, printed pages 9–10, PDF18–19.
- Section 2.3.1 and its proof, printed page 11, PDF20.
- Section 4.1.2(a), printed page 20, PDF29.
- Literature ID `tate-1979-number-theoretic-background`.
- Retained `Part II.pdf` SHA-256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.

The only project definition import is the exact published scalar twist:
artifact `c83db975-8b79-4fbb-9901-2db836910a0a`, version 1,
published commit `3d5d019e3d023c64c9a71be49c55e1d2e47b5f41`;
Lean SHA-256
`9e193a22784cba92e727402aac5117056433e796e37e1c76f8710e2ddd11d8cf`.
Its existing pullback-twist identity is reused, not redefined or resubmitted.
All induction and restriction objects are the pinned Mathlib definitions in
`RepresentationTheory/Induced.lean`, `Coinduced.lean`,
`FiniteIndex.lean`, and `Basic.lean`. Environment artifact
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1, pins Lean 4.34.0
and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.

The construction companion's `FiniteRepresentation.representation` exposes
exactly the Mathlib actions used here. Its finite-dimensional induction
construction can therefore use these target conclusions about `IndV`
without introducing another induction notion. This pair is independent
of unpublished companion code.

To specialize to `W_E ⊂ W_F`, the arithmetic construction must supply the
actual Weil groups, their continuous open finite-index inclusion, the
index `[E:F]`, and the inertia identification
`I_E = I_F ∩ W_E` with the inherited topology. These statements do not assume
that an arbitrary group/subgroup is such a local pair. They do not define
WD monodromy on an induced space, or assert arithmetic L/epsilon/gamma
identities or a Langlands correspondence.
