# The actual irreducible generic socle of a Whittaker coefficient model

Author: Worker 654.

`Langlands.Whittaker.ModelGenericSocleStatement.{uF,uV}` is a closed
Prop-valued definition. It states the representation-theoretic minimal-subspace
assertion used in JPSS Section 5.4. This module supplies a statement for a later
proof; it proves neither the existence of the subspace nor the JPSS analytic
results.

## Quantifiers and hypotheses

For every prime `p` and every `F : PadicField.{uF} p`, the proposition installs
`F.canonicalTopologicalData.topology`. It then quantifies over every bundled
`HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier` named `ψ`, every natural
number `n`, every `V : Type uV` with an additive commutative group and complex
module structure, and every actual representation
`σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V`.
The field and carrier universes `uF` and `uV` are independent. No topology is
placed on `V`. The group has rank `n + 1`, including rank one when `n = 0`.
The bundled character supplies nontriviality, continuity and unitarity.

The representation hypothesis is exactly the published
`RankinSelberg.IsOfWhittakerType n (Whittaker.standardCharacter ψ n) σ`.
Unfolding that definition gives all three conditions:

1. `Langlands.IsAdmissible σ`: smoothness and finite-dimensional complex
   fixed-vector spaces for every open subgroup, expressed by `Module.Finite`.
2. Finite generation of `σ.asModule` over the actual complex group algebra
   `MonoidAlgebra ℂ (Langlands.GeneralLinear (n + 1) F.Carrier)`.
3. `Nonempty ((Whittaker.glFunctionals ψ n σ) ≃ₗ[ℂ] ℂ)`, a linear
   equivalence of the entire character-equivariant functional space with `ℂ`.

Thus finite type means generation under the group algebra, not finite dimension
of `V`. The last condition is stronger than merely selecting a nonzero
functional or a one-dimensional subspace of functionals. It also excludes the
zero representation. There is no irreducibility hypothesis on `σ`.

For every `ℓ : Whittaker.glFunctionals ψ n σ` with `ℓ.val ≠ 0`, put
`M := Whittaker.glModelRepresentation ψ n σ ℓ`. This is the published
right-translation representation on the actual image of the coefficient map
`v ↦ (g ↦ ℓ.val (σ g v))`, with values on the actual general linear group.
The published `Whittaker.modelMap` is surjective onto this image. Its kernel
need not vanish for reducible `σ`; `Whittaker.glModelEquiv` requires
irreducibility and is not used here.

## Conclusion and actual subobject uniqueness

The conclusion asserts existence of `S : Subrepresentation M` with exactly
these four explicit clauses:

1. `S ≠ ⊥`.
2. `Representation.IsIrreducible S.toRepresentation`.
3. For every actual `T : Subrepresentation M`, `T ≠ ⊥` implies `S ≤ T`.
4. `RankinSelberg.IsOfWhittakerType n (Whittaker.standardCharacter ψ n)
   S.toRepresentation`.

Here `S.toRepresentation` is the inherited action on `S.toSubmodule`. The
Lean definition explicitly installs the canonical inherited additive group on
the coefficient image to guide type inference; this adds no hypothesis or data.
The relation `≤` is ordinary inclusion of the invariant subspaces of `M`. In particular, the
fourth clause includes smooth admissibility, group-algebra finite generation,
and a linear equivalence of the whole functional space of the inherited action
with `ℂ`; the weaker `Whittaker.IsGeneric` predicate does not replace it.

If `S` and `S'` both satisfy these clauses, the third clause applied to each
nonzero subspace gives `S ≤ S'` and `S' ≤ S`, hence `S = S'`. More generally,
any nonzero irreducible subrepresentation of `M` equals `S`, since it contains
`S`. This identifies an actual least nonzero invariant subspace, and therefore
the irreducible socle, rather than only an isomorphism class of constituents.
A separate uniqueness conjunct is unnecessary.

A unique graded generic factor in a supplied finite filtration specifies a
position and quotient in that filtration. It does not alone supply an invariant
subspace of the ambient model. In particular, the published
`Langlands.Whittaker.existsUnique_hasFunctional_factor` does not by
itself provide this statement's `S` or its containment in every nonzero `T`.
No filtration, finite-length witness, full-type assumption on `M`, socle witness
or functional-exactness hypothesis is added to this closed proposition.

## Original source and scope of the extraction

The registered original is H. Jacquet, I. I. Piatetski-Shapiro and J. A.
Shalika, *Rankin–Selberg Convolutions*, American Journal of Mathematics 105
(1983), 367–464, literature ID `jpss-1983-rankin-selberg`. The retained scan is
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Printed pages 385–386 and 420–423 (one-based PDF pages 20–21 and 55–58) were
read visually for this contribution.

Section 2.1, printed page 385, defines Whittaker type by admissibility, finite
type and dimension one of the full equivariant functional space. It recalls
exactness of the functional functor and explicitly includes rank one. Equation
(3) on printed page 386 constructs the coefficient functions; its following
paragraph identifies the right-translation model as a quotient of the original
representation, with equivalence to the original only under irreducibility.
Because the functional space is one-dimensional, any specified nonzero `ℓ`
generates the same model as the source's use of all functionals: every other
functional is a scalar multiple, absorbed into the input vector.

Section 5.2, printed page 420, works on this coefficient model. The first
paragraph of Section 5.4 on printed page 423 explicitly allows its action to be
reducible, invokes exactness to obtain its unique minimal invariant subspace,
and identifies the corresponding representation as generic because it is
realized inside the Whittaker model. This is the source of the actual-subspace
assertion here. The source paragraph occurs in an argument with an induced
`σ`; this module extracts the structural assertion uniformly for representations
satisfying the Section 2.1 hypotheses, without retaining induction data. The
full-type clause spells out the one-dimensional functional condition as well
as admissibility and finite type, rather than treating a generic constituent
label as sufficient.

Admissibility retains smoothness and finite-dimensional invariant spaces.
Together with group-algebra finite generation in this local general linear
setting, it is the finite-length input needed to find irreducible subobjects;
finite length is to be derived in the later proof, not assumed here. The
functional dimension-one condition and exactness then control how nonzero
subobjects can coexist. The coefficient-image realization is essential: a
nonzero function has a nonzero value, which a right translate moves to the
identity, so each nonzero invariant subspace has a nonzero evaluation
functional. A proof must establish the required inheritance, exactness and
containment from the stated hypotheses. This explanation records the source's
structural reasoning and the future obligations, not a formal proof in this
module.

The source is over non-Archimedean local fields; this statement is its p-adic
specialization through the existing `PadicField` API, for every prime and every
finite extension it represents. No source-specific registered JPSS erratum was
found in the current project literature index or in the project and Library
`notes/errata` locations checked for this contribution. This is a bounded
registry check, not a claim that no erratum exists anywhere.

The later occurrence of this generic socle as a constituent of the induction of
the generic block socles is a separate assertion. This module includes no gamma
identity, functional equation, Fourier transform, measure, multiplicativity,
induction-irreducibility or classification statement. It imports the existing
`RankinSelberg.AnalyticStatement` for the full Whittaker-type and actual-model
interfaces and leaves all existing Library pairs unchanged.
