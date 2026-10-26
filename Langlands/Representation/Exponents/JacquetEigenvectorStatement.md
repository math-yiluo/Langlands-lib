# Ordinary eigenvectors for generalized normalized Jacquet exponents

Author: Worker 508. The telescope and extraction route are adapted from
Worker 322's coefficient-extraction statement and Worker 314's task specification.

`Langlands.GLJacquetExponentEigenvectorStatement.{uF,uV}` is a transparent,
closed Prop-valued definition. It isolates the pure-vector step in the
coefficient-extraction argument. This module states that step and supplies
no proof of eigenvector extraction or coefficient extraction.

## Exact statement and conventions

The telescope agrees with
`Langlands.GLJacquetExponentCoefficientExtractionStatement`: every prime
`p`, finite p-adic field `F : PadicField.{uF} p`, supplied
`T : F.TopologicalData`, positive rank `n`, and complex module
`V : Type uV` are quantified. The field and carrier universes are independent.
The local instance `letI := T.topology` makes admissibility use the supplied
topology, as does the existing exponent predicate.

For every actual representation `ρ` of `GL_n(F)` satisfying
`IsAdmissible ρ`, every ordered standard block shape `B`, and every character
`χ : (Fin B.length → F.Carrierˣ) →* ℂˣ` satisfying
`T.IsJacquetExponent B ρ χ`, the conclusion is

```lean
∃ w : B.JacquetModule ρ, w ≠ 0 ∧
  ∀ a : Fin B.length → F.Carrierˣ,
    T.splitCentreJacquet B ρ a w = (χ a : ℂ) • w
```

One vector is chosen before every block-scalar tuple `a`. The equation holds
on the entire split centre, including unrestricted common scalar directions
and every tuple in the one-block case. There is no chamber condition.
The character in the conclusion is exactly `χ`.

The imported `Langlands.Representation.Exponents.Jacquet` supplies the actual
upper Jacquet quotient `B.JacquetModule ρ` and the action
`T.splitCentreJacquet B ρ`, which restricts `T.normalizedJacquet B ρ` along
`B.blockScalarLevi F.Carrier`. Its normalization on quotient classes is
`a · [v] = δ_P(a)^(-1/2) [ρ(a)v]`, as recorded by
`splitCentreJacquet_mk`. The statement introduces no replacement carrier.

`T.IsJacquetExponent` asserts that `χ` has open kernel and that some nonzero
vector is killed by one uniform power of every shifted split-centre
operator. That generalized-character witness is the premise; an ordinary
eigenvector is the conclusion. No finite length, irreducibility, scalar
central character, finite-dimensional ambient carrier, chosen invariant
space, or pairing is assumed. Zero carriers are allowed: their Jacquet
module has no nonzero generalized-character witness.

## Original source and derived provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques,
d'après Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333:

- §I.2, pp.242–243, treats finite-dimensional translation-invariant spaces
  of functions on the split centre. Pure characters occurring in their
  exponential-polynomial expansions belong to those spaces.
- §I.3, p.243, defines generalized exponents of admissible representations
  and describes the admissible Jacquet representation with inverse-half
  normalization.
- Theorem I.4.1, p.245, gives the nondegenerate canonical Jacquet pairing
  and its chamber coefficient identity.
- The first paragraph of the proof of Proposition III.2.2, p.266, invokes
  I.2 and I.4.1 to extract a pure-character coefficient. Temperedness is
  used in the ensuing growth estimate.

Registered source: `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
The retained original is
`/home/taskhub/central-library/Waldspurger--La formule de Plancherel pour les groupes p-adiques d'apres Harish-Chandra--2003.pdf`;
one-based PDF page equals printed page minus 234. The cited pages were read
in text and checked in page images. No source-specific project errata entry
was found: neither the supplied public notes nor the current Library notes
contained an `errata` directory when checked.

The present proposition is a derived representation-vector formulation of
the pure-character step behind this argument. Waldspurger I.2 concerns
function spaces; it does not state this Lean proposition verbatim.
The derivation requires the following separate proof.

Start with a nonzero generalized-character witness `v` and its uniform
power `k`. Admissibility of the normalized Jacquet representation includes
smoothness, so an open Levi subgroup `K` fixes `v`. Centrality of
`B.blockScalarLevi`, proved by `blockScalarLevi_mem_center`, implies that
the entire split-centre orbit of `v` stays in the `K`-fixed space. Jacquet
admissibility makes this fixed space finite-dimensional.

The span of that orbit is a nonzero finite-dimensional split-centre
invariant subspace. The split-centre operators commute, so every orbit
vector, and hence its span, satisfies the same generalized-character
equations with power `k`. A future proof must extract a common eigenvector
from this subspace. If its eigencharacter is `λ`, then the generalized
equations give `(λ(a) - χ(a))^k w = 0` for every `a`. The witness forces
`k > 0`, and `w ≠ 0` over `ℂ` forces `λ(a) = χ(a)` for every `a`.
This explains why the required eigencharacter is the same `χ`.
Only the fixed space and its orbit span are finite-dimensional; the whole
Jacquet module need not be.

The existing theorem `Langlands.Parabolic.normalizedJacquetAdmissibility`
in `Langlands.Representation.Parabolic.NormalizedJacquetAdmissibilityProof`
proves admissibility for the inverse-half twist of
`Parabolic.leviCoinvariants`. Applying it to the action in this statement
requires checking the actual comparison with `T.normalizedJacquet B ρ`;
the future proof must not assume those presentations are definitionally
equal. The existing `B.jacquetModuleEquiv` and
`Parabolic.jacquetModuleEquiv_leviCoinvariants` provide comparison data.
This module does not implement that comparison or the finite-dimensional
common-eigenvector argument.

Canonical pairing, opposite smooth duality, rescaling a detected vector,
lifting quotient representatives, and transporting the pairing identity to
the full deep chamber belong to the separate coefficient-extraction proof.
They are outside this pure-vector statement. The proposition alone proves
none of those steps, temperedness, or any classification result.
