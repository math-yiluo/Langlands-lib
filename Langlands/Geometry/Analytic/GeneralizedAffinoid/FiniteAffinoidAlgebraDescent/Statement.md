# Effective finite Banach algebra descent on arbitrary finite full-domain covers

`Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescentStatement`
is an unproved proposition definition. It is an effectiveness interface, not an
axiom or a proof of descent.

For every complete ultrametric normed field `K`, every actual presented
positive-polyradius affinoid algebra `R`, and every actual finite full-domain
cover of `Domain.whole K R`, the proposition takes the following ordinary local
data. Over each original cover algebra there is an actual bounded structural
map to a presented affinoid algebra satisfying `IsFiniteBanach`. On each
literal intersection there is a bounded equivalence of the two actual
closed-quotient base changes, preserving the entire intersection coefficient
algebra. The equivalences satisfy identity and the triple-overlap cocycle as
equalities of entire bounded maps. Further restrictions used in that cocycle
are constructed by the bounded pushout universal property; no further
equivalences, naturality axioms, or effective descent hypotheses are inputs.

The conclusion is the existence of an `EffectiveRealization` of those exact
data. Its fields specify:

- An actual `PresentedAffinoidAlgebra` and a bounded algebra equivalence, with
  bounded inverse, to the already constructed complete matching algebra. This
  matching algebra is the closed subalgebra of the maximum-norm finite product
  defined by the entire overlap equations.
- `IsFiniteBanach` for the constructed structural map from the original `R`
  into the matching algebra and for its transport into the presented
  realization. Thus a finite coefficient map has lifts bounded by one uniform
  positive constant times the target norm.
- A bounded equivalence from the actual closed-quotient base change of that
  global map along each original stored `R → R_i` restriction to the original
  local algebra. Its entire forward map equals the constructed comparison.
  The comparison's two leg formulas recover both the global matching
  projection and the original local structural map.
- Equality of the entire induced comparison maps over each original literal
  intersection, through the original supplied bounded transition equivalence.
- A homeomorphism from the actual topological quotient gluing of the original
  local spectra along their actual overlap spectra to the entire spectrum of
  the descended presented algebra. It equals the canonical continuous map
  constructed from the matching projections. Each original local spectrum is
  also homeomorphic, by its canonical projection-induced map, to the actual
  inverse image of its original base-domain locus.

All input and output maps are actual maps of the supplied quotient algebras.
The two lemmas identifying the overlap restrictions with
`Domain.interLeft` and `Domain.interRight` retain the original closed-quotient
intersection maps. The result does not replace whole-map compatibility by
agreement on spectrum points and does not assume spectral injectivity of any
finite local map.

The scope includes arbitrary positive polyradii and trivially valued fields.
There is no strict-radius, nontrivial-valuation, extra admissibility, global
analytic Hausdorffness, rational-cover, or pre-supplied affinoid-realization
premise. The base is an actual presented affinoid; the cover is any supplied
finite full-domain cover. Nonreduced and zero quotients, empty spectra, and
empty finite covers are included.

The source is Berkovich, *Étale cohomology for non-Archimedean analytic spaces*
(1993), Kiehl's Theorem and Remark 1.2.1(ii), printed p.15 / PDF p.12.
That theorem gives effective finite-module descent on finite affinoid covers
and identifies its global object with the section equalizer. The source
explicitly extends the theorem to general affinoids and trivial valuations
using Berkovich 1990, §2.1. Lemma 1.2.12, printed p.20 / PDF p.17, applies
this to compatible finite algebras and obtains a finite affinoid equalizer
with the desired spectrum. Registered source:
`berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.

The explicit Banach convention follows Berkovich, *Spectral theory and analytic
geometry over non-Archimedean fields* (1990), §§2.1.9–2.1.12, printed
pp.24–25 / PDF pp.38–39. Registered source:
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.
In particular, the warning after §2.1.9 rules out upgrading algebraic finiteness
with arbitrary supplied Banach norms over a trivially valued field.

The proposition is an explicit derived formulation of this effective
finite-algebra descent result, retaining the original norms, presentations,
closed-quotient maps, and quotient-spectrum comparison. A proof must establish
the bounded equalizer's norm-controlled finite-module descent, transfer the
algebra structure to an actual positive-polyradius affinoid presentation,
prove the exact bounded original base-change comparisons, and establish the
whole-spectrum and inverse-image homeomorphisms. The imported elementary
equalizer and quotient constructions alone do not establish these claims.
