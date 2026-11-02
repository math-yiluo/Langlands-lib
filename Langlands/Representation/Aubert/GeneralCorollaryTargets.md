# General targets for Aubert Corollary 1.10

Author: Worker 1186. The actual parabolic functors and K0 operator are the
constructions of Worker 23; the actual Weyl quotient and intrinsic Coxeter
indexing are reused from Worker 165.

This module declares propositions in `Langlands.Aubert.General`. It proves
neither corollary assertion nor any of the representation-theoretic
prerequisites below. It is an intermediate target family over actual
subgroups. Specialization to rational points, the structural realization of
the standard families and discharge of every representation-theoretic
premise remain obligations of the general Aubert parent
`46df6a68-5db4-4428-8044-05151d6ce1f6`.


The imported `General/Parabolic` and `General/AlternatingOperator` pairs
are the unmodified, unreviewed Worker 23 adapter draft revision 1 from task
`593ef603-6672-4424-976c-14e11e920d9c`. They are included only as validation
dependencies and are excluded from this target pair's publication paths.
Their independent acceptance and publication must precede integration of
this pair; review of these targets does not accept the adapters.

## Parameters and normalization

The ambient `G : Type uG` is a locally compact nonarchimedean topological
group. `ι` labels the finite set `S` of relative simple roots. `P I`, `M I`
and `U I` are actual subgroups of `G`, with
`h I : IsSemidirectDecomposition (P I) (M I) (U I)` and closed `U I`.
The normalization is precisely that of
`General/Parabolic`: induction uses the positive half Haar modulus and
Jacquet restriction the inverse half modulus on actual coinvariants.

The operator and maps are `alternatingOperator`, `inductionK0` and
`jacquetK0` of `General/AlternatingOperator`, on
`SmoothRep.FiniteLengthGrothendieckGroup.{0,uG,max uG uV} ℂ G`.
The named assumption `ParabolicFiniteLength` separately supplies induction
and Jacquet finite-length preservation and exactness on finite-length short
exact sequences. These are representation-theoretic premises, with owner
task `593ef603-6672-4424-976c-14e11e920d9c` (Workers 23 and 1180).
They are not external Chapter V structural assertions.

`hM J` makes the actual Levi `M J` closed. `hLevi J I` gives the restricted
semidirect decomposition inside `M J`, using literal `subgroupOf` subgroups.
`IsCorollaryLeviCuspidal` says that the normalized Jacquet module for each proper
subset of `J` is a zero object in the smooth category of its actual
restricted Levi. No class-level vanishing is substituted for this
object-level condition.

No field, characteristic, splitness or quasi-splitness restriction is
introduced by these generic definitions. To obtain the source theorem, the
parameters must be realized for rational points of a connected reductive
group over a nonarchimedean local field, with the generality of Aubert's
introduction. The generic target is not asserted for arbitrary unrelated
subgroup families. In particular one still needs `M ∅ = Z_G(T0)`,
`M univ = G`, standard-family compatibility and the rank comparisons
`|J| = dim(A0) - dim(A_(M J))` and
`|S| - |J| = dim(A_(M J)) - dim(A_G)`.

## Source-to-declaration table

All names in this table are in `Langlands.Aubert.General`.

| Declaration | Exact content and source | Remaining proof input and owner |
| --- | --- | --- |
| `HasTwoConstituents` | Internal expression of a length-two composition series: two irreducible actual smooth representations and an actual short exact sequence in either order. | It asserts neither existence nor splitting. Exact K0 additivity is the published `SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation_shortExact`. |
| `IsMaximalStandard` | `J = univ.erase α` for a simple root `α`, as in Corollary 1.10(b), printed p.2183. | Identifying this with relative semisimple corank one uses the structural rank comparisons. No such `J` exists when `S` is empty. |
| `IsCorollaryLeviCuspidal` | Every proper standard normalized Jacquet module within `M J` is a zero object, matching Aubert's cuspidality definition on p.2181 applied to the Levi. | Standard-family realization and Levi-in-Levi subgroup transport; admissibility and other representation properties are not built into this definition. |
| `corollary110a` | Corollary 1.10(a): for an irreducible cuspidal finite-length `σ` of `M J`, if the actual normalized induction `i_J σ` is irreducible, then `D_G[i_J σ] = (-1)^|J| [i_J σ]`. | Theorem 1.7 induction compatibility and the Levi cuspidal eigenvalue, owned by Worker 165's main-target unit and subsequent parent proof tasks. The source irreducibility hypothesis is retained even though the formal eigenvalue follows more generally from those identities. |
| `ConstituentExchange` | Both equations `(-1)^|J| D_G[ρplus] = [ρminus]` and `(-1)^|J| D_G[ρminus] = [ρplus]`, using the unadjusted operator. | This is the conclusion predicate, not a law assumed about the operator. |
| `rankOneLengthTwo` | Reducibility of the actual induction of irreducible cuspidal `σ` from a maximal standard Levi implies an actual length-two composition series. Aubert p.2183 cites Casselman §7.1; Casselman Corollary 7.1.2, printed p.67, gives length at most two. | Nonzero induction, finite length, composition factors and the source admissibility/general reductive hypotheses must be proved in the representation-theory layer. The parent owns the focused proof successor, coordinated with Renard owners. |
| `rankOneSelfAssociation` | In the same reducible maximal-Levi situation, `associatedSubset actual J = J`, and every lift of the specified `longestRep actual J` normalizes `M J`. | Casselman Theorem 7.1.4, pp.67–68, proves irreducibility in the non-self-dual case. Converting its contrapositive to the actual Coxeter/standard-Levi formulation also needs the structural associated-Levi comparison. This deduction is representation theory, not an extra Chapter V field. |
| `RankOneJacquetPattern` | The actual modules satisfy `r_J ρplus ≅ σ`, `r_J ρminus ≅ Ad(n⁻¹) σ`, and `r_K ρplus = r_K ρminus = 0` for every proper `K ≠ J`, exactly as used on Aubert p.2183. | Uses the actual `conjugationFunctor` and normalized `jacquetFunctor`; this predicate alone asserts no existence. |
| `rankOneJacquetModules` | In the reducible maximal-Levi situation, for every specified longest lift `n` and a proof that it normalizes the actual Levi, there are two irreducible composition factors with `RankOneJacquetPattern`. | The self-association proof supplies the domain of `Ad(n⁻¹)`. The geometric lemma, exactness, cuspidal-support detection, length two and Casselman §7.1 are representation-theoretic obligations. No GL tempered-induction irreducibility is used. |
| `corollary110b` | Corollary 1.10(b) at source scope: reducible induction of irreducible cuspidal `σ` from `J = S \ {α}` has two irreducible composition factors exchanged by `(-1)^|J| D_G`. Both the actual length-two series and the two class equations occur in the conclusion. | Assemble the separately named prerequisites, the actual top term, exact K0 additivity and `inducedK0WeylConjugacy` from `GeneralWeylConjugacyTarget`. The parent owns proof closure. |

The finite-length witnesses in the quantified objects are existing
properties, not manufactured witnesses. Irreducibility is the published
`SmoothRep.IsIrreducible`. A proof of the source result can obtain finite
length of an irreducible from the existing
`SmoothRep.hasFiniteLength_of_isIrreducible`; the induction hypotheses still
have to be supplied.

## Conjugation and sign

`actual` is a Coxeter system on the actual quotient
`RelativeWeyl.Weyl T = N_G(T)/Z_G(T)`. The longest element is the constructed
maximum in `D(J,∅)`, and the associated subset is the inverse-longest image.
The identification with actual positive relative roots remains an explicit
realization obligation.

In `RankOneJacquetPattern`, `hself` states
`x ∈ M J ↔ n*x*n⁻¹ ∈ M J`.
The adapter's `conjugationFunctor g` pulls back along `x ↦ g⁻¹*x*g`;
therefore the argument `g = n⁻¹` gives precisely
`Ad(n⁻¹) σ`, with action `σ(n*x*n⁻¹)`. There is no reversal of the
source's conjugation convention. `rankOneJacquetModules` quantifies every
actual lift with the required quotient class.

The exchange sign is `(-1)^|J|`. It is not `(-1)^|S|`, since maximality
gives `|S| = |J| + 1` in the proof's top term.
Part (a) includes `J = ∅` and the empty simple-root type. Part (b) is
vacuous when there are no simple roots. No rank-positive premise was added
to the operator.

## Sources and proof boundary

- Registered `aubert-1995-duality`, printed pp.2179–2183, especially the
  definition of cuspidality on p.2181 and Corollary 1.10 and its proof on
  p.2183. The original p.2183 was also read visually for both signs and
  `Ad(w_J⁻¹)`.
- Registered `casselman-1995-admissible-representations`, draft 1 May 1995,
  introduction p.2 and §7.1 pp.67–68: Lemma 7.1.1, Corollary 7.1.2 and
  Theorem 7.1.4. This module records the required deductions as targets; it
  does not claim a completed general proof from Casselman.

The generic predicates and actual exact-sequence formulation are internal
encodings of those source assertions. No new source theorem is claimed.
The unproved induced-K0 Weyl-conjugacy input is outside the external
structural boundary; its planned classification dependence is documented
in `GeneralWeylConjugacyTarget.md`. Proposition 3.2 is not used.
