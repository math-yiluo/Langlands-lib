# Orbit scalars on actual normalized induction

This derived construction connects rational scalar descent to the canonical
normalized induction objects. The orbit is the full complex unramified twist
orbit of the inducing representation, pulled back through the specified
identification of the Levi with a rational-point group. The comparison maps
are induced by genuine equivalences of that representation. Generic
scalarity is obtained from irreducibility of the actual induced objects.

The original intertwining families, their rational continuation data, their
original comparison squares, a nonempty open locus of induced irreducibility,
and, for presentation existence, finiteness of the full twist stabilizer are
explicit premises. This module does not prove those premises for the standard
integral operators. They remain representation-theoretic proof obligations in
the standing Plancherel program.

## Source and provenance

The source is J.-L. Waldspurger, *La formule de Plancherel pour les groupes
p-adiques (d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333,
DOI 10.1017/S1474748003000082, registered as
`waldspurger-2003-plancherel`, with content SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

IV.1, printed pp.276–277 / PDF pp.42–43, defines the complex orbit using
isomorphism classes of twists, scalar rational functions by character
pullback, and the common compact carriers. Its naturality square uses the
maps on induced representations obtained from an isomorphism of the inducing
representations. The beginning of IV.3, printed p.285 / PDF p.51, uses generic
induced irreducibility and Schur's lemma to obtain the rational scalar of the
opposite-intertwiner composite.

The present declarations are internal derived support for those passages,
not a separately numbered source theorem. They combine the published compact
restriction, continuation, scalar extraction and invariant fraction
interfaces. Unlike a comparison between arbitrary compact linear maps, the
new comparison data records an equivalence of the inducing representation
and the maps it actually induces. The source takes admissible inducing
representations and its standard operators; this support construction only
requires the displayed smooth objects and hypotheses. It asserts no
analytic extension of the source's construction to all smooth objects.

## Pullback and the actual stabilizer

Let `e : H ≃ₜ* M` identify a topological group with a subgroup of `G`, and
let `ν` be a family of norm characters of `H`. The transported family on
`M` is `νM(i) = ν(i) ∘ e.symm`. The existing character homeomorphism sends
`χ` to `χM = χ ∘ e.symm`. Canonical `SmoothRep.pullback e A` has the same
carrier as `A` and action `h ↦ A(e h)`.

`baseTwistEquivOfPullback` converts a representation equivalence

\[
(e^*A)\otimes\tau\simeq e^*B
\]

into `A ⊗ χM(τ) ≃ B`. `pullbackBaseTwistEquiv` performs the converse
conversion. Both retain the given linear equivalence; the evaluation lemmas
are definitional. Their proofs verify the intertwining equation after
substitution through `e` and its inverse. The two inducing carrier universes
may differ.

`mem_smoothRepUnramifiedTwistStabilizer_pullback_iff` therefore identifies
membership in the full twist stabilizers under the character homeomorphism.
It uses actual categorical isomorphisms of smooth representations, not an
arbitrary equivalence relation. `stabilizerBaseTwistEquiv` chooses a genuine
Levi twisting equivalence from membership in the pullback stabilizer. This
choice supplies an equivalence, not any intertwiner naturality assertion.
These declarations require the displayed nonarchimedean-group instances.
The group, character-index and representation universes remain independent.

## Original comparison data on induced representations

Take two closed semidirect decompositions `P₀ = M U₀` and `P₁ = M U₁`
inside a locally compact nonarchimedean group `G`, and a canonical smooth
representation `A` of `M`. Write `Iᵢ(χ)` for the actual
`UnramifiedLeviInduction` object after character transport through `e`.
The original families are genuine `G`-intertwining maps

\[
J_{10}(\chi):I_0(\chi)\longrightarrow I_1(\chi),\qquad
J_{01}(\chi):I_1(\chi)\longrightarrow I_0(\chi)
\]

on their independently supplied regions `Ω₁₀` and `Ω₀₁`.

`InductionSelfBaseChangeData τ` contains one equivalence
`a : A ⊗ χM(τ) ≃ A`, together with separate nonempty ambient open
forward and reverse comparison regions. The forward region lies in
`Ω₁₀ ∩ (τ * ·)⁻¹ Ω₁₀`; the reverse region has the corresponding
containment for `Ω₀₁`. On them the data requires

\[
J_{10}(\chi) I_0(a_\chi)=I_1(a_\chi)J_{10}(\tau\chi),\qquad
J_{01}(\chi) I_1(a_\chi)=I_0(a_\chi)J_{01}(\tau\chi).
\]

Here `aχ` is the existing `transportedBaseTwistEquiv`, from the translated
inducing object at `τχ` to the object at `χ`, and each `Iᵢ(aχ)` is the
actual `inducedMap`. The structure requires these original squares; it does
not manufacture them from the existence of `a`. No intersection of the two
comparison regions, denominator restriction on them, or coherent group law
on the chosen equivalences is required.

For compact restriction, the inputs additionally include a compact open
subgroup `K`, the factorizations `G = P₀ K = P₁ K`, closedness of both
parabolics, continuity of the semidirect projections and norm characters,
and the two `IsUnimodularModulus` hypotheses. The definition
`InductionSelfBaseChangeData.toSelfBaseChangeData` uses
`compactInductionBaseChangeEquiv` for its source and target maps. Applying
`compactIntertwiningOperator_transportedBaseChange_iff` to each original
square gives exactly the fixed-carrier `SelfBaseChangeData` equations.
Thus these compact self-equivalences are tied to the same actual inducing
representation and its induced maps.

## Rational-point specialization and extracted scalar

Let `F` be a nonarchimedean local field in arbitrary characteristic, `L` a
connected reductive group scheme over `F`, and `H = L(F)`. The topology and
`NonarchimedeanGroup` instance on `H`, continuity `hp` of its rational
valuation-image projection, and continuity of every rational norm character
are supplied. Use the complete rational norm-character family `νL` and a
topological group equivalence `e : H ≃ₜ* M`. The orbit representation is
precisely `π = SmoothRep.pullback e A`.

The data `p` and `q` are independent `RationalOperatorContinuationData` for
the compact restrictions of `J₁₀` and `J₀₁`. Each has a single whole-operator
denominator and a polynomial numerator family. Nonempty ambient open
subsets `D₁₀ ⊆ Ω₁₀` and `D₀₁ ⊆ Ω₀₁` are retained for the construction
of the actual continued induced intertwiners. Their common regular region is

\[
R=p.\mathrm{regularRegion}\cap q.\mathrm{regularRegion}.
\]

It is nonempty and dense by the existing actual regular-function domain
results. Neither the two original domains nor their specified open subsets
are required to intersect.

For a compact vector `v` and complex linear functional `ℓ`, put

\[
f_C=\mathrm{continuedCompositeRationalScalar}(p,q,v,\ell).
\]

This is the fraction extracted from the actual compact composite,
corresponding on `R` to `ℓ((q_ext ∘ p_ext)(v))`. It lies in the concrete
`rationalUnramifiedFunctionField L hp hL`. It is not a freely chosen scalar.

`continuedInductionCompositeOrbitScalar_value` takes any invariant
presentation `r` of this exact fraction under the full stabilizer of `π`.
At each `χ ∈ R` with `r.denominator(χ) ≠ 0`, it identifies the orbit value
of `r` with `p.continuedCompositeScalar q v ℓ χ`. The proof applies the
existing comparison with `scalarCoefficientPresentation` of the continued
compact composite. This value comparison needs neither normalized
extraction, induced irreducibility, self-comparison data nor stabilizer
finiteness once `r` is supplied.

## Fixedness, presentation and the ambient equation

Assume `G` is separable and there is a nonempty ambient open `D` on which
the actual source induced representation `I₀(χ)` is irreducible. This is a
supplied generic irreducibility hypothesis, with no irreducibility premise
at the final evaluation parameter. The existing
`continuedInductionComposite_generic_scalar` applies the separable smooth
Schur theorem to the actual induced endomorphism and then restricts it to
the compact carrier. Density of `R` gives a nonempty open test region
`D ∩ R`; it is not necessary to require `D ⊆ R`.

Require a normalized extraction pair `ℓ(v) = 1`. For every element of the
full complex twist stabilizer of `π`, supply a nonempty witness of
`InductionSelfBaseChangeData` for these same two original families.
`continuedInductionCompositeRationalScalar_stabilizer_fixed` applies the
compact adapter to those witnesses and the existing subgroup fixedness
theorem. It proves

\[
\tau^*f_C=f_C
\]

for every stabilizer element, with translation convention
`τ*(b)(χ) = b(τχ)`. Fixedness is a conclusion, not a separate premise.
The normalized pair excludes a zero compact source carrier; its existence
is not asserted here.

`continuedInductionCompositeOrbitScalarPresentation` further assumes that
this full stabilizer is finite. It applies
`unramifiedTwistOrbitScalarPresentation_exists` to the proved fixedness and
chooses an invariant regular numerator and nonzero denominator presenting
`fC`. No invariant numerator or denominator is an input. The existing
finite-index central-image finiteness criteria remain available as separate
application routes; this definition does not prove finiteness.

Finally, `continuedInductionComposite_eq_orbitScalar` takes any such
presentation `r`, the normalized pair and the stated generic
irreducibility hypothesis. For every `χ ∈ R` where `r` is regular it proves

\[
J_{01}^{\mathrm{ext}}(\chi)J_{10}^{\mathrm{ext}}(\chi)
 = r([\pi\otimes\chi])\,\operatorname{id}_{I_0(\chi)}.
\]

This is equality of actual `Representation.IntertwiningMap` objects on the
ambient normalized induction, not only of compact coefficients. The proof
uses `continuedInductionComposite_eq_scalar` and replaces its coefficient
by the preceding regular orbit-value equality. This theorem does not need
self-comparison witnesses or finiteness once an invariant presentation is
supplied. It applies at reducible parameters in the common regular locus.

## Scope and remaining obligations

The chosen orbit regular region has the existing nonempty dense open
properties, continuity and agreement with other presentations on common
regular regions. It is not asserted maximal. Values are only defined where
the chosen invariant denominator is nonzero; the operator equation also
requires both operator denominators to be nonzero. There is no value
assignment at poles, assertion of density on the unitary locus, or
algebraic-variety quotient identification.

The ambient group and inducing-carrier universes remain independent of the
field universe; generic pullback additionally preserves independent group,
index and two carrier universes. There is no characteristic-zero, splitness,
quasisplitness or positive-rank restriction.

The original families have not been identified with the standard integral
intertwiners. Their convergence, continuation and original naturality, the
generic induced irreducibility hypothesis and full-stabilizer finiteness
must still be discharged in the intended source setting. Nor is an
opposite-parabolic relation between `P₀` and `P₁` assumed or constructed.
Parabolic independence, nonvanishing and positivity, globally normalized
`j` and `mu`, compatible measures and the main Plancherel conclusions
remain separate obligations. None of the supplied representation-theoretic
or analytic premises becomes an allowed external structural hypothesis for
completion of the standing task.
