# Canonical scalar orbit presentations from an actual split component

Author: Worker 200.

## Source and provenance

This is an internal data adapter between the published modules
`StandardInductionCanonicalScalar`, `UnramifiedScalarOrbit`,
`SplitComponentLatticeBridge`, and `CompactCoefficient.GroupTransport`.
It makes no new translation claim about an original literature assertion.
It constructs an invariant presentation of the existing canonical rational
scalar by deriving its finite full-stabilizer premise from actual
split-component data and an irreducible admissible inducing object.
The rational scalar and the actual integral families are unchanged.

## Actual topology and finite stabilizer

Let `F : Type u` be a nonarchimedean local field of arbitrary
characteristic. Let `L` be an affine, locally finite-type, connected
reductive group scheme over `F`. Its rational points carry exactly
`rationalPointTopology F L.X`; the nonarchimedean group structure is the
published `rationalPoints_nonarchimedeanGroup L`.

The additional data are an affine commutative group scheme `T`, a
morphism `s : T.toGrp ⟶ L`, a proof `hs : IsSplitComponent s`, and
injectivity of the actual rational-character restriction
`GroupScheme.characterRestrict s`. The restriction injectivity remains an
explicit premise. The adapter does not construct `s` or prove that premise.

`finite_pullback_rationalSmoothRepUnramifiedTwistStabilizer` also takes an
arbitrary topological group `H : Type uG`, a continuous group equivalence
`e : L(F) ≃ₜ* H`, and a canonical complex smooth object
`A : SmoothRep.{0,uG,uV} ℂ H` with irreducibility and admissibility.
Admissibility has the canonical all-open-subgroups convention; it does
not mean finite dimension of the entire representation.

The proof bundles `SmoothRep.pullback e A` as an actual
`IrreducibleAdmissibleRep`. The published group-transport results prove
its irreducibility and admissibility on the same carrier. It then uses
`RenardCartan.finiteIndex_splitValuationImage_of_injective hL s hs hinj`
and the centrality contained in `hs` to apply
`finite_rationalSmoothRepUnramifiedTwistStabilizer`. The conclusion is
finiteness of exactly

```
smoothRepUnramifiedTwistStabilizer
  (fun ψ => (rationalNormCharacters L ψ).toMul)
  (SmoothRep.pullback e A)
```

This is the full self-twist stabilizer defined using smooth-object
isomorphism classes. Finiteness of a representation family, of its orbit,
or of a selected smaller stabilizer is never assumed. This lemma needs
neither a continuous valuation-image projection nor an intertwining
operator or generic induced irreducibility premise.

## The canonical scalar constructor

`standardInductionSplitComponentCanonicalOrbitScalarPresentation`
specializes the existing actual-standard-integral construction to this
canonical topology. Its ambient group `G : Type uG` is locally compact,
Hausdorff, nonarchimedean and separable. It retains actual closed
semidirect decompositions `P₀ = M U₀`, `P₁ = M U₁`, both unimodular
radical-modulus premises, a common compact open `K`, both decompositions
`G = Pᵢ K`, and continuity of both semidirect projections. Here
`e : L(F) ≃ₜ* M`, and `A` is an irreducible admissible canonical
`SmoothRep.{0,uG,uV} ℂ M`.

The complete rational norm-character family on `L(F)` is transported to
`M` along `e.symm`. Continuity of these characters and of the actual
valuation-image projection is explicit. The field, ambient-group and
representation-carrier universes `u,uG,uV` are independent.

All existing measure data remain explicit: Borel structures on both
radicals, both intersections and both quotients; regular right-invariant
Haar measures on the radicals and intersections; compatible quotient
measures `q₁₀,q₀₁`; closedness of `M`; and both squared-modulus
compatibility identities. These data use the same literal subgroups and
fixed compact model as the canonical scalar construction.

The two continuations `p,q` are independent whole-operator rational
continuations of the compact restrictions of the actual
`standardInductionIntertwinerFamily` in the two directions. Their
original full-domain regions require scalar convergence against every
smooth-dual functional and representability in the original carrier for
every input and group element. Each continuation has one polynomial
operator numerator and one denominator nonzero on its original region.
Separate nonempty ambient open subsets of both original full domains
are retained. They are not assumed to intersect. A separately supplied
nonempty ambient open locus `D` carries actual irreducibility of the
`P₀` normalized induced twists. No irreducibility of all tempered
inductions or intersection of these three open subsets is assumed.

Write `π = SmoothRep.pullback e A` and let `jC` be precisely
`standardInductionCompositeCanonicalRationalScalar` with these data.
The constructor first installs the finite full-stabilizer instance
proved above, then calls
`standardInductionCompositeCanonicalOrbitScalarPresentation`. Its
result is

```
UnramifiedInvariantScalarPresentation L hp hL
  (smoothRepUnramifiedTwistStabilizer νL π) jC
```

Thus it supplies an invariant regular numerator, a nonzero invariant
regular denominator and a proof that their fraction is the existing
canonical scalar. It takes no `Finite` or scalar-fixedness hypothesis:
the former is proved by this adapter, and the latter is proved for the
actual standard family by the imported canonical construction. It also
takes no external normalized coefficient; that coefficient is already
chosen internally from an actual irreducible induction.

## Using the constructed data and remaining obligations

The result is an ordinary invariant presentation for exactly the existing
scalar and full stabilizer. The published
`UnramifiedInvariantScalarPresentation.orbitRegularRegion` and
`orbitValue` therefore supply its value on a nonempty dense open subset
of the actual complex twist orbit. The existing canonical scalar
comparison theorems apply to this result directly: the continued actual
standard composite equals its orbit value times the identity when the
continuation denominators and presentation denominator are nonzero.
The original-composite theorem also applies at points of both original
full domains. No new region nonemptiness or equation is asserted beyond
those already provided by these interfaces, and no evaluation at a pole
is introduced.

The construction is conditional on its displayed split component,
restriction injectivity, inducing irreducibility and admissibility,
convergence subsets, whole-operator continuations, generic actual
induced irreducibility, and subgroup, topology and measure data. These
representation-theoretic and analytic premises remain application proof
obligations and are not promoted to external structural hypotheses for
completion of the Plancherel program. The adapter supplies the finite
full stabilizer from the stated structural and inducing inputs; it does
not prove generic induced irreducibility from inducing irreducibility.

It imposes no characteristic-zero, splitness or quasisplitness
restriction on `L`. It does not establish the realization of the
remaining inputs for every reductive group, unitary-orbit density or
measure, maximal regularity, nonvanishing, positivity, independence of
other parabolic pairs, compact models or measures, source-normalized
`j` or `mu`, or a main Plancherel assertion.

Integration uses module-specific names for local instances. Their types, values,
and local instance scopes are unchanged.
