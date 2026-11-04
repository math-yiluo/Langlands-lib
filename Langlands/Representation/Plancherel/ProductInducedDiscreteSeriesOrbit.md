# Actual discrete-series orbits and full-stabilizer tensor comparison

Author: Worker 200.

This derived adapter connects the actual representative section space to the
discrete-series orbit and full unramified stabilizer used by Waldspurger.
It imports the existing constructions by Lean name from
`ProductInducedOrbitSections` and `TwistStabilizerComparison`.

The original source is J.-L. Waldspurger, *La formule de Plancherel pour les
groupes p-adiques (d'après Harish-Chandra)* (2003), source ID
`waldspurger-2003-plancherel`, SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
III.7, printed p.273 (PDF p.39), defines the actual unitary twist orbits in
the discrete series and uses the full finite unramified stabilizer.
The proof of III.7.1, printed p.274 (PDF p.40), uses the finite quotient by
the common kernel and split center.
VI.1, printed pp.295–296 (PDF pp.61–62), describes coherent sections on
actual representatives and their diagonal invariant tensor realization.
All four original pages were read for this adapter.
The comparisons below are derived content, rather than separately quoted
theorems from these passages.

## Inputs and the actual discrete-series orbit

Let `G : Type uG` be a nonarchimedean topological group, let `M` be an actual
subgroup, and let `nu : I → (M →* ℝ≥0ˣ)` be a family of positive characters,
where `I : Type uI`.
Let `pi : IrreducibleAdmissibleRep.{0, uG, uV}` be a canonical complex
smooth object of `M`. The group, character-index and representation-carrier
universes are independent. All representatives lie in this one arbitrary
carrier universe; there is no claim about a quotient over all universes.

Fix a normal central subgroup `C` of `M`, with the displayed proof
`hC : C ≤ Subgroup.center M`. Give the actual quotient `M ⧸ C` a measurable
space and a measure `mu` with `Measure.IsHaarMeasure mu`.
For the discrete-series part supply
`hpi : IsSquareIntegrableModCentralSubgroup C hC pi.obj.representation mu`.
The source application takes `C` to be the actual split center, with its
compatible quotient measure. This unit keeps that realization explicit.

`UnitaryOrbitRepresentative nu pi` is the existing subtype of actual
irreducible admissible objects whose canonical smooth class is a unitary
unramified twist of the class of `pi`.
`unitaryOrbitRepresentative_isDiscreteSeries` proves that every such object
is square-integrable on the same central quotient. Its proof extracts the
actual character from the orbit-membership witness, rewrites by the actual
class equality, and applies the published
`isDiscreteSeriesClass_unitaryTwist`. No new square-integrability predicate
or assumed orbit identification is introduced.

`unitaryOrbitRepresentativeDiscreteSeriesOrbit` sends each representative
to its actual `discreteSeriesClass` in
`discreteSeriesOrbit C hC mu nu (discreteSeriesClass C hC mu pi hpi)`.
It retains the original canonical smooth class.
`unitaryOrbitRepresentativeDiscreteSeriesOrbit_surjective` extracts the
unitary character of any orbit element and uses the actual twisted object
of `pi` as its representative.
This map is surjective because multiple isomorphic inducing objects are
intentionally retained as different representative indices.

`unitaryClassStabilizerEquivDiscreteSeries` identifies the existing
unitary class stabilizer with `discreteSeriesStabilizer` of this actual
discrete-series class. Both directions retain the same unitary character;
subtype extensionality passes between equality of discrete-series classes
and equality of their underlying canonical smooth classes.
These orbit and stabilizer comparisons do not need a finite quotient.

## The full stabilizer and the retained finite-quotient premise

For the remaining constructions assume exactly

```lean
[Finite (M ⧸ (commonNormKernel nu ⊔ C))]
```

This is a displayed premise of the derived adapter. For actual reductive
points its proof is a retained mathematical obligation, not an additional
permitted external Chapter V assertion.
`RationalCentralQuotient` and `RationalTwistStabilizer` provide existing
conditional actual-point realizations from finite index of the actual
`RenardCartan.splitValuationImage`. The general proof of that finite-index
premise remains separate.

Write \(S\) for `unramifiedTwistStabilizer nu omega` of an actual canonical
smooth class and \(S^u\) for `unitaryClassTwistStabilizer nu omega`.
`unitaryClassStabilizerEquivFull` constructs
\[
  E:S^u\simeq S.
\]
Its forward map is the existing literal inclusion.
The inverse keeps the same continuous character and obtains its norm-one
property from the published `unramifiedTwistStabilizer_norm_eq_one`.
That theorem uses admissible Schur on the inducing representation to prove
triviality on the central subgroup, descends the character to the displayed
finite quotient, and uses finite order to prove norm one.
Thus unitarity of the full stabilizer is proved under the displayed premise.
The `_apply` theorem records agreement of the forward map with the
original inclusion.

`finite_unitaryClassTwistStabilizer` transfers the published
`finite_unramifiedTwistStabilizer` along this injective equivalence.
This is finiteness of the stabilizer of a single actual class.
It establishes no finiteness of the family of discrete-series orbits or of
spectral support.

## Actual diagonal action and comparison of invariant tensors

Supply `e : unitaryUnramifiedCharacters nu ≃* (J → Circle)` with
`J : Type uJ` finite. The coordinate universe is independent of the other
three. The construction uses the existing scalar smooth functions on this
finite torus, defined using their real exponential lifts, and their
algebraic tensor product with the coefficient module.
It assumes no topology on the coefficient module and proves no new
topological or manifold comparison for `e`.

For the compact coefficient action also supply actual subgroups `P`, `U`,
`h : IsSemidirectDecomposition P M U`, a compact open subgroup `K`, closed
`P`, continuity of all `nu i`, and continuity of the actual Levi projection.
Put `W = ProductInducedCompactPicture h K pi.obj`.
The existing `unramifiedStabilizerCompactRepresentation` is the actual
full-stabilizer representation \(\rho:S\to\operatorname{End}_{\mathbb C}(W)\).
Its vector transport and inverse pullback on smooth functionals are retained;
the self-twist action can be nontrivial. Its group laws and independence of
chosen inducing equivalences are already proved using inducing admissible
Schur, without irreducibility of the induced representation.

`fullStabilizerTorusHom` is the actual homomorphism
\[
 \tau(s)=e\bigl((E^{-1}s).\mathrm{val}\bigr).
\]
`productInducedFullStabilizerTensorRepresentation` combines inverse
translation by \(\tau(s)\) on scalar functions with \(\rho(s)\) on `W`.
In particular its pointwise invariance condition is
\[
 F(z\,\tau(s))=\rho(s)F(z),
\]
as given by the imported `mem_smoothTensorInvariants_iff`.

`productInducedFullStabilizerTensorInvariants_eq` proves equality with the
existing unitary-class invariant submodule of the same tensor carrier.
It applies that pointwise criterion in both directions, substituting
`E s` or `E.symm s`. Because these maps preserve the actual character,
both the torus coordinate and the actual coefficient operator agree.
This proof does not replace the coefficient action by a trivial action.

## Actual coherent sections and evaluation

For the normalized induced section comparison, additionally assume
`LocallyCompactSpace G`, closed `U`, and the actual factorization
`∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G)`.
The section fibers are the existing
`productInducedCoefficientObject h hU A.obj` over every actual
`UnitaryOrbitRepresentative nu pi`.
They use the actual normalized product induction and smooth contragredient,
with coherence under every inducing equivalence and finite scalar-smooth
compact restriction.

`productInducedFullStabilizerTensorOrbitEquiv` composes identity on the
equal invariant tensor submodules with the published
`productInducedSmoothTensorOrbitEquiv`. It gives the linear equivalence
\[
 [C^\infty(J\to\mathrm{Circle})\otimes_{\mathbb C}W]^S
 \simeq_{\mathbb C}
 \operatorname{productInducedSmoothOrbitSections}.
\]
When `hpi` is supplied, the first part of this module identifies its actual
representative indices with representatives of the specified
discrete-series orbit. The full-stabilizer tensor comparison itself also
works for irreducible admissible `pi` without square-integrability.

The `_restriction` theorem says that pulling the resulting section back to
each literal parameter representative and applying the actual normalized
compact restriction gives exactly `smoothTensorEvaluation` of the original
tensor at that parameter. The `_symm_evaluation` theorem gives the reverse
identity for every original section. Both follow from the corresponding
published evaluation identities, since the intermediate map retains the
underlying tensor.

The general reductive realization, source Levi-inflated normalization
comparison, formal degrees, Hermitian forms, density, normalized
intertwiners, orbit measures, wave packets and analytic Plancherel remain
separate obligations. No irreducibility of tempered parabolic induction
or desired analytic conclusion is an input to this adapter.
