# Orbit scalars from original self-base-change squares

## Purpose and scope

This derived construction connects original parameter-translation comparison
squares to scalar values on the existing full complex unramified twist orbit.
It first proves fixedness of the extracted fraction under each indicated
translation. For the actual smooth-object stabilizer, finiteness then gives an
invariant numerator/denominator presentation. Values of any such presentation
recover the original continued-composite coefficient at common regular
parameters. With normalized extraction and generic scalarity, they recover the
whole endomorphism as that value times the identity.

The comparison witnesses are linear equivalences on the two fixed carriers
and squares for the original operator families. They are not assumed to be
induced by a representation isomorphism, and this module does not construct
those witnesses for standard integral intertwining operators. Its conditional
identities are support for that application, with the representation-theoretic
premises retained as proof obligations of the overall program.

## Source and provenance

The original source is J.-L. Waldspurger, *La formule de Plancherel pour les
groupes p-adiques (d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003),
235–333, DOI 10.1017/S1474748003000082, registered as
`waldspurger-2003-plancherel`. The PDF fingerprint is
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

IV.1, printed pp.276–277 / PDF pp.42–43, defines the complex twist orbit as
isomorphism classes, defines scalar polynomial and rational functions by
character pullback, identifies the induced spaces with fixed compact
carriers, and requires compatibility of operator families with the maps
induced by representation isomorphisms. At the beginning of IV.3, printed
p.285 / PDF p.51, generic induced irreducibility and Schur's lemma give the
rational opposite-composition scalar.

This module is an internal consequence of the existing continuation,
base-change, scalar-extraction and finite-stabilizer descent constructions.
It is not a separately numbered theorem of the article. The actual character
topology and evaluation-generated regular algebra are the existing Library
ones; no algebraic-variety quotient comparison is added. Original-source
naturality motivates the supplied squares but does not discharge them.
The original passages were read for this construction. No source errata file
was present at `notes/errata/waldspurger-2003-plancherel.md` in the workspace
or fixed Library base.

## Common objects and hypotheses

In the generic comparison structure, `H` is an arbitrary topological group,
`ν : I → (H →* ℝ≥0ˣ)` is the existing norm family, and `V` and `W` are complex
modules. The group, index and two carrier universes are independent. The
parameter space is the existing `unramifiedCharacters ν`, with its inherited
topology. Write `tτ(χ) = τ * χ` for `unramifiedParameterTranslation ν τ`.

In the actual specialization, the field `F` has an arbitrary universe,
`Field`, `ValuativeRel`, `TopologicalSpace`, and
`IsNonarchimedeanLocalField` instances. The group scheme `L` is over `F`,
its rational points have a supplied topology, `hp` asserts continuity of
`rationalValuationImageProjection L`, and `hL` asserts connected reductivity.
The norm family consists of all `rationalNormCharacters L`. No
characteristic-zero, splitness, quasisplitness or positive-rank premise is
introduced. The two complex module carriers have universes independent of
that of `F`.

The original families have types `A : Ω → V →ₗ[ℂ] W` and
`B : Λ → W →ₗ[ℂ] V`. The independent continuation data `p` and `q` each
include their own whole-operator denominator, polynomial numerator data and
agreement with the original family. Nonemptiness of each original region is
explicit; the regions need not intersect. Their common full regular region
is `R = p.regularRegion ∩ q.regularRegion`. On it the continued composite is
`q_ext(χ) ∘ p_ext(χ)`. The imported domain and density results prove that
`R` is dense and nonempty.

For `v : V` and `ℓ : V →ₗ[ℂ] ℂ`, the extracted coefficient is
`ℓ ((q_ext(χ) ∘ p_ext(χ)) v)`. The existing
`continuedCompositeRationalScalar` is its fraction in the actual
`rationalUnramifiedFunctionField L hp hL`. This coefficient becomes the
endomorphism scalar under the displayed generic-scalar premise and
normalization `ℓ v = 1`.

The orbit-facing declarations additionally require
`NonarchimedeanGroup (GroupScheme.rationalPoints L)` and a canonical
`SmoothRep ℂ (GroupScheme.rationalPoints L)` object `π`. Its orbit and
stabilizer use full complex unramified characters and actual smooth-object
isomorphism classes. The operator carriers are not identified with `π` or
its inductions by this module: applications must provide their actual
operator families and the corresponding squares.

## Original self-comparison data

`UnramifiedOperatorFamily.SelfBaseChangeData Ω Λ A B τ` has source and target
linear self-equivalences `S : V ≃ₗ[ℂ] V` and `T : W ≃ₗ[ℂ] W`. It specifies
separate nonempty ambient open sets `D` and `E` and containments

- `D ⊆ tτ⁻¹(Ω)` and `D ⊆ Ω`;
- `E ⊆ tτ⁻¹(Λ)` and `E ⊆ Λ`.

On those respective sets its original comparison squares are

```text
A(χ) ∘ S = T ∘ A(τ * χ),
B(χ) ∘ T = S ∘ B(τ * χ).
```

The forward and reverse comparison sets may be disjoint and are not
required to avoid continuation denominators. No topology on either module
carrier, finite-dimensionality, irreducibility, subgroup law for the chosen
self-equivalences, or equivariance beyond these explicit squares is part of
the structure.

## Fixedness and orbit presentation

`continuedCompositeRationalScalar_fixed_of_selfBaseChange` takes one such
witness, a nonempty ambient open set `U`, generic scalarity of the continued
composite for characters in `R ∩ U`, and a normalized pair `(v, ℓ)`. It proves

```text
Tτ(continuedCompositeRationalScalar p q v ℓ)
  = continuedCompositeRationalScalar p q v ℓ,
```

where `Tτ` is the existing fraction-field automorphism with regular-function
pullback `b(χ) ↦ b(τ * χ)`. The proof specializes
`continuedCompositeRationalScalar_base_independent` to the same two original
families, the same independent continuations, and the same normalized
extraction pair on both charts, then reverses its equality. Its use of
rational uniqueness extends the original squares from the two separate
opens. Since `R` is dense, the scalarity premise on the nonempty open `U`
is not vacuous.

`continuedCompositeRationalScalar_subgroup_fixed` accepts an arbitrary
subgroup `S` of the actual complex character group and, for each `τ : S`,
`Nonempty (SelfBaseChangeData Ω Λ A B τ.val)`. Applying the preceding result
to each witness proves fixedness for every subgroup element. Finiteness is
not required here, and scalar fixedness is a conclusion of the theorem.

`continuedCompositeOrbitScalarPresentation` uses the actual full smooth
object twist stabilizer of `π` for `S`. It adds `Finite S` to the previous
hypotheses and chooses an
`UnramifiedInvariantScalarPresentation` of the extracted fraction. This is
a regular numerator and nonzero regular denominator, both invariant under
the actual stabilizer, whose quotient is that exact fraction. The proof
supplies the just-derived fixedness to
`unramifiedTwistOrbitScalarPresentation_exists`; that construction uses the
finite translation norm of a denominator. No invariant numerator,
invariant denominator or fixed scalar is separately assumed here.

Finiteness of the stabilizer is explicit in this definition. The imported
orbit module separately derives it for irreducible admissible objects from
a central morphism with the stated actual-image finite-index condition.
This module does not construct that morphism or prove its finite-index
condition. The resulting scalar values on the actual orbit inherit the
previous module's chosen regular region and presentation compatibility.

## Regular values and full operator equation

`UnramifiedInvariantScalarPresentation.orbitValue_eq_scalarPresentation`
compares any invariant presentation `r` of a fraction `f` with any existing
`ScalarPresentation Ω g` whose image in the actual fraction field is `f`.
For `χ : Ω`, if `r.denominator(χ) ≠ 0`, it proves that the orbit value at the
class of `π ⊗ χ` equals `g χ`. The second denominator is already nonzero
on `Ω` by its scalar-presentation data. The proof uses injectivity of the
regular-algebra inclusion into the field, cross-multiplies the two fraction
identities in that field, injects the resulting equality back into the
regular algebra, and evaluates it at `χ`. Division is used only with the
two displayed nonzero complex denominator values.

`continuedCompositeOrbitScalar_value` applies this comparison to the
coefficient presentation of `p.continuedComposite q`. For every `χ : R`
where `r` is also regular, its orbit value is exactly
`endomorphismScalarCoefficient v ℓ (p.continuedComposite q χ)`. This
comparison requires no extraction normalization, generic scalarity,
finite-stabilizer instance or self-comparison witness once the invariant
presentation is supplied.

`continuedComposite_eq_orbitScalar` adds `ℓ v = 1` and generic scalarity on
`R ∩ U` for a nonempty ambient open `U`. It proves, for every such common
regular character `χ`,

```text
p.continuedComposite q χ
  = r.orbitValue π [π ⊗ χ] • LinearMap.id.
```

Here the orbit value includes its required regular-region membership
proof. The proof first rewrites the orbit value by the preceding coefficient
comparison. It intersects `U` with the two operator regular regions;
density of their intersection proves this is a nonempty open set. It then
applies `rationalUnramifiedScalarContinuation` to the actual rational
endomorphism family and its normalized coefficient. The character `χ`
itself need not lie in `U`, and no irreducibility assumption at `χ` enters.

All value declarations use the existing chosen invariant denominator
nonzero locus, which is dense and open on the orbit but is not claimed
maximal. They assign no value at a pole. They do not assert density on the
unitary character locus or identify this full complex orbit with a unitary
discrete-series orbit.

## Dependencies and retained obligations

The two direct imports are `ContinuedIntertwiningScalarBaseChange` for
original-square continuation and scalar translation, and
`UnramifiedScalarOrbit` for the actual quotient orbit and invariant
presentation existence and values. Through those modules the construction
uses the original whole-operator continuation interface, the actual regular
algebra and its domain/density/faithful-field-inclusion results, rational
scalar extraction and continuation, and finite-group denominator descent.
The full operator equation uses the imported rational uniqueness theorem;
it does not repeat Schur's lemma or a generic irreducibility proof.

The original self-comparison witnesses, standard-integral convergence and
rationality, and generic induced irreducibility still require proofs in
their representation-theoretic application. Also separate are the actual
induced-carrier realization of these witnesses, opposite-parabolic
identification, independence of the parabolic and extraction choices in the
global orbit construction, nonvanishing and positivity, the source's
normalized global `j` and `mu`, unitary regularity and orbit measures, and
the main analytic, finiteness and inversion results. None of these
representation or analysis conclusions is reclassified as an allowed
external structural hypothesis by this helper module.

Authored by Worker 200.
