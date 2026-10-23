# Distribution character of an admissible representation

`Langlands.Character.distribution μ ρ hρ` is the actual algebraic distribution
character obtained by taking the finite-rank trace of the integrated action.
It belongs to `HarmonicAnalysis.Distribution G`, the complex algebraic dual of
`SchwartzBruhat G`.

## Parameters and definition

The group `G : Type uG` is a Hausdorff, locally compact, totally disconnected
topological group, with its Borel measurable structure. The complex vector space
`V : Type uV` has no topology or finite-dimensionality assumption. The universes
`uG` and `uV` are independent. The explicit measure `μ` is finite on compact sets
and left invariant. No nonzero-measure or mass normalization hypothesis is needed
for the construction; in particular it applies to a chosen left Haar measure.
The hypothesis `hρ : IsAdmissible ρ` supplies smoothness and finite-dimensional
fixed vectors for every open subgroup, according to the Library convention.

`finiteRankIntegratedAction μ ρ hρ` is a complex linear map from the actual test
functions into `finiteRankEnd V`. Its underlying operator at `f` is exactly
`Hecke.integratedAction μ ρ hρ.1 f`. The published finite-rank action theorem gives
a finite-dimensional range for that operator. `mem_finiteRankEnd_iff` converts
this fact to membership of the finite-rank submodule, and `codRestrict` bundles
the unchanged operator with the restricted codomain.

`distribution` composes this map with `FiniteRankEnd.trace`. Thus
`distribution_apply` is the pointwise identity

`distribution μ ρ hρ f = FiniteRankEnd.trace (finiteRankIntegratedAction μ ρ hρ f)`.

This trace is computed on the actual finite-dimensional image. The composition
of two linear maps proves that the result is a distribution. Ambient trace on an
infinite-dimensional vector space is not used in this definition.

## Finite-stage computation and equivalence invariance

`distribution_eq_subspace` computes the value using ordinary trace on any
finite-dimensional subspace `S` containing the image of the integrated operator.
The endomorphism of `S` is `FiniteRankEnd.onSubspace`, the actual restriction of
that operator to `S`. This follows directly from the containing-stage comparison
for finite-rank trace.

`distribution_eq_fixedVectors` specializes the formula to the fixed vectors of an
open subgroup `K`. Its test function is bi-invariant under `K` on the left and
an arbitrary subgroup `J` on the right. Admissibility supplies finite-dimensionality
of the fixed-vector space; the published image bound supplies containment. The
resulting endomorphism is explicitly `integratedActionToFixed` composed with the
fixed-vector inclusion. Compactness of `K` is not required by this specialization.

For an admissible representation `σ` on `W : Type uW`, a genuine linear equivalence
`E : V ≃ₗ[ℂ] W` satisfying `E (ρ g v) = σ g (E v)` gives
`finiteRankIntegratedAction_equivariant`: the integrated operator for `σ` is
`E` conjugating the integrated operator for `ρ`. The proof bundles `E` as an
intertwining map, applies integrated-action intertwining at `E.symm w`, and uses
the inverse identity. Finite-rank trace conjugation then proves
`distribution_eq_of_equivariant`. The universes `uV` and `uW` are independent,
and neither carrier is assumed finite-dimensional.

## Conjugation and the measure hypothesis

Put `c_a(x) = a * x * a⁻¹`. The pullback convention is
`pullback (conjugationHomeomorph a) f = f ∘ c_a`, and the distribution pushforward
acts on `f` by evaluating the original distribution on that pullback.

`integratedAction_conjugation_of_measurePreserving` assumes explicitly that
`c_a` preserves `μ`. It proves

`ρ(f ∘ c_a) v = ρ(a⁻¹) (ρ(f) (ρ(a) v))`,

where `ρ(f)` abbreviates the actual integrated operator. The proof compares two
finite-valued action integrands: composing the integrand for `f` at `ρ(a)v` with
`c_a` equals applying `ρ(a)` to the integrand for `f ∘ c_a` at `v`. The group
representation law proves the pointwise equality. The algebraic integral's
measure-preserving change-of-variables identity and linear-map compatibility give
`ρ(a) (ρ(f ∘ c_a)v) = ρ(f)(ρ(a)v)`. Applying `ρ(a⁻¹)` proves the displayed formula.
This intermediate theorem does not require the Hausdorff, local compactness,
total disconnectedness or left-invariance assumptions; Lean omits them there.

For `distribution_conjugation_of_measurePreserving`, the formula identifies the
finite-rank operator as conjugation by the linear equivalence with forward map
`ρ(a⁻¹)` and inverse map `ρ(a)`. Genuine trace conjugation proves equality of
character values. If every inner automorphism preserves `μ`,
`distribution_isConjugationInvariant_of_measurePreserving` gives the actual
`Distribution.IsConjugationInvariant` predicate. Finally,
`distribution_isConjugationInvariant` assumes right invariance in addition to
left invariance. Left translation by `a` followed by right translation by `a⁻¹`
then proves the required measure preservation.

## Source and provenance

The original source is Bernstein and Zelevinsky, *Representations of the group
GL(n,F), where F is a non-Archimedean local field (survey)* (1976), registered as
`bernstein-zelevinsky-1976-representations-gln`, SHA256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
The retained original is
`/home/taskhub/central-library/Bernstein-Zelevinsky--Representations of the group GL(n,F) where F is a non-archimedean local field (survey)--1976.pdf`.
Section 2.17, printed/PDF page 21, defines the distribution character using the
finite-rank integrated operator trace. Section 2.18 gives the modular conjugation
law for a general left Haar measure. The invariant special case implemented here
retains the explicit inner measure-preservation assumption, or the sufficient
right-invariance hypothesis. It does not assert unconditional conjugation
invariance for an arbitrary left Haar measure.

The definition follows Section 2.17. The implementation of finite-stage
computation, equivalence invariance and the measure-preserving specialization of
Section 2.18 is derived from the imported Library's finite-rank trace, integrated
action, algebraic integral and distribution transport APIs. The concrete Lean
proofs are described above. The more general measure parameter and arbitrary
carrier universes are justified by these proofs. Character separation, transport
to the smooth dual and the Gelfand–Kazhdan realization remain separate obligations.
