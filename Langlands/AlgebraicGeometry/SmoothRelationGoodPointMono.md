# Differential generation from a monomorphic relation

This internal prerequisite for the smooth-relation slicing proof constructs the
graph of a derivation and proves differential generation on affine charts of a
monomorphic relation. It also proves the same generation after localization,
including localization at a prime. It imports only Mathlib. All declarations
are in `Langlands.AlgebraicGeometry.SmoothRelationGoodPoint`.

## The derivation graph

For commutative rings `A`, `B`, an `A`-algebra `B`, a `B`-module `M` with the
additional module structures in the Lean declaration, and an `A`-derivation
`δ : Derivation A B M`, `derivationGraph δ` is the actual ring homomorphism

`b ↦ (b, δ(b)) : B → TrivSqZeroExt B M`.

The opposite `B`-action is required to agree with the `B`-action through
`IsCentralScalar B M`. The zero and one identities follow from the derivation
identities, additivity gives the additive identity, and the Leibniz rule gives
multiplicativity. `derivationGraph_snd` records its second component.

## Cancellation on affine charts

Let `t s : R → U` be scheme morphisms in an arbitrary universe, with
`Mono (prod.lift t s)`. Let `V` be an affine open of `U`, and `W` an affine open
of `R` mapping into `V` under both `s` and `t`. Write

- `A = Γ(U,V)` and `B = Γ(R,W)`;
- `σ : A → B` for the pullback along `s`;
- `θ : A → B` for the pullback along `t`.

`ringHom_ext_of_mono` proves that two homomorphisms `f g : B → C`, for a
commutative ring `C` in the scheme universe, are equal if their compositions
with both `σ` and `θ` agree. Their induced maps from `Spec C` to `R` have equal
composites with `t` and `s`, so the product's universal property and monicity
make the maps to `R` equal. Cancellation of the affine chart's `fromSpec` map
and faithfulness of `Spec` then give `f = g`.

`derivation_eq_zero_of_mono` equips `B` with the given `A`-algebra structure
and explicitly assumes that its algebra map is `σ`. If an `A`-derivation
`δ : B → M` vanishes on `θ(A)`, it is zero. Indeed, its graph and the canonical
inclusion `b ↦ (b,0)` agree on `σ(A)` because it is an `A`-derivation, and on
`θ(A)` by the hypothesis. The preceding cancellation lemma identifies the
homomorphisms. Their second components identify `δ` with zero. Here `M` is in
the scheme universe, and the proof supplies its canonical opposite `B`-action
using commutativity of `B`.

## Differential generation and localization

`span_targetDifferentials_eq_top_of_mono`, under the same chart hypotheses,
proves

`span_B {d(θ(a)) | a ∈ A} = Ω[B/A]`.

The relative differential uses the algebra structure `σ`. Let `N` be the span
on the left. The universal derivation followed by the quotient map to
`Ω[B/A]/N` vanishes on `θ(A)`. The preceding derivation lemma makes this
quotient derivation zero. Every universal differential therefore lies in `N`,
and universal differentials generate `Ω[B/A]`.

`span_targetDifferentials_localization_eq_top_of_mono` allows a submonoid `S`
of `B` and any commutative `B`-algebra `T` which is an `S`-localization, with a
compatible `A`-algebra structure. It proves

`span_T {d(algebraMap B T (θ(a))) | a ∈ A} = Ω[T/A]`.

Mathlib identifies the canonical differential map `Ω[B/A] → Ω[T/A]` as a
module localization. Its theorem `span_eq_top_of_isLocalizedModule` transports
the proved spanning result, and `KaehlerDifferential.map_D` identifies the
generators. `span_targetDifferentials_atPrime_eq_top_of_mono` specializes this
result to `T = Localization.AtPrime q` for any prime ideal `q` of `B`, with the
canonical tower of algebra structures. The general localization result permits
the universe of `T` to be independent of the scheme universe.

## Provenance and scope

Worker 303 proposed the monomorphism and square-zero-extension route as the
first step of the good-point existence argument. Worker 101 implemented the
graph, affine cancellation, quotient differential proof and localization
consequences. This is an internally derived auxiliary construction; no external
literature theorem is assumed. Smoothness, local finite type, a section and
an equivalence-relation hypothesis are unnecessary for these lemmas. The module
does not choose coordinates, prove existence of a good point, or prove the
global etale-and-surjective slicing theorem. Those later steps use the
differential generation established here.
