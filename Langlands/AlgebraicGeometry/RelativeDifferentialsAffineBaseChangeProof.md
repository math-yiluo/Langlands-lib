# Canonical differential base change for spectra

`Langlands.Scheme.relativeDifferentialsAffineBaseChangeIsIso` proves exactly
the published proposition
`Langlands.Scheme.RelativeDifferentialsAffineBaseChangeIsIsoStatement.{u}`.
For all `R A B : CommRingCat.{u}` and all ring maps `f : R ⟶ A` and
`b : R ⟶ B`, the actual canonical comparison

```text
relativeDifferentialsBaseChangeMap (Spec.map f) (Spec.map b)
```

is invertible on the categorical scheme pullback. The universe `u` is
arbitrary. Zero rings are included, and no flatness, smoothness, finiteness,
nonemptiness, extra affineness certificate, or supplied base-change witness is
assumed. The statement and its dependencies are imported unchanged.

## Comparison with algebraic differentials

`relativeDifferentialsSquareMap_isIso_of_tilde_comparison` first treats an
algebra pushout `R → A`, `R → S`, with pushout ring `B`. Write
`g : Spec B ⟶ Spec A` and `q : Spec B ⟶ Spec S`. Mathlib's
`KaehlerDifferential.tensorKaehlerEquiv R S A B` is the `B`-linear
isomorphism

```text
B ⊗[A] Ω[A/R] ≃ₗ[B] Ω[B/S].
```

The proof identifies two maps out of `g* (tilde Ω[A/R])`. The first is the
pullback of the published spectral comparison followed by the actual
canonical square map. The second is the tilde-pullback isomorphism, followed
by the associated-sheaf map of the tensor differential isomorphism and the
spectral comparison for `S → B`.

Apply the pullback/pushforward adjunction and then the tilde/global-sections
adjunction. Linear maps out of `Ω[A/R]` are determined by the generators
`D a`, using `LinearMap.ext_on_range` and
`KaehlerDifferential.span_range_derivation`. On each generator,
`relativeDifferentialsSpecMap_app_toOpen_D`,
`relativeDifferentialsSquareMap_adjoint_app`, the tilde-pullback generator
formula, and `KaehlerDifferential.tensorKaehlerEquiv_tmul_D` identify the
two maps. `Scheme.ΓSpecIso_inv_naturality` identifies the pulled-back
global function. Thus the comparison uses the published local-section
formula of the concrete canonical map. Cancellation of the spectral
comparison and preservation of isomorphisms then prove invertibility of
that square map.

## The categorical scheme pullback

`relativeDifferentialsBaseChangeMap_spec_isIso_of_tilde_comparison`
specializes to `C = A ⊗[R] S`, with the two tensor inclusions. The standard
`Algebra.IsPushout` instance, used with its symmetry, supplies the ring
pushout hypothesis. Mathlib's `pullbackSpecIso R A S` identifies the
categorical scheme pullback with `Spec C`. Its inverse has the two required
projection identities, `pullbackSpecIso_inv_fst'` and
`pullbackSpecIso_inv_snd`.

The independent helper module `RelativeDifferentialsBaseChangeTransport`
proves composition and congruence for the canonical square maps from their
adjoint formula on local differentials. Its
`relativeDifferentialsBaseChangeMap_isIso_of_square` uses those identities
to compare the square map on `Spec C` with the pullback of the actual
categorical base-change map. The open-immersion comparison applies to the
isomorphism from `Spec C` and the identity base map. Cancellation and the
singleton isomorphism cover then prove that the original categorical map
is invertible.

## Discharging the comparison inputs

`relativeDifferentialsBaseChangeMap_spec_isIso_of_comparisons` converts the
arbitrary maps `f` and `b` to algebra instances via `RingHom.toAlgebra`.
It supplies the published `Modules.tildePullbackAlgebraIso` and
`Modules.tildePullbackAlgebraIso_adjoint_toOpen`. This algebra-form API
identifies scalar extension along the ring homomorphism with the tensor
module for the given algebra structure and preserves pure tensors.

The final theorem supplies the published proofs
`relativeDifferentialsOpenImmersionIsIso` from
`RelativeDifferentialsOpenImmersionProof` and
`relativeDifferentialsSpecMapIsIso` from `RelativeDifferentialsSpecMapIsIso`.
The helper lemmas retain explicit comparison premises for reuse, but the
final theorem has exactly the published Prop as its type and no remaining
premises.

Neither this module nor the transport helper imports the arbitrary-scheme
base-change statement, the global reduction, or its unconditional proof.
The parent task can import this affine theorem and the transport helper for
its separate local assembly.

## Sources and provenance

Stacks Project Lemma 29.33.10 (tag
[01V0](https://stacks.math.columbia.edu/tag/01V0)), specialized to
`X = Spec A`, `S = Spec R`, and `S' = Spec B`, is the source assertion.
The map is the one characterized on local differentials in Lemma 29.33.8
(tag [01UV](https://stacks.math.columbia.edu/tag/01UV)). Both statements and
proofs were read in retained `01UM.html`, lines 321–371, of registered source
`stacks-relative-differentials-internal-hom-2026-10-21`, directory content
SHA256 `9c075370ba97d8876785c5486425c6c661765e747452c026583f4dc51f1e1133`.
No relevant public errata file was present in the Library base consulted.

The Stacks proof refers to the sheafified algebraic base-change result
10.131.12 (00RV). The implemented proof instead uses the equivalent
Mathlib tensor differential isomorphism and the explicit compatibilities
above. Mathlib is pinned at commit
`5ed2965256430c3649e86755f9576b54eca72435`; its
`RingTheory/Kaehler/TensorProduct.lean` supplies the algebraic isomorphism
and its formula, and `AlgebraicGeometry/Pullbacks.lean` supplies the
tensor-spectrum pullback isomorphism and projection identities.

Worker 208 implemented the square-map comparison and categorical-pullback
transport. Worker 274 contributed the generator comparison pattern and
the published canonical tilde construction, including its algebra-form
adapter. Worker 538 reused the two helper pairs, discharged the premises
with the published prerequisite proofs, and prepared this exact-target
proof and its explanation.
