# Geometric torsor input from the exact CM normal comparison

This module constructs the original normal residual action as an object of
the coarse represented CM scheme's actual small etale category. Assuming
invertibility of the previously constructed residual coproduct comparison,
it proves unique residual transport between field-valued points in the same
fiber. Together with explicit finite-etale and surjectivity premises, this
supplies exactly the existing `Coefficients.IsFiniteGeometricTorsor`
predicate. No new torsor predicate or coefficient-descent construction is
introduced.

## Fixed represented schemes, original forgetting and residual action

The construction takes a family `R` of the existing
`CMLevelRepresentation` witnesses. For sufficiently small levels `V ≤ U`,
write

```
X_V = (representedCMSchemeTower ... R).obj V,
X_U = (representedCMSchemeTower ... R).obj U,
p   = representedCMNormalProjection ... R U V hVU,
Q   = SmallCMResidualGroup D U V.
```

The witnesses represent the fixed normalized CM class presheaf. They
include admissible schemes over `Spec F`, smoothness, projectivity and
isomorphisms from lifted Yoneda to that presheaf. The scheme tower recovers
its transition maps by fully faithful Yoneda preimage. Thus `p : X_V ⟶ X_U`
is the original forgetting map for the identity-element inclusion
transporter, rather than an additional supplied scheme morphism.

The residual type is the actual quotient
`U.obj.subgroup ⧸ V.obj.subgroup.subgroupOf U.obj.subgroup`. The inclusion
identifies its denominator with `V` inside `U`; relative normality gives
the quotient-group structure. Normality in the entire finite-adelic group
is not required. `smallCMResidualGroup_finite`, proved in the imported
refinement module, establishes finiteness from compactness of `U` and
openness of `V`.

Write `ρ` for the original `representedCMNormalQuotientAction`. Its
underlying scheme maps satisfy the already proved equation `ρ(g) ≫ p = p`.
The action uses the inherited inverse-right convention: a representative
`g` acts through the original transporter with element `g⁻¹`. This converts
the source's right frame-composition action into Mathlib's left categorical
action while retaining the original opposite finite-adelic group.

The imported module `HarrisTaylorCMNormalKernelPair` constructs the actual
scheme coproduct, pullback and morphism

```
κ = representedCMNormalKernelComparison ... R U V hVU :
    (∐ (fun _ : Q => X_V)) ⟶ (X_V ×[X_U] X_V).
```

On summand `g`, this map is the graph of `ρ(g)`, with first projection
identity and second projection `ρ(g)`. The present module assumes
`IsIso κ` only where needed; the imported construction does not prove it.

## Factorization from one-point schemes

The private theorem `existsUnique_coproductFactor` concerns any small family
`X : I → Scheme` and any scheme `Z` with a nonempty subsingleton underlying
point type. For every `f : Z ⟶ ∐ X` it proves

```
∃! i : I, ∃ a : Z ⟶ X i, a ≫ Sigma.ι X i = f.
```

The quantified uniqueness is uniqueness of the summand index. The proof
chooses a point `z` of `Z` and uses the surjectivity of Mathlib's
`AlgebraicGeometry.sigmaMk`, the disjoint-union homeomorphism, to find the
summand containing `f z`. Every point of `Z` equals `z`, so the entire range
of `f` lies in the range of this summand's inclusion.
`IsOpenImmersion.lift` constructs a scheme morphism to that summand and
proves its factorization equation. For any other factorization, evaluation
at `z` and `AlgebraicGeometry.sigmaι_eq_iff` give equality of the summand
indices. The proof uses actual scheme morphisms, not just maps of point
sets. For `Z = Spec Ω` with `Ω` a field, Mathlib supplies the nonempty
subsingleton point type from the unique prime ideal of a field.

## Unique original residual transport

`representedCMNormal_existsUnique_transport` assumes `IsIso κ`. For every
field `Ω` and morphisms `a b : Spec Ω ⟶ X_V` satisfying `a ≫ p = b ≫ p`,
it proves

```
∃! g : Q, a ≫ ρ(g) = b.
```

The proof forms the actual pullback lift `c` of `(a,b)` and sets
`t = c ≫ inv κ`. The private factorization theorem gives a unique summand
`g` and a map `d : Spec Ω ⟶ X_V` whose composite with that summand's
inclusion is `t`. Composing with `κ` identifies `d ≫ graph(g)` with `c`.
The first pullback projection gives `d = a`; the second gives
`a ≫ ρ(g) = b`.

For uniqueness, any `g'` satisfying `a ≫ ρ(g') = b` defines the same
pullback lift by pullback extensionality. Cancellation of the monomorphism
`κ` then shows that `a` followed by the `g'`-summand inclusion also equals
`t`. Uniqueness of the summand index gives `g' = g`.

This argument requires no separable-closure hypothesis on `Ω`. It also
does not use etaleness, finiteness or surjectivity of `p`. Those separate
premises are needed to supply the full existing geometric-torsor predicate.

## The actual small etale action and torsor implication

Under exactly `Etale p`, `representedCMNormalEtaleAction` is an

```
Action X_U.Etale Q.
```

Its object is `Scheme.Etale.mk p`. Each action map is the original
`ρ(g)`, bundled as a morphism over `X_U` using the proved invariant
projection equation. Extensionality for morphisms in the over category
reduces the identity and multiplication laws to those of the original
action. No action law or equivariance equation is a new hypothesis.

The lemmas `representedCMNormalEtaleAction_left`,
`representedCMNormalEtaleAction_hom` and
`representedCMNormalEtaleAction_ρ_left` are definitional equalities:
the fine scheme is exactly `X_V`, its structural map is exactly `p`, and
its action maps are exactly the original inverse-right residual
translations.

`representedCMNormalEtaleAction_isFiniteGeometricTorsor` takes the following
precise additional premises on these same maps:

- `Etale p`;
- `IsFinite p`;
- `IsIso κ`;
- `Function.Surjective p` on the underlying scheme points.

It concludes
`Coefficients.IsFiniteGeometricTorsor X_U (representedCMNormalEtaleAction ...)`
from `Langlands.Shimura.Coefficients.Etale`. That existing predicate
requires a finite acting group, a finite and surjective structural map,
and unique residual transport on every fiber of separably closed
field-valued points. Etaleness is already part of its input action's
object in `X_U.Etale`.

The proof supplies the imported residual-group finiteness theorem, the
stated finiteness and surjectivity of `p`, and the preceding transport
theorem specialized to separably closed fields. It constructs the exact
existing predicate, with no supplied geometric-fiber conclusion.
It proves an implication from the listed premises; it does not prove
that those premises hold for the CM tower.

For `q : CMRepresentabilityStatement ...`,
`cmNormalEtaleAction` applies the same construction to
`chosenCMLevelRepresentation ... q`. Its structural map is the original
forgetting map of the corresponding `cmSchemeTower`.
`cmNormalEtaleAction_isFiniteGeometricTorsor` supplies the same implication
for these exact chosen witnesses. The choice comes from precisely the
existing representability target and does not select unrelated schemes.

## Source, explicit inputs and remaining obligations

The source is Harris and Taylor, *The Geometry and Cohomology of Some
Simple Shimura Varieties* (2001), III.1, printed p.91, one-based PDF p.99,
registered as `harris-taylor-2001-geometry-cohomology-simple-shimura`,
SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The passage defines monodromy-invariant orbits of pairing-compatible
adelic frames, right translation by frame composition, natural
finite-etale forgetting and the normal-level Galois-cover assertion with
group `U/V`. The factorization, transport and small-etale packaging here
are derived categorical prerequisites for that assertion. They are not
formulas attributed verbatim to the source or a proof of its existence
and cover theorems.

The actual arithmetic inputs remain the totally real number field `E`,
CM number field `F` quadratic over `E`, central simple unitary datum `D`,
imaginary quadratic field `L` inside `F`, embedding `τ₀`, and
CM-compatible Harris signature charts `C`. The named prerequisites remain
explicit: pullback-tensor preservation, composition, unit coherence,
associativity, unitor comparison and symmetry; Picard-zero pullback
stability, Mumford-square and universal base change; duality naturality,
polarization base change, relative finite Weil transition, the rational
profinite-integer/adele comparison and torsion finite etaleness. None is
proved by this module.

The representing witnesses still lie in the existing
`ComponentwiseAdmissibleCMBaseCategory` over `Spec F`. Its inherited
local Noetherian, connected-component and geometric-point prerequisites
are retained. Representability is asserted only as the explicit
existing target for that restricted presheaf. The transport theorem is
a theorem about field-valued morphisms to the resulting actual schemes;
it does not extend the presheaf's represented test category.

Applicable existence under the source's division and global conditions,
comparison with the original moduli problem, finite etaleness and
surjectivity of original forgetting, and invertibility of the exact `κ`
remain separate proof obligations. Isomorphisms comparing different
representing witnesses in the imported module do not establish
invertibility of `κ`. Canonical-model comparison, uniformization and
the coefficient-descent comparison are not proved here. The generic
small-etale and coefficient constructions are reused from their existing
modules; this pair adds only the specific CM action and the proved
conditional torsor implication.

All code and prose in this pair are by Worker 57. The pinned environment
is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
