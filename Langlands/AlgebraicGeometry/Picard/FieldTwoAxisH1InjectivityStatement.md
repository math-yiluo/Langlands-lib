# Degree-one cohomology of a product over a field is detected on the two axes

Author: Worker 727. The fibrewise branch was assigned by Worker 606, first
executor of task `eab37f2b-d9cf-40e4-86ad-492608a9c630`.

`Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1InjectivityStatement.{u}` is
a `Prop`-valued definition. This module states the injectivity and supplies no
proof. A separate exact-target proof of this proposition is still required.

## Exact interface

The only external parameter is the universe `u`. Inside the proposition the
following data are quantified, in this order.

- A commutative ring `K : CommRingCat.{u}` with `IsField K`. The base scheme is
  `Spec K` itself, not `Spec (CommRingCat.of K')` for a separately given field.
  This form applies directly to Mathlib's residue fields
  `S.residueField s : CommRingCat` and to the base `Spec (S.residueField s)` of
  Mathlib's scheme-theoretic fibre `f.fiber s`.
- Two objects `X Y : Over (Spec K)`, that is schemes `X.left`, `Y.left` with
  structure morphisms `X.hom`, `Y.hom` to `Spec K`. Each structure morphism is
  assumed `Smooth`, `IsProper` and `GeometricallyConnected` (Mathlib's
  properties of scheme morphisms). No group structure, projectivity or
  cohomological hypothesis is assumed.
- Rational points `x₀ : Over.mk (𝟙 (Spec K)) ⟶ X` and
  `y₀ : Over.mk (𝟙 (Spec K)) ⟶ Y`. Their underlying morphisms
  `x₀.left : Spec K ⟶ X.left` and `y₀.left : Spec K ⟶ Y.left` are sections of
  `X.hom` and `Y.hom` by the commutativity condition of `Over`.
- A scheme `P : Scheme.{u}` with morphisms `p₁ : P ⟶ X.left`,
  `p₂ : P ⟶ Y.left` and `hP : IsPullback p₁ p₂ X.hom Y.hom`. So `P` is any
  fibre product `X ×_K Y` with its two projections; the statement does not fix
  a particular construction of the product. Mathlib's `pullback X.hom Y.hom`
  with `pullback.fst`, `pullback.snd`, and the underlying scheme of the product
  `X ⨯ Y` in `Over (Spec K)` are instances.

The proposition then introduces the following local definitions.

- The axes `i₁ : X.left ⟶ P` and `i₂ : Y.left ⟶ P` are
  `i₁ = hP.lift (𝟙 X.left) (X.hom ≫ y₀.left)` and
  `i₂ = hP.lift (Y.hom ≫ x₀.left) (𝟙 Y.left)`, so `i₁ ≫ p₁ = 𝟙`,
  `i₁ ≫ p₂ = X.hom ≫ y₀.left`, `i₂ ≫ p₁ = Y.hom ≫ x₀.left` and
  `i₂ ≫ p₂ = 𝟙`. These are the source's `1 × τ : X → X ×_S Y` and
  `σ × 1 : Y → X ×_S Y` over a field, `x ↦ (x, y₀)` and `y ↦ (x₀, y)`.
- `O = Langlands.Scheme.Modules.structureSheaf P`, the structure sheaf of `P`
  as a module over itself (`SheafOfModules.unit P.ringCatSheaf`).
- `H = DerivedSections.relativeCohomology (p₁ ≫ X.hom) 1 : P.Modules ⥤ ModuleCat K`,
  the Library's first sheaf cohomology of actual `𝒪_P`-modules as `K`-modules,
  via the structure morphism `p₁ ≫ X.hom : P ⟶ Spec K` (module
  `Langlands.AlgebraicGeometry.Modules.DerivedSections`). It is Mathlib's
  right-derived functor of the `K`-module global sections, computed from chosen
  injective resolutions in `P.Modules`.

For `j = 1, 2` let `ηⱼ = (Scheme.Modules.pullbackPushforwardAdjunction iⱼ).unit.app O`,
the unit `O ⟶ iⱼ_* iⱼ^* O` of Mathlib's adjunction
`Scheme.Modules.pullback iⱼ ⊣ Scheme.Modules.pushforward iⱼ`.

The conclusion: every class `c : H.obj O`, that is `c ∈ H¹(P, 𝒪_P)`, with
`(H.map η₁).hom c = 0` and `(H.map η₂).hom c = 0` is zero. Equivalently the
`K`-linear map

```text
H¹(P, 𝒪_P) ⟶ H¹(P, i₁_* i₁^* 𝒪_P) ⊕ H¹(P, i₂_* i₂^* 𝒪_P),   c ↦ (H(η₁) c, H(η₂) c)
```

is injective.

## Relation to the restriction maps of the source

The source states injectivity of the restriction map
`H¹(X × Y, 𝒪) → H¹(X, 𝒪) ⊕ H¹(Y, 𝒪)` along the two axes. The Lean statement
uses, for each axis, the map `H¹(P, η)` induced by the adjunction unit on
cohomology of the total space `P`. This is unconditional functoriality of the
Library's derived functor in its coefficient module; no new pullback map on
cohomology is defined.

The two formulations are equivalent; this equivalence is explanation and is not
part of the Lean statement. For a closed immersion `i` the pushforward `i_*` is
exact, and it sends injective modules to modules with no higher cohomology
(Stacks tags 09SX and 09SY; stated in Lean as
`Langlands.AlgebraicGeometry.Modules.PushforwardInjectiveAcyclicStatement`,
submitted alongside this statement, whose proof is a separate obligation). Hence
`H¹(P, i_* M)` is canonically `H¹` of the source of `i` with coefficients `M`,
and the composite `H¹(P, 𝒪_P) → H¹(P, i_* i^* 𝒪_P) ≅ H¹(X, i^* 𝒪_P) = H¹(X, 𝒪_X)`
is the usual pullback along `i`. The axes are closed immersions because they
are sections of the separated morphisms `p₁` and `p₂`. Since the second map is
an isomorphism, the joint kernel of the Lean maps is the joint kernel of the
source's restriction maps.

## Original source

The Stacks Project, More on Morphisms, Section "Theorem of the cube"
(tag 0BEZ), proof of Lemma `lemma-pic-of-product` (tag 0BF3, Lemma 37.33.7),
retained file `more-morphisms.tex`, lines 9621-9650 (statement 9621-9632, proof
9634-9650). Registered source `stacks-picard-diagonal-seesaw-0bdp-0bf0-a04446e5`
(git commit `a04446e57ec1fbc252a871afcec7752fb2807b14`, folder SHA-256
`b97dd26d238af5bb18d082504515f27f5316b6b87c2a7d68ca8630e7862ad48e`). The
proof begins: "By Künneth (Varieties, Lemma 0BED) the map
`H¹(X_s ×_{Spec κ(s)} Y_s, 𝒪) → H¹(X_s, 𝒪) ⊕ H¹(Y_s, 𝒪)` is injective",
the map being restriction along the two axes `1 × τ` and `σ × 1` on the fibres
over `s`. The Lean statement is this claim for a field `K` in place of `κ(s)`,
with `X`, `Y` in place of the fibres `X_s`, `Y_s` and `x₀`, `y₀` in place of
the fibres of the sections.

The Künneth formula is Stacks, Varieties, Section "Künneth formula, I"
(tag 0BEC), Lemma `lemma-kunneth` (tag 0BED, Lemma 33.29.1), retained file
`varieties.tex`, lines 5441-5457 (proof 5459-5630). Registered source
`stacks-flasque-affine-vanishing-kunneth-a04446e5` (same git commit, folder
SHA-256 `af02e6f0aff875e216f1e0fde58f6baad3eedeb6b82799a8d6c91ff68cccaa3a`).
For a field `k`, quasi-compact `k`-schemes `X`, `Y` with affine diagonal and
quasi-coherent `F`, `G` it gives
`Hⁿ(X ×_k Y, pr₁^* F ⊗ pr₂^* G) = ⊕_{p+q=n} H^p(X, F) ⊗_k H^q(Y, G)`.

### Why the hypotheses suffice

The source lemma 0BF3 assumes the hypotheses of tag 0BDP on the families; over
a field the proof needs only the following, all implied by the Lean hypotheses.

- Künneth applies: a proper morphism is quasi-compact and separated, so `X` and
  `Y` are quasi-compact with closed, hence affine, diagonal.
- `H⁰(X, 𝒪_X) = K = H⁰(Y, 𝒪_Y)`: for smooth proper geometrically connected
  schemes over a field this is the Library proposition
  `Langlands.AlgebraicGeometry.FieldSmoothProperConnectedGlobalFunctions`
  (Stacks tag 0BUG, registered source
  `stacks-global-functions-field-and-fibre-criterion-2026-10-23`).

With `F = 𝒪_X`, `G = 𝒪_Y` and `n = 1`, Künneth gives
`H¹(P, 𝒪_P) = H¹(X, 𝒪_X) ⊕ H¹(Y, 𝒪_Y)` through `pr₁^*` and `pr₂^*`.
Restriction along `1 × y₀` sends `pr₁^* a` to `a` and `pr₂^* b` to
`X.hom^* (y₀^* b)`, which is zero because `H¹(Spec K, 𝒪) = 0`; symmetrically
for `x₀ × 1`. So the joint restriction map is an isomorphism
`H¹(P, 𝒪_P) ≅ H¹(X, 𝒪_X) ⊕ H¹(Y, 𝒪_Y)`, in particular injective. The rational
points are needed: the source uses the sections `σ`, `τ` to define the axes.

Errata: on 2026-10-29 the pages of tags 0BF3 and 0BED had no comments ("Comments
(0)"; retained as `tag-0BF3.html`, `tag-0BED.html` in the folder of
`stacks-flasque-affine-vanishing-kunneth-a04446e5`). No project errata file
exists for either source.

## Intended use

This is the fibre input of the local two-axis criterion
`Langlands.AlgebraicGeometry.Picard.LocalTwoAxisTrivialityStatement` (proof of
Stacks 0BF3 via tag 0BF2), applied with `K = κ(s)` and `P` the fibre of
`X ×_S Y` over `s`; that fibre is a fibre product of the fibres of `X` and `Y`
by pasting of pullback squares.
