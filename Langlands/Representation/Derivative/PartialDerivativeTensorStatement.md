# Partial derivative of an exterior tensor product (statement)

Author: Worker 749.

This module states Zelevinsky's Proposition 3.7(a) for every pair of natural
ranks. The statement is a natural isomorphism between two actual functors on
the product category. The module also defines the elementary functors the
statement needs: the raw binary exterior tensor product, the first-factor
tensor product and the top derivative. No proof of the comparison is supplied;
the definition below is a proposition, not a theorem.

## Principal proposition

For `p : ℕ` with `[Fact p.Prime]`, `F : PadicField.{uF} p` (explicit) and
`T : F.TopologicalData`,
`Langlands.Derivative.PartialDerivativeTensorStatement.{uF,uV} F T` is

```
letI := T.topology
∀ (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (k m : ℕ),
  Nonempty (exteriorTensor.{uF,uV} T k m ⋙ partialDerivative T ψ k m ≅
    firstFactorTopDerivative T ψ k m)
```

Both sides are functors

```
SmoothRep.{0,uF,uV} ℂ (GeneralLinear k F.Carrier) ×
    SmoothRep.{0,uF,uV} ℂ (GeneralLinear m F.Carrier) ⥤
  SmoothRep.{0,uF,uV} ℂ (GeneralLinear k F.Carrier).
```

`≅` is an isomorphism in the functor category. Its components are actual
isomorphisms of smooth representations, that is, equivariant linear maps with
equivariant inverses. Its naturality square holds for every morphism `(f, g)`
of the product category, so it is natural in both variables at once. The same
`ψ` and the same topology `T.topology` enter both sides. The level parameters
are `[uF, uV]` in that order, and the result type is `Prop`.

The left side is the ordinary exterior tensor product followed by the
published partial derivative
`Langlands.Derivative.partialDerivative T ψ k m` from
`Langlands.Representation.Derivative.Partial`. The right side sends `(A, B)` to
`A ⊗[ℂ] D_m(B)`, with `GL_k` acting through `A` only, where

```
D_m = topDerivative T ψ m
    = generalLinearDerivative T ψ m m (Nat.le_refl m) ⋙
        generalLinearRankCast T (Nat.sub_self m)
```

is the published order-`m` derivative of `Langlands.Representation.Derivative.Iteration`
followed by the published rank transport from `GL_(m-m)` to `GL_0`.
`D_m(B)` is the whole carrier of that actual smooth `GL_0` representation. No
one-dimensional model or chosen basis replaces it.

## Helper definitions

The generic helpers are in namespace `Langlands.Derivative.PartialTensor`. They
work for groups `G H : Type uG` and complex vector spaces whose universes are
all independent.

| Declaration | Meaning |
| --- | --- |
| `exterior ρ σ` | `Representation.tprod (ρ.comp (MonoidHom.fst G H)) (σ.comp (MonoidHom.snd G H))` on `V ⊗[ℂ] W` |
| `exterior_tmul` | `(g, h) (v ⊗ w) = ρ g v ⊗ σ h w` (`rfl`) |
| `exteriorMap f g` | Mathlib's `IntertwiningMap.tensor` of `f` and `g` lifted along the projections |
| `exteriorMap_toLinearMap`, `exteriorMap_tmul` | Its linear map is `TensorProduct.map f.toLinearMap g.toLinearMap` (`rfl`) |
| `exteriorMap_id`, `exteriorMap_comp` | Identity and composition laws, from `TensorProduct.map_id` and `map_comp` |
| `firstFactor ρ W` | `Representation.tprod ρ (Representation.trivial ℂ G W)`: `G` acts on `V ⊗[ℂ] W` through `V` |
| `firstFactor_tmul` | `g (v ⊗ z) = ρ g v ⊗ z` (`rfl`) |
| `firstFactorMap f h` | `IntertwiningMap.tensor` of `f` with an arbitrary linear map `h` |
| `firstFactorMap_toLinearMap`, `firstFactorMap_tmul` | Its linear map is `TensorProduct.map f.toLinearMap h` (`rfl`) |
| `firstFactorMap_id`, `firstFactorMap_comp` | Identity and composition laws |
| `isSmoothVector_exterior_tmul`, `isSmooth_exterior` | Smoothness of the exterior tensor product |
| `isSmoothVector_firstFactor_tmul`, `isSmooth_firstFactor` | Smoothness of the first-factor tensor product |
| `exteriorFunctor` | `SmoothRep.{0,uG,uV} ℂ G × SmoothRep.{0,uG,uV} ℂ H ⥤ SmoothRep.{0,uG,uV} ℂ (G × H)` |
| `firstFactorFunctor` | `SmoothRep.{0,uG,uV} ℂ G × SmoothRep.{0,uG,uV} ℂ H ⥤ SmoothRep.{0,uG,uV} ℂ G` |

`exteriorFunctor` sends `(A, B)` to the smooth representation `exterior` of
`A` and `B`. It sends `(f, g)` to `exteriorMap` of the underlying intertwiners
`SmoothRep.hom f` and `SmoothRep.hom g`. `firstFactorFunctor` sends `(A, B)` to
`firstFactor A.representation B`, which keeps the carrier of `B` and forgets
its `H`-action. It sends `(f, g)` to `firstFactorMap (SmoothRep.hom f)
(SmoothRep.hom g).toLinearMap`. Both functors prove their identity and
composition laws through `TensorProduct.map_id` and `TensorProduct.map_comp`.

Smoothness uses the predicate of `Langlands.Representation.Smooth.Definitions`.
A pure tensor `v ⊗ w` of smooth vectors is fixed by `K.prod L`, where `K` and `L`
are open subgroups fixing `v` and `w`. Mathlib's `OpenSubgroup.prod` makes this
an open subgroup of the product topology. For the first-factor action, `v ⊗ z`
is fixed by any open subgroup fixing `v`. Pure tensors span the tensor product
(`TensorProduct.inductionOn`), and smooth vectors are closed under addition
(`isSmoothVector_add` from `Smooth.SmoothPart.BasicProof`). No topology is put
on any vector space, and no finite dimension is assumed.

The specialized definitions are in namespace `Langlands.Derivative`, with `F`
implicit and `letI := T.topology` installed:

| Declaration | Meaning |
| --- | --- |
| `exteriorTensor T k m` | `PartialTensor.exteriorFunctor` for `GL_k × GL_m` with the product topology |
| `topDerivative T ψ m` | `D_m` above, `GL_m ⥤ GL_0` |
| `firstFactorTopDerivative T ψ k m` | `(𝟭 _).prod (topDerivative T ψ m) ⋙ PartialTensor.firstFactorFunctor` |

The unfolding lemmas, all proved by `rfl`, record the required data:

- `exteriorTensor_obj_carrier`: the carrier of `(exteriorTensor T k m).obj X`
  is `X.1 ⊗[ℂ] X.2`;
- `exteriorTensor_action_tmul`: `(g, h)` acts on `v ⊗ w` by
  `X.1.representation g v ⊗ X.2.representation h w`;
- `exteriorTensor_map_toLinearMap`: the image of `f` has linear map
  `TensorProduct.map (SmoothRep.hom f.1).toLinearMap (SmoothRep.hom f.2).toLinearMap`;
- `topDerivative_eq`: `topDerivative T ψ m` is the displayed composite;
- `topDerivative_zero`: `topDerivative T ψ 0` is the identity functor of
  `SmoothRep.{0,uF,uV} ℂ (GeneralLinear 0 F.Carrier)`;
- `firstFactorTopDerivative_obj_carrier`: the carrier is
  `X.1 ⊗[ℂ] (topDerivative T ψ m).obj X.2`;
- `firstFactorTopDerivative_action_tmul`: `g` acts on `v ⊗ z` by
  `X.1.representation g v ⊗ z`;
- `firstFactorTopDerivative_map_toLinearMap`: the image of `f` has linear map
  `TensorProduct.map (SmoothRep.hom f.1).toLinearMap (SmoothRep.hom ((topDerivative T ψ m).map f.2)).toLinearMap`.

## Sources

Zelevinsky, *Induced representations of reductive p-adic groups II.
Irreducible representations of GL(n)* (1980), `zelevinsky-1980-induced-ii`,
SHA256 `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`,
`/home/taskhub/central-library/Zelevinsky--Induced representations of reductive p-adic groups II, irreducible representations of GL(n)--1980.pdf`.
§3.7 and its Proposition are on printed p.182, one-based PDF page 19. The page
was rendered and visually inspected. For integers `k, m ≥ 0`, Zelevinsky lets
`U` be the upper unipotent matrices in `G_m = {e} × G_m ⊂ G_k × G_m = G_(k,m)`.
He defines `θ((u_ij)) = ψ(Σ_{1≤i≤m-1} u_(k+i,k+i+1))` and sets
`∂ = r_{U,θ} : Alg G_(k,m) → Alg G_k`. The printed formula drops the symbol
`ψ` before the parenthesis, but the next sentence names `ψ` as the additive
character used for derivatives. Proposition (a) reads: if `σ ∈ Alg G_k` and
`τ ∈ Alg G_m` then `∂(σ ⊗ τ) = σ ⊗ τ^(m) ∈ Alg(G_k × G_0) = Alg G_k`. The page
says the Proposition follows from the definition of the `m`-th derivative and
BZ77 1.9(c),(g). Part (b), the comparison of the `m`-th derivative with
`∂ ∘ r_{(k,m),(n)}`, is not stated here.

Bernstein–Zelevinsky, *Induced representations of reductive p-adic groups I*
(1977), `bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`,
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.
The following parts were read:

- §1.8(b), printed pp.444–445 / PDF5–6: `E(U,θ)` is spanned by
  `π(u)ξ - θ(u)ξ`, and `r_{U,θ}(E) = E/E(U,θ)` carries the action
  `mod_U^(-1/2)(m) π(m)` of `M`.
- Proposition 1.9(c), printed p.445 / PDF6: transitivity of localizations,
  `r_{V,θ'} ∘ r_{U,θ} = r_{U°,θ°}` with `U° = UV` and
  `θ°(uv) = θ(u)θ'(v)`.
- Proposition 1.9(g), same page: `r_{U,θ}` commutes with the functors
  `ξ ↦ ξ ⊗ τ` and `ξ ↦ τ ⊗ ξ` for a representation `τ` of another group `H`.
- §3.5, printed p.452 / PDF13: `τ^(k) = Ψ⁻ ∘ (Φ⁻)^(k-1)(τ)` for
  `τ ∈ Alg P_n`; §4.3, printed p.454 / PDF15: `π^(0) = π` and
  `π^(k) = (π|_(P_n))^(k)` for `π ∈ Alg G_n`.

Both hashes were verified. No errata file for either source was found in the
project literature folder, the central library or the public notes. This is a
bounded check, not an assertion that no errata exist.

## Correspondence with the source

- **Exterior tensor.** Zelevinsky's `σ ⊗ τ ∈ Alg G_(k,m)` is the ordinary,
  unnormalized exterior tensor product, implemented by `exteriorTensor`. It is
  not normalized parabolic induction `σ × τ`; there is no induction, modulus
  character or `ULift` in this functor.
- **Partial derivative.** `partialDerivative T ψ k m` is the published
  quotient of the carrier by the span of `ρ(1,u)x - θ(u)x`, `u` upper
  unipotent in the second factor, where `θ` is the published
  `Whittaker.entrywiseCharacter ψ.complex m`, the full nondegenerate
  character on all of `U_m`. It carries the descended action of
  `g ↦ (g,1)`. The first factor commutes with `{1} × U_m`, so
  `mod_U = 1` on it and BZ77's inverse-half factor is trivial. That is why the
  published functor has no first-factor twist. This is recorded in the
  `Partial` Markdown.
- **Top derivative.** Zelevinsky's `τ^(m)` is BZ77's `m`-th derivative, an
  object of `Alg G_0`. In the Library, `generalLinearDerivative T ψ m m` is
  the identity for `m = 0`. For `m > 0` it is restriction to the mirabolic
  subgroup followed by `Ψ⁻ ∘ (Φ⁻)^(m-1)`, made from the published
  determinant-normalized minus functors. Each `Φ⁻` localizes at the
  last-column character of its radical and then twists by `|det|^(-1/2)` on
  the output mirabolic group. The final `Ψ⁻` localizes at the trivial
  character and twists by `|det|^(-1/2)` on the output `GL`. Its target is
  `GL_(m-m)`. The published `generalLinearRankCast T (Nat.sub_self m)` moves
  it to `GL_0`, which is the transport needed because `m - m` is not
  definitionally `0` for a variable `m`. `topDerivative` is exactly this
  composite. The actual normalized derivative is used; no untwisted quotient
  replaces it.
- **Why the two sides should agree.** This explains the source assertion and
  is not proved here. By 1.9(g), on `σ ⊗ τ` the partial-derivative relations
  are `v ⊗ (τ(u)w - θ(u)w)`, so the quotient is `σ ⊗ τ_{U_m,θ}`. By 1.9(c),
  the iterated last-column quotients of the top derivative compose to the
  quotient of `τ` at the full upper unipotent group with the product
  character. The intermediate determinant twists are characters of the
  intermediate groups that are trivial on their unipotent radicals. They do
  not change the later relation spans, and they are invisible on the trivial
  group `GL_0`. Identifying the Library's iterated last-column characters with
  the entrywise character, including the inverse-half normalization and the
  rank-one boundary, is the shared top-localization comparison discussed
  below. It is not assumed here.
- **`Alg(G_k × G_0) = Alg G_k`.** `GL_0` has exactly one element, so its
  action on `D_m(B)` is the identity. `firstFactorFunctor` forgets that action
  and keeps the entire carrier and the actual linear maps
  `SmoothRep.hom (D_m.map g)`. `GL_k` acts by `g (v ⊗ z) = g v ⊗ z`.
- **Equality as natural isomorphism.** Zelevinsky writes `=`. Here it is
  formalized as a natural isomorphism of actual functors on the product
  category. It is not an isomorphism-class equality, a Grothendieck-group
  identity or an objectwise statement. Choosing this categorical form is an
  internal formalization decision.

## Ranks and boundary cases

Every `k, m : ℕ` is quantified, including `k = 0`, `m = 0`, `k = m = 0` and
`m = 1`. Instances are obtained by specialization; this was checked with a
private scratch file.

- `m = 0`: `topDerivative T ψ 0` is the identity functor (`topDerivative_zero`,
  `rfl`), matching `τ^(0) = τ`. The right side is then `(A, B) ↦ A ⊗[ℂ] B` with
  an arbitrary `GL_0` representation `B` and all its tensor multiplicities.
  The published `partialDerivativeZeroIso` shows the left side retains the
  entire original carrier.
- `m = 1`: by the published `generalLinearDerivative_one_one`, `D_1` is
  `generalLinearRestriction T 0 ⋙ Mirabolic.psiMinus T 0` after an identity
  rank transport.
- `m = n + 1`: by the published `generalLinearDerivative_top_succ`, `D_m` is
  `generalLinearRankCast T (Nat.zero_add (n+1)).symm ⋙ generalLinearDerivativePositive T ψ 0 n`.
- `k = 0`: the first factor is an arbitrary smooth representation of `GL_0`,
  that is, an arbitrary complex vector space. It is not replaced by `ℂ`.

There are no positivity, finite length, admissibility, irreducibility,
genericity, nonzero-object or finite-dimension assumptions.

## Universes and carriers

All carriers stay in the unsaturated universe `Type uV`. The tensor product of
two `Type uV` spaces is again `Type uV`, so no `ULift` and no `max uF uV`
appears. The groups `GL_k`, `GL_m` and `GL_k × GL_m` live in `Type uF`, and
`uF` and `uV` are independent. The scratch check instantiated the proposition
at `.{0,3}`. The generic `PartialTensor` laws allow independent carrier
universes for the three objects of a composition.

## Provenance of the local packaging

The raw exterior tensor helpers are derived from Mathlib's
`Representation.tprod`, `Representation.IntertwiningMap.tensor`,
`TensorProduct.map_id`, `TensorProduct.map_comp`, `TensorProduct.inductionOn`
and `OpenSubgroup.prod`. The project supplies the smoothness predicate and
`isSmoothVector_add`. These helpers are internal constructions.

The local `firstFactor` and `firstFactorMap` definitions delegate to the existing
`Langlands.BinaryTensor` constructions, and `isSmooth_firstFactor` reuses their
smoothness theorem. These generic declarations are now in
[Tensor representations with one acting factor](../Tensor/OneFactor.md),
extracted unchanged from `Induction/BinaryProduct`. This preserves the formulas,
independent carrier universes and local interfaces without importing binary
normalized induction or its rank-zero conventions.

`FiniteTensor.externalFunctor` from `Langlands.Representation.Tensor.Finite`
uses `PiTensorProduct` over an index type and the product group `∀ i, H i`.
Transporting it to `GL_k × GL_m` would need two-factor equivalences for both
the groups and the tensor modules, so the raw binary exterior functor remains
local to this module.

This module defines no quotient equivalence. It does not duplicate
`FiniteTensor.characterLocalizationEquiv` from
`Langlands.Representation.Tensor.CharacterLocalization`, which a proof may
reuse.

## Imports and independence

The module imports `Langlands.Representation.Derivative.Partial`,
`Langlands.Representation.Derivative.Iteration` and
`Langlands.Representation.Tensor.OneFactor`, which imports
`Smooth.SmoothPart.BasicProof`. The transitive `Langlands` import closure has
61 modules. They cover GL groups and their
mirabolic and unipotent subgroups, local fields, harmonic-analysis
characters, the smooth category, twists, Jacquet localization, the
Whittaker entrywise character, the mirabolic minus functors and the two
derivative constructions. The original 60-module closure was checked against
Library commit `d8292e5e2ee514f9410e96a37b722b57f1e9de93`. Integration adds only
the extracted `Tensor.OneFactor` module to that closure. Every module retains
nonempty paired Markdown; the existing one-factor declarations are moved with
their documentation, with no change of mathematical meaning.

The closure contains no segment, multisegment, socle, head, square-integrable,
tempered, classification, exhaustion, supercuspidal, coinvariant-finiteness or
binary-induction module. A text scan of every closure source found none of
the excluded declarations. The scan covered `SegmentHeadProductIrreducibility`,
`GenericSegmentProductUniqueness`, `SquareIntegrableLanglandsClassification`,
`UnlinkedSegmentSocleProductIrreducible`,
`LinkedSegmentSocleReverseProductStructure`, `LinkedSegmentSoclePairReducible`,
`SegmentSocleProductIrreducibility`,
`TwoSupercuspidalNonadjacentProductIrreducible`,
`TwoSupercuspidalProductStructure`,
`SegmentSpecialEssentialSquareIntegrability`,
`OrderedMultisegmentSocleExistence`, `MultisegmentSocleExhaustion`, the
segment Jacquet formulas, `IrreducibleCoinvariantFinitenessStatement`,
`LeviCuspidalCoinvariantFinitenessStatement`,
`SupercuspidalCoinvariantFinitenessStatement` and `SupercuspidalDerivatives`.
The closure includes `Whittaker.PrerequisitesStatement` through the entrywise
character. That is a proposition definition only, and nothing here uses it
as a proved input. No derivative, plus-functor, adjunction, duality,
filtration, pairing, segment or classification theorem is imported or used,
and none of the excluded tasks or their conclusions enters this unit.

## Scope, ownership and proof

This unit states the comparison only. The actual partial and ordinary
derivative constructions are used as definitions; they are not comparison
proofs. The intended exact proof successor targets this unchanged proposition,
with proposed module `Langlands.Representation.Derivative.PartialDerivativeTensorProof`
and theorem `Langlands.Derivative.partialDerivativeTensor`. It will construct
the natural isomorphism from the concrete tensor quotient and an
independently accepted top-localization comparison. The `k = 0`
top-localization adapter is arranged with Worker 288's task
`62de5903-b616-4b5c-88eb-a066b77c5467`. The positive two-block Jacquet
comparison is Worker 357's task `087df35f-27e7-46d2-b882-e873faefe447`.
Worker 710 owns the minus-normalization bridge `cc7a2ee5-94fa-4f70-bad6-23a025910130`.
These are coordination pointers. None of them is a premise of this proposition
or a proved input.

Environment: `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
