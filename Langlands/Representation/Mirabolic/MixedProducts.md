# The mixed mirabolic products of BZ77 §4.12(II) and (III)

Author: Worker 837. Main declarations:
`Langlands.PadicField.TopologicalData.leftMixedProductFunctor` and
`Langlands.PadicField.TopologicalData.rightMixedProductFunctor`.

This pair constructs the two actual products of smooth complex representations
in cases (II) and (III) of Bernstein–Zelevinsky, *Induced representations of
reductive p-adic groups I* (1977), source ID
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`. The passages
read are §1.8 (printed p.444, PDF p.5), which defines normalized induction
`i_(U,θ)`, and §4.12 (printed pp.456–458, PDF pp.17–19). The page images of
printed pp.457–458 were inspected, including the three block diagrams and the
case (III) twist `ε(m₁,m₂) = ν(m₂)^(-1/2)`, which text extraction loses. A
bounded search of the Library `notes/` tree and the project notes found no BZ77
errata file. This reports that search only; it does not claim that no errata
exist elsewhere.

## Source scheme

BZ77 §4.12 defines each product `Alg M₁ × Alg M₂ → Alg G` as `i ∘ ⊗`, with
`M = M₁ × M₂` embedded in `G` and `i = i_(U,1) ∘ ε` for a subgroup `U` and a
character `ε` of `M`. By §1.8 a vector of `i_(U,1)(ρ)` is a function
`f : G → L` with `f(umg) = mod_U^(1/2)(m) ρ(m) f(g)`, one open subgroup of right
stabilizers, compact support modulo `MU`, and right-translation action. In case
(II), `M₁ = GL_k`, `M₂ = P_m`, `G = P_n`, `ε = 1`. In case (III),
`M₁ = P_m`, `M₂ = GL_k`, `G = P_n` and `ε(m₁,m₂) = ν(m₂)^(-1/2)`. Here
`n = k + m`, and the Lean rank `r` is `m - 1`.

## Groups, topologies and universes

All declarations quantify over `{p : ℕ} [Fact p.Prime]`, `F : PadicField.{uF} p`,
the supplied `T : F.TopologicalData`, and arbitrary `k r : ℕ`. The source's
`GL_k` is `GeneralLinear k F.Carrier`. The source's `P_(r+1)` is the published
`mirabolic r F.Carrier`. The common target is `mirabolic (k + r) F.Carrier`, of
matrix rank `k + r + 1`. Every topology is the one induced by `T.topology` on
matrix units, then on the mirabolic subgroup and its subgroups; group
continuity comes from `T.generalLinearTopologicalGroup (k + r + 1)`. `T` is not
replaced by a canonical realization.

The inducing subgroups, projections, sections, kernels and rectangle actions
are the published ones in `Langlands.Group.GL.MirabolicMixedProductSubgroups`,
used unchanged: `leftSubgroup`, `leftProjection : leftSubgroup k r →
GL_k × P_(r+1)` and `left_conjugate` (`Z ↦ a Z p⁻¹` on `k × (r+1)`
rectangles) in case (II). Case (III) uses `rightSubgroup`,
`rightProjection : rightSubgroup k r → P_(r+1) × GL_k` and `right_conjugate`
(`X ↦ d X a⁻¹` on `r × k` rectangles, `d = Mirabolic.projection p`). The case
(III) embedding uses the first `r` and the final coordinate for the mirabolic
block. It is not the consecutive embedding.

Inputs are `SmoothRep.{0, uF, uV}` objects with carriers in `Type uV`, for an
independent universe `uV`; no relation between `uF` and `uV` is assumed.
Outputs are `SmoothRep.{0, uF, max uF uV}`. The inspected level parameters of
both functors are `[uF, uV]`. Carriers may be infinite-dimensional.

## The binary external tensor product

Namespace `Langlands.MixedProductTensor` contains a binary tensor model; the
contract permits it in place of `FiniteTensor.externalFunctor`.
`external ρ σ = Representation.tprod (ρ ∘ fst) (σ ∘ snd)` is the action of
`G × H` on `V ⊗[ℂ] W`. On pure tensors,
`external_tmul : external ρ σ (g, h) (v ⊗ₜ w) = ρ g v ⊗ₜ σ h w`.
`externalMap f g` is `TensorProduct.map f g`, with `externalMap_tmul`,
`externalMap_id` and `externalMap_comp`. `isSmooth_external` proves smoothness:
`v ⊗ w` is fixed by `K.prod L` for open stabilizers `K` of `v` and `L` of `w`,
and smooth vectors are closed under addition. `externalFunctor` bundles this as a
functor `SmoothRep G × SmoothRep H ⥤ SmoothRep (G × H)` with carrier `V ⊗ W` in
`Type uV`. Its identity and composition laws are proved from
`TensorProduct.map_id` and `TensorProduct.map_comp`. Neither factor is collapsed
in any rank.

`pullbackFunctor φ hφ` pulls a smooth representation back along a continuous
homomorphism, with smoothness from the published `isSmooth_comp`; maps are
unchanged (`pullbackMap`). `lift`, `liftEquiv`, `liftMap`, `isSmooth_lift` and
`liftFunctor` move a carrier `V` to `ULift V` by `ULift.up`/`ULift.down`.
`unitTensorLeft W : ULift ℂ ⊗ W ≃ W` and `unitTensorRight V : V ⊗ ULift ℂ ≃ V`
send `c ⊗ w` and `v ⊗ c` to `c.down • w` and `c.down • v`. They come with
inverse formulas and naturality in the other factor (`unitTensorLeft_naturality`,
`unitTensorRight_naturality`). `externalUnitLeftEquiv` and
`externalUnitRightEquiv` show these are equivariant when the line carries the
trivial action. `twistOneEquiv` is the identity map from a twist by a character
equal to `1`. `compEquiv` pulls an equivalence back along a homomorphism.
`smoothRep_hom_ext` identifies morphisms with equal underlying maps.

The five helpers `pullbackMap`, `compEquiv`, `lift`, `liftEquiv` and `liftMap`
are compatibility abbreviations for the existing `Langlands.BinaryTensor`
constructions in [BinaryProduct](../Induction/BinaryProduct.md). The first two
put the group homomorphism first; all five retain the same underlying maps and
independent universes. Their implementations are shared with the binary
normalized product.

`Langlands.GeneralLinear.Mirabolic.MixedProduct.leftInducingRepresentation σ τ`
is `external σ τ` pulled back along `leftProjection`. Thus
`leftInducingRepresentation_apply` gives `h ↦ σ(a) ⊗ τ(p)` for
`(a,p) = leftProjection h`. `leftInducingRepresentation_leftMatrix` evaluates it
on `leftMatrix a p Z` as `TensorProduct.map (σ a) (τ p)`.
`leftInducingRepresentation_of_mem_leftKernel` and `_leftUnipotent` prove that
the actual radical acts trivially. `rightInducingRepresentation τ σ`, with its
`_apply`, `_tmul`, `_rightMatrix`, `_of_mem_rightKernel` and
`_rightUnipotent` laws, is the case (III) analogue along `rightProjection`.
`isSmooth_leftInducingRepresentation` and
`isSmooth_rightInducingRepresentation` derive smoothness from the continuous
published projections.

## The explicit total characters

Write `ν_n = T.determinantNorm n`, the published residue-normalized character
`g ↦ |det g|_F`; real powers use the published `realPowerCharacter`. Ranks are
cast to `ℝ` before division or negation.

- `T.leftLeviCharacter k r : GL_k × P_(r+1) →* ℂˣ` is
  `ν_k(a)^(((r+1 : ℕ) : ℝ)/2) · ν_(r+1)(p.val)^(-((k : ℝ)/2))`
  (`leftLeviCharacter_apply`).
- `T.rightLeviCharacter k r : P_(r+1) × GL_k →* ℂˣ` is
  `ν_r(d)^((k : ℝ)/2) · ν_k(a)^(-(((r+1 : ℕ) : ℝ)/2))` with
  `d = Mirabolic.projection p` (`rightLeviCharacter_apply`).

These are the source-prescribed total covariance characters. The derivation
uses the published rectangle actions; it is documentation, not a formal theorem
here. In case (II), `left_conjugate` gives the action `Z ↦ a Z p⁻¹` on
`k × (r+1)` matrices. This linear map has determinant
`det(a)^(r+1) det(p)^(-k)`, so the corresponding module is
`ν_k(a)^(r+1) ν_(r+1)(p)^(-k)`. Its positive square root is `χ_L`, and
`ε = 1`. In case (III), `right_conjugate` gives `X ↦ d X a⁻¹` on `r × k`
matrices. Its determinant is `det(d)^k det(a)^(-r)`, with square root
`ν_r(d)^(k/2) ν_k(a)^(-r/2)`. Multiplying by the retained
`ε = ν_k(a)^(-1/2)` gives `χ_R`. The formal statement
`rightLeviCharacter_eq_mul` proves
`rightLeviCharacter = rightRectangleHalfCharacter * rightEpsilonCharacter`,
where the two factors are exactly these two characters. No formal equality
between these determinant powers and an actual Haar-measure modulus is
asserted, assumed or imported. Any such identification needs its own reviewed
statement and proof.

`T.leftCharacter k r` and `T.rightCharacter k r` are genuine
`Induction.SmoothCharacter ℂ` values on the actual inducing subgroups. Each is
the corresponding Levi character composed with the published projection
(`leftCharacter_apply`, `rightCharacter_apply`). Their open kernels are proved,
not supplied. `isOpen_ker_leftLeviCharacter_comp` and
`isOpen_ker_rightLeviCharacter_comp` show that the kernel contains the
intersection of the preimages of the published open kernels
`T.isOpen_ker_determinantNorm`. The preimages are taken along the continuous
published projections, and also along the subtype or `Mirabolic.projection` map.
A real power is `1` wherever its positive character is `1`. Value formulas:
`leftCharacter_leftMatrix`, `leftCharacter_leftSection`,
`rightCharacter_rightMatrix` and `rightCharacter_rightSection`. Triviality on the
actual radical: `leftCharacter_of_mem_leftKernel` and
`rightCharacter_of_mem_rightKernel`.

Boundary ranks: `leftLeviCharacter_zero_left` and
`rightLeviCharacter_zero_left` prove that both characters are `1` when `k = 0`.
Here `ν_0 = 1` because `GL_0` is trivial, and the other exponent is `0`.
`leftCharacter_zero_left` and `rightCharacter_zero_left` give the same statement
on the subgroups. For `r = 0`, `leftLeviCharacter_zero_right_apply` gives
`χ_L(a,p) = ν_k(a)^(1/2)`, since `P_1` is trivial.
`rightLeviCharacter_zero_right_apply` gives `χ_R(p,a) = ν_k(a)^(-1/2)`, since
`ν_0(d) = 1`. Thus at `r = 0` the right product still twists by the inverse-half
power coming from `ε`.

## The products

```text
leftMixedProductFunctor k r :
  SmoothRep.{0,uF,uV} ℂ (GeneralLinear k F.Carrier) ×
    SmoothRep.{0,uF,uV} ℂ (mirabolic r F.Carrier) ⥤
  SmoothRep.{0,uF,max uF uV} ℂ (mirabolic (k + r) F.Carrier)

rightMixedProductFunctor k r :
  SmoothRep.{0,uF,uV} ℂ (mirabolic r F.Carrier) ×
    SmoothRep.{0,uF,uV} ℂ (GeneralLinear k F.Carrier) ⥤
  SmoothRep.{0,uF,max uF uV} ℂ (mirabolic (k + r) F.Carrier)
```

Each is the composite of four genuine functors: `externalFunctor`, then
`pullbackFunctor` along the published projection, then `SmoothRep.toRep`, then
the published `Induction.normalizedCompactInductionFunctor` for the inducing
subgroup and `T.leftCharacter k r` (respectively `T.rightCharacter k r`). Each
total character is used exactly once, as the twist inside that published
functor. The identity and composition laws are those of the composite; they are
proved, not taken as parameters. Morphisms of the product categories are pairs
of intertwiners.

`leftMixedProductFunctor_obj` states that each object is the published
`Induction.normalizedCompactInduced` of `leftInducingRepresentation`, bundled
with `Induction.compactInduced_smooth`. `leftMixedProductFunctor_map` states
that each map is `Induction.compactInducedMap` of the twisted, pulled-back
`externalMap`. The right versions are analogous. A vector `f` has values
`T.leftMixedEval X f x ∈ A ⊗ B` (respectively `T.rightMixedEval X f x ∈ B ⊗ A`).
These are actual functions on `P_(k+r+1)`, and `*_injective` says the values
determine the vector. The usable formulas are:

- covariance (`leftMixedEval_covariant`): for `h` in the subgroup,
  `f(h x) = (χ_L(leftProjection h) : ℂ) • (A ⊠ B)(leftProjection h) (f x)`,
  which is `χ(h) • (tensor action of projection h)(f x)`;
- the source form (`leftMixedEval_leftMatrix_mul`):
  `f([a Z; 0 p] x) = χ_L(a,p) • (A(a) ⊗ B(p)) (f x)`, and
  `rightMixedEval_rightMatrix_mul` for case (III);
- radical invariance (`leftMixedEval_of_mem_leftKernel_mul`,
  `rightMixedEval_of_mem_rightKernel_mul`);
- right translation (`leftMixedProductFunctor_action`):
  `(g · f)(x) = f(x g)`;
- maps (`leftMixedProductFunctor_map_eval`): `(φ f)(x) = (φ₁ ⊗ φ₂)(f x)`;
- one open subgroup of right stabilizers for the whole function
  (`*_exists_openSubgroup`) and compact projected support in
  `H \ P_(k+r+1)` (`*_isCompact_quotientSupport`);
- construction from a covariant function with these properties
  (`leftMixedMk`, `rightMixedMk`, with `leftMixedEval_mk`, `rightMixedEval_mk`),
  using the published `Induction.compactFunctionOf`.

Support, smoothness and functoriality all come from the published induction
construction; no finite-support replacement or abstract certificate is
inserted.

## Boundary ranks and the unit

No definition branches on `k` or `r`. For every `k` and `r`, including `k = 0`,
`r = 0` and both zero, the product is compact induction from the actual
subgroup. The inducing representation is the actual tensor of both inputs. Any
representation of the trivial groups `GL_0` and `P_1 = mirabolic 0` remains a
tensor factor with its full multiplicity. In particular `P_1` is not treated as
a unit: at `r = 0` the right product still induces from the embedded `GL_k` and
twists by `ν_k^(-1/2)`.

The unit is `T.mixedProductUnit`, the genuine line `ULift.{uV} ℂ` in `Type uV`
with the trivial action of `GL_0` (`mixedProductUnit_representation`,
`finrank_mixedProductUnit`). For `k = 0` both inducing subgroups are the whole
group (`mem_leftSubgroup_zero`, `mem_rightSubgroup_zero`).
`leftUnitProjection r`, `rightUnitProjection r : P_(0+r+1) → P_(r+1)` are the
mirabolic components of the published projections on the whole group. Their
entries are given by `leftUnitProjection_apply` and
`rightUnitProjection_apply`. Both are bijective
(`leftUnitProjection_bijective`, `rightUnitProjection_bijective`) and
continuous.

`T.leftMixedProductUnitEquiv r B` is an explicit equivariant linear equivalence
from the product of `(1, B)` to `lift (B ∘ leftUnitProjection r)` on
`ULift.{uF} B`, in `Type (max uF uV)`. It composes four maps:

1. evaluation at `1`, `Induction.compactInducedTopEquiv`, for compact induction
   from a subgroup containing every element; its inverse is
   `v ↦ (g ↦ σ(g) v)`, smooth by pulling back an open stabilizer of `v`, with
   compact support because the quotient is a single point;
2. removal of the twist, which is `1` since `χ_L = 1` at `k = 0`;
3. the tensor unit `ULift ℂ ⊗ B ≃ B`;
4. the lift `ULift.up`.

`leftMixedProductUnitEquiv_apply` gives `(e f).down = unit(f(1))`, and
`unitTensorLeft_leftMixedEval_symm` gives the value of the inverse at each `x`.
`leftMixedProductUnitEquiv_naturality` proves naturality in `B`, and
`leftMixedProductUnitIso` packages the natural isomorphism
`Prod.sectR unit ⋙ leftMixedProductFunctor 0 r ≅
pullbackFunctor (leftUnitProjection r) ⋙ liftFunctor`. The `right*` versions
use `Prod.sectL`, the right unit `B ⊗ ULift ℂ ≃ B` and `rightUnitProjection`.
These equivalences come from the actual tensor unit and evaluation for
induction from the whole target group. They do not identify arbitrary
representations of a trivial group with the coefficient line.

Both-zero inputs. For `k = r = 0` the target is `mirabolic (0 + 0)`, a trivial
group. Both characters are `1` (the `k = 0` lemmas) and both subgroups are the
whole group. The product of any `(A, B)` is therefore the general construction
applied to the full tensor `A ⊗ B`, on which the trivial group `GL_0 × P_1` acts
through the projection. No separate both-zero construction is made and neither
factor is dropped. When `A` is the unit, the unit isomorphisms above apply with
`r = 0`.

## Provenance and scope

Cases (II) and (III) for ranks with `k ≥ 1` and `r + 1 ≥ 1` follow BZ77 §4.12
with §1.8's normalization; the implemented characters are explicit. The
extension to `k = 0`, the bundled functors on product categories, the evaluation
API, the unit isomorphisms, the generic `compactInducedTopEquiv` and the binary
tensor helpers are intrinsic constructions justified by the proved laws above;
they are not attributed verbatim to the paper. The paper's convention
`P_0 = ∅` in §4.13 is not used, and no `P_0` is introduced.

This pair proves no exactness, restriction filtration, derivative formula,
associativity, admissibility, irreducibility, classification, adjunction,
duality or pairing result. It asserts no Haar-modulus identity.

## Lean details and dependencies

The file sets `set_option backward.isDefEq.respectTransparency.types false`, as
`Langlands.Representation.Induction.Definitions` does. It is needed so that
definitional unfolding of the functor objects to the published compact-function
types is accepted. This option affects elaboration only. The inspected axioms of
the main declarations are `propext`, `Classical.choice` and `Quot.sound`.

Direct project imports: `Langlands.Group.GL.MirabolicMixedProductSubgroups`,
`Langlands.Group.GL.NormalizedCharacter`,
`Langlands.Representation.Induction.BinaryProduct`,
`Langlands.Representation.Induction.Definitions`,
`Langlands.Representation.Twist.RealPower`,
`Langlands.Representation.Smooth.SmoothPart.BasicProof` and
`Langlands.Representation.Smooth.Transfer.PullbackProof`. The other imports are
`Mathlib.Algebra.Module.ULift` and `Mathlib.CategoryTheory.Products.Basic`.

`BinaryProduct` is imported for the five compatibility abbreviations described
above. `MixedProductTensor.pullbackMap φ f` is `BinaryTensor.compMap f φ`,
`MixedProductTensor.compEquiv φ e` is `BinaryTensor.compEquiv e φ`, and
`MixedProductTensor.lift`, `liftEquiv` and `liftMap` are `BinaryTensor.lift`,
`BinaryTensor.liftEquiv` and `BinaryTensor.liftMap`. These five are the only
`BinaryProduct` declarations used by this module. In particular the binary
normalized product `binaryNormalizedProductFunctor` is not used.

The complete transitive project import closure, excluding this module, consists
of 40 modules:

- `Langlands.Group.GL.{Basic, BlockModulus, Blocks, Mirabolic,
  MirabolicMixedProductSubgroups, MirabolicOppositeIntersection,
  MirabolicProjection, MirabolicRadical, NormalizedCharacter, OppositeBlocks,
  Padic, PadicBlocks, RankMaps, RankReindex, UpperUnipotent}`;
- `Langlands.LocalField.{Definitions, Canonical, Topology}` and
  `Langlands.LocalField.Normalization.{Definitions, Statement, Proof}`;
- `Langlands.Representation.Category.Basic`;
- `Langlands.Representation.Induction.{BinaryProduct, BlockFactors, Definitions,
  Parabolic}`;
- `Langlands.Representation.Jacquet.PositiveCharacter`;
- `Langlands.Representation.Smooth.{Definitions, SmoothPart.Definitions,
  SmoothPart.BasicStatement, SmoothPart.BasicProof, Transfer.PullbackStatement,
  Transfer.PullbackProof, Transfer.SubquotientStatement,
  Transfer.SubquotientProof}`;
- `Langlands.Representation.Tensor.Finite`;
- `Langlands.Representation.Twist.{Definitions, SmoothStatement, SmoothProof,
  RealPower}`.

The other six direct imports account for 27 of these modules. The remaining 13
come only through `BinaryProduct`: `BinaryProduct` itself,
`Langlands.Group.GL.{BlockModulus, Blocks, MirabolicOppositeIntersection,
OppositeBlocks, PadicBlocks, RankReindex}`,
`Langlands.Representation.Induction.{BlockFactors, Parabolic}`,
`Langlands.Representation.Jacquet.PositiveCharacter`,
`Langlands.Representation.Smooth.Transfer.{SubquotientStatement,
SubquotientProof}` and `Langlands.Representation.Tensor.Finite`. Thus
`Tensor.Finite` is a transitive import, through `Induction.BlockFactors`. This
module uses none of its declarations. In particular it does not use
`FiniteTensor.externalFunctor`; the binary tensor model above takes its place.

These are matrix, block-parabolic, local-field, smooth-category, tensor, twist,
positive-character and induction infrastructure only, including the binary
normalized product. `Jacquet.PositiveCharacter` provides only the positive
square root of a positive real character and its inverse in `ℂˣ`
(`positiveHalfCharacter`, `inverseHalfCharacter`); it is used by
`Group.GL.BlockModulus`, and no Jacquet module is imported. The
closure contains no Haar-modulus identification, derivative, segment, socle,
classification, adjunction, duality or pairing module. In particular it avoids
the modules `SegmentHeadProductIrreducibility`, `GenericSegmentProductUniqueness`,
`SquareIntegrableLanglandsClassification`,
`UnlinkedSegmentSocleProductIrreducible`,
`LinkedSegmentSocleReverseProductStructure`, `LinkedSegmentSoclePairReducible`
and `SegmentSocleProductIrreducibility`, and every result owned by the tasks
excluded in task `f5488c8d-59a8-4de8-8649-4511bbaea5d9`. All imported pairs are
used unchanged.
