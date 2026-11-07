# Equivariant scheme sections for actions of arbitrary tori

This module extends the published split-torus result
`IsSplitTorus.exists_equivariantSection` (module
`GroupScheme/Rational/SplitTorusEquivariantSection`) to an arbitrary torus over a field.
A torus `D` acts compatibly on a group scheme `E`, on a quotient `q : E ⟶ H`, and on the
kernel `N` of `q`, which is a vector group with linear coordinates. If `q` has a section as
a morphism of schemes, then it has a `D`-equivariant section as a morphism of schemes. The
section need not be a group homomorphism. No assumption is made on the characteristic, on
the splitting field, or on the weights, and `N` need not be central.

Provenance: this is an internal construction. It combines two published arguments. The
first is the equivariant section over a splitting field from
`SplitTorusEquivariantSection`. The second is the coefficient-contraction descent of
`GroupScheme/Rational/VectorExtensionDescent`
(`VectorExtensionDescent.extensionSectionOfBaseChange`). That module descends a
homomorphic section through the linear two-cocycle equation. Here the same contraction
descends a linear equivariance equation. As context only: the underlying fact is the
vanishing of Hochschild cohomology `H¹(D, V)` for groups `D` of multiplicative type (Milne,
*Algebraic groups*, 2017, Remark 15.17). The Lean proof does not use it.

## Setting

`k` is a field in universe `u`. `IsTorus D` is the published Library definition: `D`
becomes a split torus after base change to some field extension `K` of `k`. The data are
the same as in the split-torus module:

- group schemes `D`, `E`, `H` and `N` over `Spec k`, with automorphic actions `cE`, `cH`
  and `cN` of `D`;
- a homomorphism `i : N ⟶ E` that is a monomorphism of schemes, and a homomorphism
  `q : E ⟶ H`;
- `hker`: on every test scheme `T`, a point `g` of `E` lies in the range of `i` exactly
  when `g ≫ q = 1`;
- `hq`: `cE.act t g ≫ q = cH.act t (g ≫ q)`;
- `hi`: `cE.act t (w ≫ i) = cN.act t w ≫ i`;
- a morphism of schemes `s : H.X ⟶ E.X` with `s ≫ q = 𝟙` (hypothesis `hs`);
- natural coordinates `e` on `N` with `he : IsLinearVectorCoordinates cN e`.

`H` and `N` are affine over `Spec k`. In the main results `D` is a torus, so it is affine
too.

## Definitions (namespace `Langlands.GroupScheme.EquivariantSectionDescent`)

Here `D` is any group scheme; no torus hypothesis is used.

- `actionDefectUniversal`, `kernelActionDefect` and `actionDefect t x`, written `δ(t, x)`.
  This is the equivariance defect `(t · s(x)) · s(t · x)⁻¹`, factored through `i`
  (`actionDefect_comp`). It is natural in the test scheme (`comp_actionDefect`).
- `IsEquivariantCorrection cE cH cN i q hker hq s hs e he K b`. Let `K` be any field with
  `Algebra k K` and `b : H_K ⟶ N_K` a morphism of schemes over `K`. The predicate states
  that `δ(t, x) + B(t · x) = t · B(x)` in the vector coordinates of `N` for every
  `k`-algebra `A` with a compatible `K`-algebra structure. Here `B` is the coordinate
  vector of `b` (published `extendedMapCoordinates`) and the right-hand side is the
  published coordinate action.
- `equivariantCorrection i q hker s hs K σ hσ`. Let `σ : H_K ⟶ E_K` be a morphism of
  schemes with `σ ≫ q_K = 𝟙`. Then the point `s_K · σ⁻¹` lies in the kernel of `q_K`
  (`mem_range_baseChange_iff`, `baseChangedSection_comp`). This definition is its
  factorization through `i_K` (`equivariantCorrection_comp`).
- `sectionPoint K σ x`: the value of `σ` at an affine point `x` of `H` over a compatible
  algebra `A`, viewed as a point of `E` through the published
  `Lie.affineBaseChangeEquiv`.
- `correctedSection i s e K b = (contractedMap e K b ≫ i)⁻¹ · s`. The published
  `RelativeRoot.contractedMap` contracts the `K`-coefficients of `b` to `k` by a
  `k`-linear retraction `K → k` of the scalar inclusion (published
  `VectorCocycleDescent.contract`).
- `equivariantSectionOfBaseChange i q hker s hs e K σ hσ`: `correctedSection` applied to
  `equivariantCorrection`.
- `IsTorus.equivariantSection hD cE cH cN i q hker hq hi s hs e he` (namespace
  `Langlands.GroupScheme`): a chosen equivariant section, by `Classical.choose` from
  `IsTorus.exists_equivariantSection`.

## Statements

- `mem_range_baseChange_iff`, `baseChange_act_comp`, `baseChange_act_inclusion` and
  `baseChangedSection_comp`: the hypotheses `hker`, `hq`, `hi` and `hs` hold for the base
  change to `K` of all the data. The actions are the published
  `AutomorphicAction.baseChange`.
- `contracted_equation`: if `b` satisfies `IsEquivariantCorrection`, then the same
  equation holds with `B` replaced by the contracted coordinates, over every `k`-algebra
  `A`.
- `contractedMapPoint_act`: the contracted point `C(x)` satisfies
  `C(t · x) = δ(t, x)⁻¹ · (t · C(x))`.
- `comp_correctedSection`, `correctedSection_comp`: values of `correctedSection` on affine
  points, and `correctedSection ≫ q = 𝟙 H.X`.
- `act_correctedSection_affine` and `act_correctedSection`: let `b` satisfy
  `IsEquivariantCorrection`. Then
  `cE.act t (x ≫ correctedSection) = cH.act t x ≫ correctedSection` for affine points
  `t` of `D` and `x` of `H`. If `D` is affine over `Spec k`, the same holds for every test
  scheme `T`, `t : T ⟶ D.X` and `x : T ⟶ H.X`.
- `act_sectionPoint`: if `σ` is equivariant for the base-changed actions (hypothesis
  `hσact`), then so are its values `sectionPoint`.
- `extendedCorrectionPoint_comp` and `extendedCorrectionPoint_act`: on affine points over
  compatible algebras, the correction `c` satisfies `c(x) ≫ i = s(x) · σ(x)⁻¹` and
  `c(t · x) = δ(t, x)⁻¹ · (t · c(x))`.
- `equivariantCorrection_equation`: under `hσact`, the correction satisfies
  `IsEquivariantCorrection`.
- `equivariantSectionOfBaseChange_comp` and `act_equivariantSectionOfBaseChange`: the
  descended section is a section of `q` and is equivariant on every test scheme.
- `IsTorus.exists_equivariantSection` (namespace `Langlands.GroupScheme`). Let `D` be a
  group scheme with `IsTorus D` acting on `E`, `H` and `N` as above, with `H` and `N`
  affine over `Spec k`. Assume `hker`, `hq`, `hi`, `hs`, and linear coordinates on `N`.
  Then there is `σ : H.X ⟶ E.X` with `σ ≫ q = 𝟙` and
  `cE.act t (x ≫ σ) = cH.act t x ≫ σ` for every test scheme `T`, `t : T ⟶ D.X` and
  `x : T ⟶ H.X`.
- `IsTorus.equivariantSection_comp` and `IsTorus.act_equivariantSection`: these two
  properties of the chosen section `IsTorus.equivariantSection`.

## Proofs

**Equivariant correction over the splitting field.** Let `K` split `D`. All data base
change to `K`, and the base-changed coordinates `vectorBaseChangeCoordinates e K` are
linear by the published `IsLinearVectorCoordinates.baseChange`. So the published
`IsSplitTorus.exists_equivariantSection` gives an equivariant section `σ` of `q_K`. Let
`c` be the correction with `c ≫ i_K = s_K · σ⁻¹`. On points this reads
`i(c(x)) = s(x) · σ(x)⁻¹`. Cancel the monomorphism `i`. Expand `t · s(x)` with `δ(t, x)`,
and use `hi`, the action laws and `t · σ(x) = σ(t · x)`. A group calculation gives
`c(t · x) = δ(t, x)⁻¹ · (t · c(x))`. In additive coordinates, with linearity of the action
(`IsLinearVectorCoordinates.coordinateAction_eq`), this is `IsEquivariantCorrection`.

**Contraction.** Evaluate the equation at the images of `t` and `x` over `A ⊗[k] K`. The
defect is natural, so it becomes the image of `δ(t, x)`. Apply the contraction
`A ⊗[k] K → A` coordinate by coordinate. It is `A`-linear, commutes with the coordinate
action (published `AutomorphicAction.coordinateAction_contract`) and fixes the left copy
of `A` (`contract_includeLeft`). This gives the same equation over `A` for the contracted
coordinates (`contracted_equation`). Exponentiating gives `contractedMapPoint_act`.

**Equivariance of the corrected section.** On affine points,
`σ'(x) = i(C(x))⁻¹ · s(x)`. Act by `t` and substitute `t · s(x) = i(δ(t, x)) · s(t · x)`
and `contractedMapPoint_act`. A group calculation gives `t · σ'(x) = σ'(t · x)`. The
affine scheme `D × H` gives equality on the universal pair (published
`PointedCoordinateWeights.affine_hom_ext`), which pulls back to every test scheme. The
correction lies in the kernel, so `σ' ≫ q = s ≫ q = 𝟙`.

**Main theorem.** A torus over a field is affine (published
`SplittingAssembly.isAffine_of_isTorus`). Choose a splitting field `K` from `IsTorus D`.
Apply the split-torus theorem over `K`, then `equivariantSectionOfBaseChange`.

## Scope

The module constructs an equivariant section of schemes only. It does not make the section
a group homomorphism, does not prove existence of the original section `s`, and does not
treat root groups. The intended application is a torus-equivariant Heisenberg normal form
of a multipliable relative root group under the action of a non-split torus. This module
does not carry out that application.
