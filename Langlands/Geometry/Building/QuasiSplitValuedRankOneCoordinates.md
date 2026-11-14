# Coherent valued opposite-root coordinates over the maximal unramified field

This module defines a derived interface for a pair of opposite relative root groups. It does not assert that the records are inhabited. The separate `QuasiSplitValuedRankOneCoordinatesStatement` asserts their existence.

The field `F : Type u` is any nonarchimedean local field, with the Library's field, valuative relation and topology instances. There is no characteristic restriction. Write `K = UnramifiedClosure F`, the actual inertia fixed field, and let `H` be an actual affine group scheme over `K`. The parameters are supplied `B : MaximalUnramified.BuildingData F H`, `hZ : IsTorus B.centralizer.Z`, and `b : characterLattice B.S`. Write `i = B.i`, `j = B.centralizer.j` and `s = B.centralizer.s`. The records can be formed for any `b`; the existence statement selects indivisible roots and the appropriate branch.

## Coordinates on specified fields

`RootFieldCoordinatesOn i j s a E` keeps precisely the equivalence, full-centralizer character, restriction and conjugation fields of `RootFieldCoordinates`, with `E` specified externally. For every field `k : Type u`, group schemes `G,Z` over `k`, commutative group scheme `S`, morphisms `i : S.toGrp → G`, `j : Z → G`, `s : S.toGrp → Z`, character `a` of `S`, and extension field `E/k`, it contains:

- An equivalence `e : Multiplicative E ≃* rootGroupPoints i a`. Here `Multiplicative E` is the additive group of `E` written multiplicatively.
- A rational scheme character `β` of `Z_E` whose restriction along `s_E` is exactly the base change of `a`, as an equality of scheme characters.
- For every `z : Z(k)` and `t : E`, the ambient equality `j(z) e(t) j(z)⁻¹ = e(β(z_E)t)`, using actual rational scalar extension.

For finite separable `E/k`, `toRootFieldCoordinates` recovers the existing record, with the same field, equivalence and character.

`RootUnitaryCoordinatesOn i j s a E L` similarly keeps precisely the equivalence, double-root identification, character, restriction and conjugation fields of `RootUnitaryCoordinates`. Its parameters are fields `k,E,L : Type u`, compatible algebras `k → E → L` and `k → L`, a scalar-tower witness, and a separable quadratic extension `L/E`. It contains an equivalence `e : SU3Root.rationalParameters E L ≃* rootGroupPoints i a`, a rational character `β` of `Z_L` restricting along `s_L` to the base change of `a`, and, for every `z : Z(k)` and parameter `p`, the equality

`j(z) e(p) j(z)⁻¹ = e(scale (β(z_L)) p)`.

The actual parameters are pairs `(u,v)` in `L × L` satisfying `v + bar(v) = u bar(u)`. Scaling by `λ` sends them to `(λu, λ bar(λ)v)`. For every ambient `g : G(k)`, the `double` field states that `g ∈ rootGroupPoints i (2 • a)` if and only if `g = e(p)` for some parameter with literal first coordinate zero. For finite separable `L/k`, `toRootUnitaryCoordinates` recovers the existing record on exactly the same tower. No existing public coordinate declaration is changed.

## Nonmultipliable coordinates

`ValuedSL2RootCoordinates B hZ b` contains a field `E : Type u`, finite-dimensional and separable over `K`. Its `positive` and `negative` are specified-field coordinate records at `b` and `-b` over this same `E`, with independent full-centralizer characters. It contains one group homomorphism

`rho : Matrix.SpecialLinearGroup (Fin 2) E →* rationalPoints H`.

For every `t : E`, `rho_upper` and `rho_lower` identify its values on the actual determinant-one matrices

```text
upper(t) = [[1,t],[0,1]],    lower(t) = [[1,0],[t,1]]
```

with the positive and negative coordinate images, respectively. These matrices are `Matrix.SpecialLinearGroup.transvection` at positions `(0,1)` and `(1,0)`. The diagonal is the existing `SpecialLinear.Root.contractingMatrix` at `(0,1)`, hence `diag(t,t⁻¹)` for `t : Eˣ`.

The `coroot` field is an actual group-scheme morphism

`(WeilGm.commGroupScheme (CommRingCat.of K) E).toGrp → (B.centralizerTorus hZ).toGrp`.

For every `t : Eˣ`, `coroot_points` says that applying this morphism to `(WeilGm.rationalUnitsEquiv K E).symm t` and then applying `j` gives `rho(diag(t,t⁻¹))`. Thus the units are compared with the rational points of the actual induced torus.

Finally `origin : B.Apartment` is one point. For every `t : E`, both `origin.val b (positive.equiv t)` and `origin.val (-b) (negative.equiv t)` equal

`Langlands.FieldTheory.henselianSeparableAddValuation (MaximalUnramified.valuation F) (MaximalUnramified.valuationSubring_isHenselian F) E t`.

## Multipliable coordinates

`ValuedSU3RootCoordinates B hZ b` contains fields `E,L : Type u`, finite separable extensions `E/K` and `L/K`, a separable quadratic extension `L/E`, and compatible algebra structures with a scalar-tower witness. Its `positive` and `negative` are specified-tower unitary coordinate records at `b` and `-b`, using the same `SU3Root.rationalParameters E L`. Each sign retains its own full-centralizer character and its own literal double-root identification.

It contains one group homomorphism

`rho : SU3Root.specialUnitarySubgroup (SU3Root.fieldInvolution E L) →* rationalPoints H`.

For every parameter `p = (u,v)`, `rho_upper` and `rho_lower` identify its values on the actual upper and opposite matrices with the two coordinate images. In the Library convention these matrices and the diagonal are

```text
upper(p) = [[1,u,v],[0,1,bar(u)],[0,0,1]],
lower(p) = [[1,0,0],[-bar(u),1,0],[v,-u,1]],
diagonal(t) = diag(t,bar(t)/t,1/bar(t)).
```

The subgroup is the determinant-one subgroup preserving the Hermitian Gram matrix `[[0,0,1],[0,-1,0],[1,0,0]]`. The inputs to `rho` are bundled with the published membership proofs for `Parameters.embedding`, `oppositeEmbedding` and `diagonal`. No injectivity of `rho` is included.

The `coroot` field is an actual morphism from `(WeilGm.commGroupScheme (CommRingCat.of K) L).toGrp` to `(B.centralizerTorus hZ).toGrp`. For every `t : Lˣ`, its `K`-point map, compared through `WeilGm.rationalUnitsEquiv K L` and followed by `j`, equals `rho(diagonal(t))`. The coroot parameter is `t`; the root-action scalar `t²/bar(t)` is a different expression. The two full-centralizer characters are not identified by an extra equation.

One `origin : B.Apartment` satisfies all four depth identities. For every parameter `p`, its positive and negative root depths equal `SU3Root.towerDepth K E L (MaximalUnramified.valuation F) hH p`. For every `q` in the literal central subgroup, the positive double-root depth of `positive.equiv q.val` and the negative double-root depth of `negative.equiv q.val` equal `SU3Root.towerCentralDepth K E L (MaximalUnramified.valuation F) hH q`. The negative double is written `2 • (-b)`, equal to `-(2 • b)`.

Here and above `hH = MaximalUnramified.valuationSubring_isHenselian F`. The extension valuation is normalized on `K`, with no new normalization on `E` or `L`. `towerDepth` is half the second-coordinate value and `towerCentralDepth` is the whole second-coordinate value of that same extension valuation. All depth equalities are in `WithTop ℝ`, including infinite depth at the identity. The point may depend on `b`; the records make no simultaneous choice across different roots.

## Provenance

This packaging is internal and derived from Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered source `kaletha-prasad-2023-bruhat-tits-new-approach`. Construction 6.1.17 and Remark 6.1.18 (printed pp.205–206, PDF pp.236–237) give the original-base-normalized coordinate values; Proposition 6.1.19 (PDF pp.237–238) reduces to restrictions of scalars of SL₂ and SU₃. The comparison Proposition 6.2.6 (printed p.216, PDF p.247) and the quasi-split rank-one reduction in Proposition 7.1.1 (PDF pp.268–271) motivate requiring a point of the supplied apartment and one common rank-one homomorphism. Section 7.2, especially Lemma 7.2.3 (PDF pp.276–277), motivates retaining the actual induced-torus morphism for functoriality. The source does not print this exact bundled interface.

The registered 2024 corrections, `kaletha-prasad-2024-corrections`, PDF p.33, add AS 5 to Chapter 7 hypotheses. The records here are data definitions; the separate existence target is not a coroot estimate, a torus-root commutator estimate, S1 or S2. No downstream estimate is built into these records.
