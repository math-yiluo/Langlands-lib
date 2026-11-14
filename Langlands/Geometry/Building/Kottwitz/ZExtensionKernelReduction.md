# Reducing the unramified kernel clause of KP Proposition 11.5.3 to named inputs

This module is a conditional step toward
`Langlands.Geometry.Building.Kottwitz.ZExtensionKottwitzKernelSurjectivityStatement`
(module `Kottwitz.ZExtensionKernelStatement`), the kernel clause of
Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), Proposition 11.5.3,
printed page 431, PDF page 462 (source ID
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`). It does not
prove that statement. It proves the first conjunct (points over
`K = UnramifiedClosure F`) from three unproved Library statements, which are
explicit premises. It gives no result about the second conjunct (`F`-rational
points).

The module is derived content. It splits the published statement into its two
conjuncts and puts together a proof from Library facts and the three assumed
statements. It asserts nothing from the literature beyond what those statements
and the published target already assert.

## Declarations

- `ZExtensionUnramifiedKottwitzKernelStatement` is the first conjunct of the
  target, copied verbatim: for every nonarchimedean local field `F : Type u`, every
  field `k` with compatible maps `k → K → E = SeparableClosure F`, `E` a
  separable closure of `k` and `K/k` normal, every connected reductive `G` over
  `Spec k` and every `z : ZExtension G`, the image of the kernel of
  `reductiveKottwitz F k z.H` under `z.H.affinePointsTarget z.p (CommAlgCat.of k K)`
  is the kernel of `reductiveKottwitz F k G hG`.
- `ZExtensionRationalKottwitzKernelStatement` is the second conjunct, copied
  verbatim: for every connected reductive `G` over `Spec F` and every
  `z : ZExtension G`, the image of the kernel of `reductiveKottwitzRational F z.H`
  under `rationalPoints.map z.p` is the kernel of `reductiveKottwitzRational F G hG`.
- `zExtensionKottwitzKernelSurjectivityStatement_iff` proves that the published
  target is the conjunction of these two propositions. The proof is `Iff.rfl`, so
  each named conjunct is definitionally the corresponding half of the target.
- `ZExtensionUnramifiedKernelReductionStatement` is the implication

  `ReductiveKottwitzExistenceStatement → ReductiveKottwitzFunctorialityStatement →
  CentralTorusInertiaExactnessStatement → ZExtensionUnramifiedKottwitzKernelStatement`,

  all at universe `u`. The three premises are the Library's published, unproved
  statements: KP Lemma 11.5.1 as existence (with surjectivity and the z-extension
  clauses) and as functoriality, in module `Kottwitz.ReductiveMapStatement`, and
  right exactness of inertia coinvariants for a central torus quotient, in module
  `Kottwitz.CentralTorusExactnessStatement`. Nothing else is assumed. In
  particular the reduction does not use `ReductiveKottwitzDescentStatement`,
  injectivity of `π₁(Z)_I → π₁(H)_I`, KP Corollary 11.1.9, or
  `ZeroKernelStatement`.
- `zExtensionUnramifiedKernelReduction` proves
  `ZExtensionUnramifiedKernelReductionStatement`.

## The source argument

KP prove Proposition 11.5.3 for an arbitrary base field `k` of Chapter 11. They
use exactness of `1 → Z(k) → G̃(k) → G(k) → 1` for the induced torus `Z`, the
exact sequence `X_*(Z)_I → π₁(G̃)_I → π₁(G)_I → 0` from right exactness of
coinvariants, injectivity on the left from torsion-freeness of `X_*(Z)_I` (proof
of Lemma 2.5.20), exactness of Galois invariants for the induced Galois module
`X_*(Z)_I`, surjectivity of `Z(k) → (X_*(Z)_I)^Γ` (Corollary 11.1.9) and the
snake lemma. For the first conjunct the base field is `K` and `Γ = Gal(K/K)` is
trivial. Then only part of this argument is needed: surjectivity of
`G̃(K) → G(K)`, the commuting square, exactness at `π₁(G̃)_I`, and
surjectivity of the Kottwitz map for the torus `Z` over `K`. Injectivity on
`X_*(Z)_I` is only needed in the source to make the lifted class Galois
invariant, so it plays no role here.

## The Lean proof

Write `p = z.p`, `i = z.i`, `Z = z.Z` and `H = z.H`. The connected reductivity of
`H` is `z.isZExtension.source_reductive`. For `Z` it comes from
`IsInducedTorus.isTorus` and `IsTorus.isConnectedReductive_of_fieldSplitting`.
The proof applies the Library's group-theoretic snake step
`map_kernel_eq_of_kernel_lift` (module `Kottwitz.KernelTransport`) to:

- the point map `H.affinePointsTarget p (CommAlgCat.of k K) : H(K) → G(K)`;
- `κ_H = reductiveKottwitz F k H hH` and `κ_G = reductiveKottwitz F k G hG`;
- `q`, the multiplicative form of the linear map
  `fundamentalInertiaMap k K E G hG H hH p : π₁(H)_I → π₁(G)_I`.

It discharges the three hypotheses of `map_kernel_eq_of_kernel_lift` as follows.

1. *Surjectivity of the point map.* This is the first component of the last
   clause of `ReductiveKottwitzExistenceStatement` for `G` and `z`.
2. *The square `κ_G ∘ p = q ∘ κ_H`.* This is the first conjunct of
   `ReductiveKottwitzFunctorialityStatement` for the homomorphism `f = p`,
   moved from additive to multiplicative notation by `Multiplicative.ofAdd`.
3. *Lifting kernel elements.* Let `a ∈ ker q`. Then `a.toAdd` is in the kernel
   of the linear map `fundamentalInertiaMap … p`. By
   `CentralTorusInertiaExactnessStatement.zExtension`, applied to the field
   tower `k → K → E` and to `z`, this kernel is the range of
   `fundamentalInertiaMap k K E H hH Z i`. So `a.toAdd = π₁(i)(b)` for some
   `b ∈ π₁(Z)_I`. Surjectivity of `reductiveKottwitz F k Z` (the fourth clause of
   `ReductiveKottwitzExistenceStatement` for the group `Z.toGrp`) gives
   `x ∈ Z(K)` with `κ_Z(x) = b`. The candidate lift is
   `h = affinePointsTarget Z.toGrp i (CommAlgCat.of k K) x ∈ H(K)`.
   - `h ∈ ker(p)`: after unfolding `affinePointsTarget_apply` and reassociating,
     this is `x ≫ i ≫ p = 1`. That is
     `Langlands.GroupScheme.comp_quotient_eq_one`, applied to the quotient
     property `z.isZExtension.quotient.2.2.2` (the range of the kernel inclusion
     of `p` is the range of `i`).
   - `κ_H(h) = a`: the first conjunct of
     `ReductiveKottwitzFunctorialityStatement` for `f = i` gives
     `κ_H(h).toAdd = π₁(i)(κ_Z(x).toAdd) = π₁(i)(b) = a.toAdd`.

The equation produced by `map_kernel_eq_of_kernel_lift` is then exactly the
first conjunct for `F`, `k`, `G`, `hG` and `z`.

The module compiles in the pinned environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`. The proof uses only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`. It sets
`backward.isDefEq.respectTransparency false` and raises `maxHeartbeats` to
800000, as the neighbouring Kottwitz modules do.

## Scope

The second conjunct also needs rational point surjectivity
(`ZExtensionPointSurjectivityStatement` with `k = K = F`), the rational square
from `ReductiveKottwitzDescentStatement`, Galois equivariance of `π₁(i)` (part of
the Library's `FundamentalInertiaMapStatement`), injectivity of
`π₁(Z)_I → π₁(H)_I`, and KP Corollary 11.1.9 for the induced torus `Z`. When this
module was written, the last two inputs had no Library statement. This module
gives no reduction for that conjunct. The consumer of the target, the
proof of KP Proposition 11.5.4 (`ZeroKernelStatement`), uses only the first
conjunct.
