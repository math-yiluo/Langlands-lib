# KP Proposition 11.5.4: the zero subgroup, proof

Lean module: `Langlands.Geometry.Building.Kottwitz.ZeroKernelProof`,
namespace `Langlands.Geometry.Building.Kottwitz`.

## Statement

```
theorem Langlands.Geometry.Building.Kottwitz.zeroKernel : ZeroKernelStatement.{u}
```

The type is exactly the published proposition
`Langlands.Geometry.Building.Kottwitz.ZeroKernelStatement.{u}` of the module
`Langlands.Geometry.Building.Kottwitz.ZeroKernelStatement`, at an arbitrary
universe `u`, with no further hypothesis. Unfolded, it reads:

```
∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
  (S : CommGroupScheme (Spec (CommRingCat.of F)))
  (Z : GroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G) (j : Z ⟶ G)
  (d : ZeroSubgroupDatum i j),
  d.zeroSubgroup = (reductiveKottwitzRational F G hG).ker
```

In words: for every connected reductive group `G` over a nonarchimedean local
field `F` and every datum `d` (a maximal split torus, its centralizer and the
data of KP Definition 2.6.23(3)), the zero subgroup `G(F)^0` of `d` is the
kernel of the constructed rational Kottwitz homomorphism of `G`.

## Proof

The Lean proof is the single application

```
zeroKernel_of_unramifiedZeroDescent unramifiedZeroDescent
```

of `zeroKernel_of_unramifiedZeroDescent` (module
`Geometry.Building.Kottwitz.UnramifiedZeroKernelProof`), which derives the
statement from `UnramifiedZeroDescentStatement.{u}`, to
`unramifiedZeroDescent` (module `Geometry.Building.UnramifiedZeroDescentProof`),
proved without hypotheses: over the maximal unramified extension `K`,
`G(K)^1` and `G(K)^0` are Galois-stable and `G(F)^0 = G(K)^0 ∩ G(F)`.

Inside the reduction, `zeroKernel_of_unramified` combines this descent with
the descent of the Kottwitz map (`reductiveKottwitzDescent_assembled`) and the
unramified equality `G(K)^0 = ker κ_{G_K}` (`unramifiedZeroKernel`); the
details are on the page of `Geometry.Building.Kottwitz.UnramifiedZeroKernelProof`.
The statement is not modified and no hypothesis is added.

## Declarations

- `Langlands.Geometry.Building.Kottwitz.zeroKernel : ZeroKernelStatement.{u}`.

## Literature

T. Kaletha and G. Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Chapter 11, §11.5, Proposition 11.5.4, printed p. 431: `G(k)^0 = ker(κ_G)`.
The book's proof uses `ker(κ_G) = ker(κ_{G_K}) ∩ G(k)` and
`G(k)^0 = G(K)^0 ∩ G(k)` (Proposition 9.3.24) to reduce to `k = K`, where `G`
is quasi-split; the Lean proof follows the same reduction.
