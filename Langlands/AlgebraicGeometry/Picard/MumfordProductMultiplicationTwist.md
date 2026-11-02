# Pulling the twisted Mumford product bundle back along multiplication on the parameter

Lean module: `Langlands.AlgebraicGeometry.Picard.MumfordProductMultiplicationTwist`,
namespace `Langlands.AbelianScheme.MultiplicationTwist`.

Author: Worker 998.

## Role and provenance

This is internal infrastructure for task `981f6bcb-41de-4a08-83b8-48b6eec2b236`, the proof of
`Langlands.AbelianScheme.AlgClosedFieldAmpleEulerInverseScalingStatement`
(`χ(H^k) χ(H^{-k}) = k^{2g} χ(H) χ(H^{-1})`). On the self-product `Z = A ×_K A` (the Library's
`mumfordProduct A`, parameter-first, with projections `fst` and `snd` and the addition
`m = mumfordAddition A = (fst * snd).left`), the proof compares `m^* H^k ⊗ fst^* H^{-k}` with
the pullback of `m^* H ⊗ fst^* H^{-1}` along `1 × [k]`. This module proves that comparison,
up to a twist by a bundle pulled back from the second factor. It uses the balanced cube
identity, published as the statement `Langlands.GroupScheme.FieldCubePullbackStatement`. That
statement is not yet proved in the Library, so it appears here as an explicit hypothesis.

Mathematically, the cube identity for the three maps `fst`, `snd^j`, `snd` reads
`H(x + (j+1)y) ⊗ H(x) ⊗ H(jy) ⊗ H(y) ≅ H(x + jy) ⊗ H(x + y) ⊗ H((j+1)y)`. By induction on `j`,
`H(x + ky) ⊗ H(x)^{-1}` is `(H(x+y) ⊗ H(x)^{-1})^k` twisted by `H(ky) ⊗ H(y)^{-k}`. This is the
bilinearity of the Mumford bundle in the parameter, which follows from the theorem of the cube
(Edixhoven, van der Geer and Moonen, *Abelian Varieties*, registered source
`edixhoven-vandergeer-moonen-abelian-varieties-draft`: Theorem of the Cube (2.7) and its
Corollary (2.8) for three morphisms `f, g, h : Y ⟶ X`, printed pp.19-20, PDF pp.23-24; the
Mumford bundle, Definition (2.15), printed p.22, PDF p.26; its use in the proof of (9.11),
printed p.132, PDF p.136). The module states no
new mathematical notion. Its anchor proposition `MumfordProductMultiplicationTwistStatement` is
internal: it is exactly the main theorem with the cube identity as a premise, and it is proved
in the same module.

## Method

The computation takes place in the Picard group of `Z`. This is the Library's
`Langlands.CategoryTheory.PicardGroup` of the monoidal category of modules on `Z`. Its elements
are isomorphism classes of tensor-invertible modules, and two modules are isomorphic exactly
when their classes agree (`PicardGroup.ofObject_eq_iff`). Line bundles are tensor invertible by
the Library's `locallyFreeRankOneIffTensorInvertible`. The Library's `localizedTensorIso`
compares the sheafified tensor `tensorObj` with the monoidal tensor.

## Declarations

- `tensorObj_tensorInvertible`, `lineBundle_tensorInvertible`, `pullback_tensorInvertible`:
  tensor invertibility of `tensorObj` of invertibles, of line bundles and of their pullbacks.
- `ofObject_tensorObj`: the class of `tensorObj M N` is the sum of the classes.
- `ofObject_structureSheaf`: the class of the structure sheaf is zero.
- `ofObject_eq_of_iso`: isomorphic modules have equal classes.
- `pc A L a`: the class of `a.left^* L` for a line bundle `L` on `A` and a morphism
  `a : Z ⟶ A` over `K`.
- `powLB L n`: the tensor power `tensorPow L.obj n` as a line bundle (Library
  `tensorPow_isLocallyFreeRankOne`).
- `pc_one`: `pc A L 1 = 0`. The constant morphism `1` factors through `Spec K`
  (`Hom.one_def`), and every line bundle on `Spec K` is trivial (Library
  `fieldLineBundleTriviality`).
- `pc_inverse`: if `L ⊗ N ≅ 𝒪`, then `pc A N a = - pc A L a`. Pull the isomorphism back and use
  `pullbackTensorIso` and `pullbackUnitIso`.
- `pc_tensorPow`: `pc A (powLB L n) a = n • pc A L a`, by induction with `pullbackTensorIso`.
- `ofObject_pullback_pullback`: the class of `Φ.left^*(a.left^* L)` is `pc A L (Φ ≫ a)`
  (`pullbackComp`).
- `pc_cube`: under `FieldCubePullbackStatement`, for `f g h : Z ⟶ A`,
  `pc(f*g*h) + (pc f + (pc g + pc h)) = pc(f*g) + (pc(f*h) + pc(g*h))`. The cube is applied
  with `T = Z` and `G = A.toGrp`, and the classes of both sides are compared.
- `pc_first_mul_second_pow`: under the cube identity, for every `j`,
  `pc(fst * snd^j) - pc(fst) = j • (pc(fst * snd) - pc(fst)) + pc(snd^j) - j • pc(snd)`.
  Induction on `j`: the case `0` is `pc_one`, and the step applies `pc_cube` to
  `(fst, snd^j, snd)` and rearranges with `abel`.
- `twistedProduct A L M = m^* L ⊗ fst^* M` and `multiplicationTwist A H Nk k = [k]^* H ⊗ Nk`
  (abbreviations), where `[k] = (multiplication A.toGrp k).hom.hom`.
- `nonempty_pullback_twistedProduct_iso`: under the cube identity, let `N` be an inverse of
  `H` and `Nk` an inverse of `tensorPow H.obj k`. Let `Φ : Z ⟶ Z` satisfy `Φ ≫ fst = fst` and
  `Φ ≫ snd = snd ^ k`. Then
  `Φ^*(twistedProduct A H N) ≅ twistedProduct A H^k Nk ⊗ snd^*(multiplicationTwist A H Nk k)`.
- `MumfordProductMultiplicationTwistStatement` and `mumfordProductMultiplicationTwist`: the
  anchor proposition, the cube identity implying the previous theorem for all data, and its
  proof.

## Proof of `nonempty_pullback_twistedProduct_iso`

It suffices to compare classes. The class of the left side is
`pc H (Φ ≫ (fst * snd)) + pc N (Φ ≫ fst)`, using `pullbackTensorIso`, `ofObject_tensorObj` and
`ofObject_pullback_pullback`. Since `Φ ≫ (fst * snd) = (Φ ≫ fst) * (Φ ≫ snd)`
(`MonObj.comp_mul`), this is `pc H (fst * snd^k) - pc H fst`, by `pc_inverse`. On the right
side, `pc_tensorPow` and `pc_inverse` give
`k • pc H (fst * snd) - k • pc H fst` for `m^* H^k ⊗ fst^* Nk`. The twist `snd^*([k]^* H ⊗ Nk)`
has class `pc H (snd ≫ [k]) - k • pc H snd`. Here `snd ≫ [k] = snd ^ k` by the Library's
`points_multiplication`. By `pc_first_mul_second_pow` with `j = k` the two classes agree.

The module uses only Mathlib and published Library results, with the cube identity as an
explicit premise. Its axioms are `propext`, `Classical.choice` and `Quot.sound`.
