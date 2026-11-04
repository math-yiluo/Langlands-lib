# Points of kernels of central isogenies over a field are killed by a fixed power

Author: Worker 1384.

This module moves the algebraic torsion theorem of `Langlands.Algebra.FiniteHopfConvolutionPower`
to group schemes over `Spec k`, for a field `k`. The two exported theorems are:

- `exists_pow_eq_one_of_isFinite K`: let `K : GroupScheme (Spec (CommRingCat.of k))` be
  commutative (`[IsCommMonObj K.X]`) with finite structure morphism (`[IsFinite K.X.hom]`).
  Then there is `N > 0` such that `x ^ N = 1` for every test object
  `T : Over (Spec (CommRingCat.of k))` and every point `x : T ⟶ K.X`. The proof takes `N`
  to be the `k`-dimension of the coordinate Hopf algebra of `K`, which is the order of `K`.
- `IsCentralIsogeny.exists_pow_eq_one_kernel hπ`: for a central isogeny
  `π : G ⟶ H` of group schemes over `Spec k`, there is `N > 0` such that `x ^ N = 1` for
  every point `x : T ⟶ (kernel π).X` on every test object `T` over `Spec k`.

Powers and `1` are taken in the group of `T`-points of the group object. The exponent `N`
is the same for all test objects.

## Provenance

The first theorem is the commutative case of Milne, *Algebraic Groups* (2017),
Proposition 11.32 (printed p. 221, PDF p. 237; source ID `milne-2017-algebraic-groups`). That
proposition says that a finite group scheme of order `n` over a field is killed by `n`. The
second theorem specializes it to kernels of central isogenies: such a kernel is finite and
central, hence commutative. The module is internal infrastructure for the proof of
`Langlands.GroupScheme.CentralIsogenyMaximalSplitTorusLiftStatement`. That proof uses only
the existence of some positive exponent.

## Spectra of Hopf algebras

Let `A` be a commutative Hopf algebra over `k` and `Y = (Spec A).asOver (Spec k)`.

- `id_spec_asOver_eq_mapMulEquiv`: the identity of `Y` corresponds to the point
  `AlgHom.id k A` under Mathlib's `Spec.mapMulEquiv`. That map is the multiplicative
  equivalence between the convolution monoid `WithConv (A →ₐ[k] T)` and morphisms
  `(Spec T).asOver (Spec k) ⟶ Y`.
- `id_spec_asOver_pow_finrank`: if `A` is cocommutative and finite-dimensional, then
  `𝟙 Y ^ finrank k A = 1`. This is `FiniteHopfConvolutionPower.pow_finrank_eq_one` moved
  through the multiplicative equivalence `Spec.mapMulEquiv`.
- `isCocomm_of_commute`: if any two points `Spec (A ⊗[k] A) ⟶ Y` over `Spec k` commute,
  then `A` is cocommutative. The two tensor-factor points `includeLeft` and `includeRight`
  then commute in the convolution monoid, because `Spec.mapMulEquiv` is injective and
  multiplicative. The TauCeti lemma
  `TauCeti.HopfAlgebra.commute_includeLeft_includeRight_iff_isCocomm` turns this into
  cocommutativity.

## Finite commutative group schemes (`exists_pow_eq_one_of_isFinite`)

1. `K.X.left` is affine, because a finite morphism is affine and the base `Spec k` is
   affine.
2. Let `A = AffineCoordinates.hopfAlgebra K` and `e = AffineCoordinates.hopfSpecIso K`, the
   Library isomorphism of group schemes from the relative spectrum of `A` to `K`. Let
   `f : Y ⟶ K.X` and `g : K.X ⟶ Y` be its underlying morphisms over `Spec k`. Then `f` is a
   monoid morphism and `f`, `g` are mutually inverse.
3. `A` is finite over `k`. The composite `f.left ≫ K.X.hom` is finite, since it is an
   isomorphism followed by a finite morphism. By `Over.w` it equals the structure morphism
   `Spec.map (algebraMap k A)`. Then Mathlib's `IsFinite.SpecMap_iff` and
   `RingHom.finite_algebraMap` apply.
4. `A` is cocommutative, by `isCocomm_of_commute`. For points `p, q` of `Y`, the monoid
   morphism `f` sends `p * q` and `q * p` to `(p ≫ f) * (q ≫ f)` and `(q ≫ f) * (p ≫ f)`,
   which are equal because `K` is commutative. Since `f` is an isomorphism, hence a
   monomorphism, `p * q = q * p`.
5. `A` is nontrivial, because the counit is a `k`-algebra map `A → k`. So
   `N = Module.finrank k A > 0`.
6. For a point `x : T ⟶ K.X`, write `x = (x ≫ g) ≫ f`. Precomposition is multiplicative
   (`MonObj.comp_pow`), so `(x ≫ g) ^ N = (x ≫ g) ≫ (𝟙 Y) ^ N = (x ≫ g) ≫ 1 = 1` by
   `id_spec_asOver_pow_finrank`. Postcomposition with the monoid morphism `f` is
   multiplicative (`MonObj.pow_comp`), and `1 ≫ f = 1`, so `x ^ N = 1`.

## Kernels of central isogenies (`IsCentralIsogeny.exists_pow_eq_one_kernel`)

The kernel `kernel π` is commutative by `IsCentral.isCommMonObj` from
`GroupScheme/Rational/CentralSubgroupGeometry`, applied to centrality of the kernel
inclusion (`hπ.isCentral_kernelι`). It is finite over the base by
`IsCentralIsogeny.kernel_isFinite`. Then `exists_pow_eq_one_of_isFinite` applies.
