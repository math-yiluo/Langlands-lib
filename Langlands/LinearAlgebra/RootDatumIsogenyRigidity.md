# Rigidity of isogenies of root data on roots

This module proves lattice lemmas about the isogenies of reduced integral
root data of `Langlands.LinearAlgebra.RootDatumIsogeny` (module
[`Langlands.LinearAlgebra.RootDatumIsogeny`](RootDatumIsogeny.md), Milne,
*Algebraic Groups* (2017), Definition 23.1). They say when two such
isogenies `f g : RootDatumIsogeny p P Q` from `P : RootDatum ι X Y` to
`Q : RootDatum ι₂ X₂ Y₂` have the same weight map `X →ₗ[ℤ] X₂`, given that
the two weight maps agree on every root of `P`.

These are the lattice steps of the corrected proof of Milne's Proposition
23.8 (printed p.487), as written out in the Markdown of
[`SplitIsogenyTorusRigidityStatement`](../GroupScheme/Reductive/SplitIsogenyTorusRigidityStatement.md):
the case where the target group is semisimple uses
`weightMap_eq_of_finite_rootSpan`, and the case where the source group is
semisimple uses `weightMap_eq_of_finite_corootSpan`. The module is derived
content. The two weight-map equality lemmas assume agreement on roots and
the stated finite-index condition; semisimplicity supplies that condition in
the corresponding group case. Without a finite-index condition, agreement on
roots does not determine the weight map: for the reduced root datum of
`SL₂ × Gₘ` (both lattices `ℤ²` with the standard pairing, roots `±2e₁`,
coroots `±e₁`), taking the identity, respectively `diag(1, 2)`, as both the
weight map and the coweight map gives two values of
`RootDatumIsogeny 1 P P` with the identity root correspondence and all root
factors `1`; their weight maps agree on the roots and differ on `e₂`.

All declarations are in the namespace
`Langlands.LinearAlgebra.RootDatumIsogeny`.

## General lemmas

- `nsmul_injective_of_isPerfPair`: if `B : M →ₗ[ℤ] N →ₗ[ℤ] ℤ` is a perfect
  pairing (`B.IsPerfPair`), `n : ℕ` is nonzero and `n • x = n • y` in `M`,
  then `x = y`.

  *Proof.* The map `x ↦ B x` is injective (`IsPerfPair.bijective_left`). For
  every `c`, `n * B x c = n * B y c` in `ℤ`, so `B x c = B y c`.

  The weight lattice `X` of a root datum `P` is torsion free by this lemma
  applied to `P.toLinearMap`, and the coweight lattice `Y` by the same lemma
  applied to the flipped pairing `P.toLinearMap.flip`.

- `linearMap_eq_of_eqOn_finite_quotient`: let `N` be an additive group in
  which `n • x = n • y` implies `x = y` for every nonzero `n : ℕ`, let
  `L` be a submodule of the `ℤ`-module `M` with `M ⧸ L` finite, and let
  `f g : M →ₗ[ℤ] N` agree on `L`. Then `f = g`.

  *Proof.* For `x : M` the class of `x` in the finite group `M ⧸ L` has
  finite order `n > 0`, so `n • x ∈ L`. Then `n • f x = f (n • x) =
  g (n • x) = n • g x`, hence `f x = g x`.

- `root_eq_of_smul_eq`: let `Q` be a reduced root datum over `ℤ`, let
  `a b : ℕ` with `0 < a`, and suppose `(a : ℤ) • Q.root i = (b : ℤ) • Q.root j`.
  Then `i = j` and `a = b`.

  *Proof.* The pair `Q.root i, Q.root j` is linearly dependent over `ℤ`
  (the coefficients `a` and `-b` give zero, with `a ≠ 0`). Reducedness
  (`RootPairing.IsReduced.eq_or_eq_neg`) gives `Q.root i = Q.root j` or
  `Q.root i = -Q.root j`. In the second case `(a + b) • Q.root j = 0`, so
  `Q.root j = 0` by torsion freeness of the weight lattice, which
  contradicts `RootPairing.ne_zero`. In the first case `i = j`, because the
  roots form an embedding. If `a ≠ b`, the difference of the larger and the
  smaller multiple kills the root, again contradicting `ne_zero`.

## Isogenies of root data

In this section `P` and `Q` are reduced root data on finitely generated
lattices with finite index types, and `f g : RootDatumIsogeny p P Q`.
Write `h` for the hypothesis
`∀ i, f.weightMap (P.root i) = g.weightMap (P.root i)`.

- `indexEquiv_eq_and_rootFactor_eq`: under `h`, for every `i : ι`,
  `f.indexEquiv i = g.indexEquiv i` and `f.rootFactor i = g.rootFactor i`.

  *Proof.* By the field `root_weightMap`, `h i` reads
  `(f.rootFactor i : ℤ) • Q.root (f.indexEquiv i) =
  (g.rootFactor i : ℤ) • Q.root (g.indexEquiv i)`. Root factors are positive
  (`rootFactor_pos`), so `root_eq_of_smul_eq` applies.

- `coweightMap_coroot_eq`: under `h`, `f.coweightMap (Q.coroot j) =
  g.coweightMap (Q.coroot j)` for every `j : ι₂`.

  *Proof.* Write `j = f.indexEquiv i`. By the field `coroot_coweightMap`,
  `f.coweightMap (Q.coroot (f.indexEquiv i)) = (f.rootFactor i : ℤ) • P.coroot i`,
  and likewise for `g`. The previous lemma identifies the indices and the
  factors.

- `weightMap_eq_of_finite_rootSpan`: if `X ⧸ P.rootSpan ℤ` is finite, then
  `h` implies `f.weightMap = g.weightMap`.

  *Proof.* The two weight maps agree on the span of the roots, by induction
  on the span. The weight lattice `X₂` of `Q` is torsion free, so
  `linearMap_eq_of_eqOn_finite_quotient` applies.

- `weightMap_eq_of_finite_corootSpan`: if `Y₂ ⧸ Q.corootSpan ℤ` is finite,
  then `h` implies `f.weightMap = g.weightMap`.

  *Proof.* By `coweightMap_coroot_eq` the coweight maps `Y₂ →ₗ[ℤ] Y` agree
  on the span of the coroots of `Q`. The coweight lattice `Y` of `P` is
  torsion free, so `linearMap_eq_of_eqOn_finite_quotient` gives
  `f.coweightMap = g.coweightMap`. For `x : X` and `y : Y₂`, `pairing_apply`
  gives `Q.toLinearMap (f.weightMap x) y = P.toLinearMap x (f.coweightMap y)`,
  and likewise for `g`. So `Q.toLinearMap (f.weightMap x)` and
  `Q.toLinearMap (g.weightMap x)` are equal, and `f.weightMap x =
  g.weightMap x` because the pairing of `Q` is perfect.

The lemmas use only the axioms `propext`, `Classical.choice` and
`Quot.sound`.
