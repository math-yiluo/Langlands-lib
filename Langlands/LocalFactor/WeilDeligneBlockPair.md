# Pair L-factors of two uncentered special blocks

This module computes the pair L-factor of two uncentered special blocks
\(B \otimes S_{a+1}\) and \(B' \otimes S_{b+1}\) (the Library's
`WeilDeligneRepresentation.block ν B (a+1)` and `block ν B' (b+1)`):
\[
  L\bigl((B\otimes S_{a+1})\otimes(B'\otimes S_{b+1})\bigr)
    = \prod_{j < \min(a+1,\,b+1)} L\bigl(\nu^{a+b-j} B \otimes B'\bigr),
\]
where each factor on the right is the pair L-factor of the twist of \(B\) by the
character \(\nu^{a+b-j}\) and of \(B'\), both with zero monodromy.

Everything is algebraic. The coefficient field \(K\), group \(G\), character
\(\nu : G \to K^\times\), normal subgroup \(I\), element \(g \in G\), finite
representations \(B\), \(B'\) (in possibly different universes) and lengths
\(a, b \in \mathbb{N}\) are arbitrary inputs. The only hypothesis is that
\(\nu\) is trivial on \(I\) (`hν : ∀ i : I, ν i = 1`). No characteristic-zero,
semisimplicity, irreducibility or topology assumption is used: the kernel of
the monodromy is computed in explicit coordinates rather than by a
Clebsch–Gordan decomposition.

The L-factors are the existing Library objects: `WeilDeligne.eulerPolynomial A I g`
is the reversed characteristic polynomial \(\det(1 - X\,g)\) of \(g\) on the
inertia-fixed monodromy kernel \((\ker N)^I\) of \(A\), `rationalLFactor A I g`
is its reciprocal in \(K(X)\), and `pairLFactor A A' I g` is `rationalLFactor` of
the actual tensor pair `WeilDeligneRepresentation.tensor A A'`, whose monodromy is
\(N_A \otimes 1 + 1 \otimes N_{A'}\). A block `block ν B m` is the tensor of
`zeroMonodromy ν B` with the special block on \(K^m\), on which \(g\) acts on
the coordinate of weight \(i\) by \(\nu(g)^i\) and the monodromy raises the
weight by one (`Special.action`, `Special.raising`).

## Provenance

The main theorem is the algebraic content of Henniart 2002
(henniart-2002-characterization), §2.4, printed p.594 (PDF p.8): for
\(\rho, \rho'\) and integers \(n, n' \ge 1\),
\[
  L\bigl(s, (\rho\otimes\mathrm{St}_n)\otimes(\rho'\otimes\mathrm{St}_{n'})\bigr)
    = \prod_{j=1}^{\min(n,n')} L(s, \nu^{n+n'-1-j}\otimes\rho\otimes\rho').
\]
With \(n = a+1\), \(n' = b+1\) and the index shifted to \(j = 0, \dots,
\min(a+1,b+1)-1\), the exponent \(n+n'-1-(j+1)\) is \(a+b-j\), which is the form
proved here. Henniart states it for irreducible \(\rho,\rho'\); the Lean result
holds for arbitrary finite representations \(B, B'\) and arbitrary \(I\), \(g\)
with \(\nu\) trivial on \(I\). The auxiliary definitions (`extendZero`,
`gridMonodromy`, `gridScale`, `gridEmbedding`, `blockPairCoord`,
`blockPairKernelOperator`, `blockPairKernelEmbedding`) are internal proof
infrastructure. In the arithmetic setting,
`Langlands.Correspondence.arithmeticPairLFactor F X Y` is by definition
`pairLFactorClass (localInertia F) (localGeometricFrobenius F) X Y`, which on
`classOf` representatives is `pairLFactor`; with
`ν := (Weil.Local.localNormCharacter F).toMonoidHom` (a continuous character
`localWeilGroup F →ₜ* ℂˣ` viewed as a monoid hom), `I := localInertia F`,
`g := localGeometricFrobenius F` and
`hν := Weil.Local.localNormCharacter_on_inertia F`, `pairLFactor_block_block`
gives the arithmetic product formula for two uncentered blocks. This
corollary is not stated in this module.

## Grid combinatorics (namespace `Langlands.LocalFactor`)

Vectors of \((B\otimes K^{a+1})\otimes(B'\otimes K^{b+1})\) are written as grids
\(x : \mathrm{Fin}(b+1) \to \mathrm{Fin}(a+1) \to U\), with \(U = B\otimes B'\);
the entry \(x\,l\,i\) pairs weight \(i\) of the first block with weight \(l\) of
the second.

- `extendZero y j` extends a family \(y : \mathrm{Fin}\,k \to U\) by zero to all
  \(j \in \mathbb{N}\) (`extendZero_of_lt`, `extendZero_of_le`).
- `gridMonodromy a b`: \((N x)\,l\,i = [i>0]\,x\,l\,(i-1) + [l>0]\,x\,(l-1)\,i\),
  raising both weights (`gridMonodromy_apply`).
- `gridScale a b c f`: \((x\,l\,i) \mapsto c^{i+l}\, f(x\,l\,i)\), the shape of the
  group action (`gridScale_apply`).
- `gridEmbedding a b`: sends \(y : \mathrm{Fin}(\min(a+1,b+1)) \to U\) to the grid
  \(x\,l\,i = (-1)^i \cdot y_{a+b-(i+l)}\) (zero when \(a+b-(i+l)\) is out of
  range): the component \(y_j\) is spread with alternating signs along the
  antidiagonal of total weight \(a+b-j\) (`gridEmbedding_apply`).
- `gridMonodromy_gridEmbedding`: these vectors are killed by `gridMonodromy`
  (adjacent entries along an antidiagonal cancel; the boundary terms fall out of
  range).
- `gridEmbedding_last`: the component \(y_j\) is read off at the entry
  \((l, i) = (b-j, a)\), up to the sign \((-1)^a\); hence
  `gridEmbedding_injective`.
- `gridScale_gridEmbedding`: `gridScale c f` maps `gridEmbedding y` to
  `gridEmbedding (fun j => c^(a+b-j) • f (y j))`.
- Kernel description, for \(x\) with `gridMonodromy a b x = 0`:
  `grid_step` (interior relation \(x\,l\,i = -x\,(l-1)\,(i+1)\)), `grid_bottom_left`,
  `grid_bottom_right` (boundary zeros), `grid_chain` (along an antidiagonal,
  \(x\,l\,i = (-1)^t\, x\,(l-t)\,a\) for \(i+t = a\)), `grid_zero_left`,
  `grid_zero_right` (entries of total weight below \(\max(a,b)\) vanish), and
  `eq_gridEmbedding`: \(x = \) `gridEmbedding` of
  \(j \mapsto (-1)^a\, x\,(b-j)\,a\). Thus the kernel of `gridMonodromy` is exactly
  the image of `gridEmbedding`, in every characteristic.

## Weil–Deligne side (namespace `Langlands.LocalFactor.WeilDeligne`)

- `blockPairCoord B B' a b`: the linear equivalence
  \((B\otimes K^{a+1})\otimes(B'\otimes K^{b+1}) \simeq
  (\mathrm{Fin}(b+1)\to\mathrm{Fin}(a+1)\to B\otimes B')\), built from Mathlib's
  `TensorProduct.tensorTensorTensorComm`, `TensorProduct.assoc` and
  `TensorProduct.piScalarRight`. On pure tensors
  (`blockPairCoord_tmul`): \((u\otimes f)\otimes(u'\otimes f') \mapsto
  \bigl(l, i \mapsto f_i f'_l \cdot u\otimes u'\bigr)\).
- `blockPairCoord_monodromy_tmul`, `blockPairCoord_representation_tmul`: the
  monodromy and the action of \(g\) of the tensor of the two blocks on pure
  tensors, in coordinates. Extending by `TensorProduct.ext_fourfold'`,
  `blockPairCoord_monodromy` identifies the monodromy with `gridMonodromy`, and
  `blockPairCoord_representation` identifies the action of \(g\) with
  `gridScale (ν g) (TensorProduct.map (B g) (B' g))`.
- `blockPairKernelOperator ν B B' a b I g`: on
  \(\mathrm{Fin}(\min(a+1,b+1)) \to (B\otimes B')^I\), the componentwise operator
  whose component \(j\) is \(\nu(g)^{a+b-j}\) times the action of \(g\) on the
  \(I\)-invariants of \(B\otimes B'\) (`Representation.toInvariants`).
- `blockPairKernelEmbedding ν B B' a b I`: the inverse coordinates of
  `gridEmbedding` applied to \(I\)-invariant families;
  `blockPairCoord_kernelEmbedding` records its coordinates.
- `eulerPolynomial_block_block` (hypothesis `hν`): the Euler polynomial of the
  tensor of the two blocks equals that of `blockPairKernelOperator`. Proof:
  `eulerPolynomial_eq_of_embedding` (from `WeilDeligneEulerSum`) applied to
  `blockPairKernelEmbedding`. It is injective by `gridEmbedding_injective`; its
  image is killed by \(N\) (`gridMonodromy_gridEmbedding`) and fixed by \(I\)
  (since \(\nu\) is trivial on \(I\), `gridScale` acts on the image through the
  invariant components); every \(I\)-fixed kernel vector is in the image
  (`eq_gridEmbedding`, its read-off entries being \(I\)-invariant); and \(g\)
  intertwines with `blockPairKernelOperator` by `gridScale_gridEmbedding`.
  `rationalLFactor_block_block` is the rational version.
- `tensor_zeroMonodromy_twist_representation`: \(g\) acts on the tensor of
  `zeroMonodromy ν (twist χ B)` and `zeroMonodromy ν B'` by
  \(\chi(g)\,(B(g)\otimes B'(g))\) (`TensorProduct.map_smul_left`).
- `pairLFactor_zeroMonodromy_twist` (for \(\chi\) trivial on \(I\)): that pair
  factor is the rational factor of \(\chi(g)\) times the action of \(g\) on
  \((B\otimes B')^I\). Proof: the monodromy \(0\otimes1 + 1\otimes0\) vanishes, so
  \((\ker N)^I\) is the \(I\)-invariants of \(B\otimes B'\), and
  `rationalLFactor_eq_of_embedding` applies to the inclusion of the invariants.
- `pairLFactor_block_block` (main theorem, hypothesis `hν : ∀ i : I, ν i = 1`):
  ```
  pairLFactor (block ν B (a + 1)) (block ν B' (b + 1)) I g =
    ∏ j : Fin (min (a + 1) (b + 1)),
      pairLFactor (zeroMonodromy ν (FiniteRepresentation.twist (ν ^ (a + b - j.val)) B))
        (zeroMonodromy ν B') I g
  ```
  Proof: `rationalLFactor_block_block`, then `rationalFactor_pi` splits the
  componentwise operator into the product of its components, and each component
  is identified by `pairLFactor_zeroMonodromy_twist` with
  \(\chi = \nu^{a+b-j}\) (trivial on \(I\) since \(\nu\) is).
