# Weight spaces and roots through the actual adjoint representation

Worker 274.

This module defines the weight spaces and the roots of a commutative group scheme
`T` mapping to a group scheme `G` by a homomorphism `i : T ⟶ G`. Both use the
adjoint representation `adjoint G A` of the module `Langlands.GroupScheme.Lie.Adjoint`
on the actual dual-number kernels `lieKernel G A`, over **every** test algebra `A`,
not only over field-valued points.

## Sources

Milne, *Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`
(printed page = PDF page − 16):

- 10.18–10.20, printed pp.191–192 (PDF 207–208): `g(R) = Ker(G(R[ε]) → G(R))`
  and the adjoint representation `Ad` by inner automorphisms of `G(R[ε])`.
- Definition 12.16, printed p.236 (PDF 252): the weights of a torus on a
  representation are the characters with a nonzero eigenspace, and the nonzero
  eigenspaces are the weight spaces.
- §21.a, printed pp.424–425 (PDF 440–441): for a split reductive group `(G, T)`,
  `T` acts on `g` through `Ad`, `g` decomposes as `g_0 ⊕ ⨁ g_α`, and the
  nontrivial characters `α` that occur are the roots.

Milne works with algebraic groups over a field and with representations,
meaning comodules. Here the weight space is defined directly by the eigenvalue
condition on actual points of `T` over all test algebras, for a commutative group
scheme `T` over an arbitrary affine base `Spec R` and an arbitrary homomorphism
`i`. These generalisations are **derived**. This module does not use comodules
and does not compare with them. The weight decomposition is the separate
statement `WeightDecompositionStatement`.

## Definitions

Let `R : CommRingCat`, let `T : CommGroupScheme (Spec R)`, let `G` be a group
scheme over `Spec R` with `IsAffineHom G.X.hom` (needed for the module structure
on `lieKernel`), and let `i : T.toGrp ⟶ G`.

- `Lie.characterValue χ t : Aˣ` is `χ(t)` for a character
  `χ : characterLattice T` and an actual `A`-point `t : Lie.AffinePoints T.toGrp A`.
  It is the point `t ≫ χ` of `𝔾_m` read as a unit of `A` through the published
  `Gm.affinePointsEquiv`. `Lie.characterValue_comp` records
  `(f ≫ χ)(t) = χ(f(t))`.
- `lieKernelCommGroupOf` and `lieKernelModuleOf` restate the published
  commutative group and module structures on `lieKernel G A`
  (`lieKernelCommGroup`, `lieKernelModule`) for bases `Spec (CommRingCat.of k)`.
  Instance search does not find the generic instances there, because their keys
  contain `↑R` while `↑(CommRingCat.of k)` reduces to `k`. They are definitionally
  the published instances.
- `weightSpace i χ : Submodule R (Additive (lieKernel G R))` is the set of `X`
  such that for every commutative `R`-algebra `A : Type u` and every
  `t ∈ T(A)`,
  `adjoint G A (t ≫ i) X_A = χ(t) • X_A`.
  Here `X_A = lieKernelMapLinear G (Algebra.ofId R A) X` is the image of `X`
  under the map induced by `algebraMap R A`, and `t ≫ i` is the image `i(t)` of
  `t` in `G(A)`. The set is an `R`-submodule because `X ↦ X_A` is semilinear over
  `R → A` and `adjoint G A g` is `A`-linear. `mem_weightSpace` unfolds membership.
- `roots i : Set (characterLattice T)` is `{χ | χ ≠ 0 ∧ weightSpace i χ ≠ ⊥}`
  (`mem_roots`).
