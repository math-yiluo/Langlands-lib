# Smoothness of torus centralizers: statement

Worker 1379.

`TorusCentralizerSmoothStatement.{u}` concerns a field `k : Type u`, a
smooth affine group scheme `G` over `Spec k`, a commutative group scheme
`T`, and a homomorphism `i : T.toGrp ⟶ G` such that `IsTorus T.toGrp` and
`IsClosedSubgroup i`. Let `j : C ⟶ G` be any homomorphism that represents
the published subgroup functor `torusCentralizer i` (`IsRepresentedBy`:
`j` is a monomorphism on points and its range is the functor) and is a
closed subgroup. The statement says that `C` is smooth over `Spec k`.

The source is Milne, *Algebraic Groups* (2017), source ID
`milne-2017-algebraic-groups`, Corollary 13.10, printed p.257 (one-based
PDF p.273): "Let H be a subgroup variety of a group variety G. If H is
of multiplicative type, then C_G(H) and N_G(H) are smooth." Only the
centralizer half is used. The correspondence is as follows.

- In Milne, a group variety is a smooth algebraic group, that is, a smooth
  group scheme of finite type over `k`. A smooth affine group scheme over a
  field is of finite type, so `G` is a group variety. Connectedness of `G`
  is not required, either here or in the source.
- `H` is the image of `i`. Since `i` is a closed immersion, `H` is
  isomorphic to `T`. It is a torus, so it is smooth and of multiplicative
  type, hence a subgroup variety of multiplicative type.
- Milne's `C_G(H)` (Proposition 1.92, printed p.33, one-based PDF p.49)
  represents the functor whose points over a `k`-algebra `R` are the
  `g ∈ G(R)` that commute with `H(R')` for every `R`-algebra `R'`. The Lean
  functor `torusCentralizer i` tests every `k`-scheme `U` and asks that `g`
  commute with every point of `T` after every refinement `V ⟶ U`. Both
  functors are Zariski sheaves and agree on affine test schemes, so
  `C_G(H)` represents `torusCentralizer i`. A representing monomorphism is
  unique up to unique isomorphism over `G`. Therefore every `j` in the
  statement has source isomorphic to `C_G(H)`, and smoothness transfers.

Existence of a closed representative is not part of this statement. The
Library proves it separately as `fieldCentralizerRepresentability`, which
needs only that `T` is affine over `k`.

This file only defines a proposition and proves nothing. The statement is
a premise of `MaximalTorusBaseChangeForwardReductionStatement`.
