# Central maximal tori under field extension: statement

Worker 1379.

`CentralMaximalTorusBaseChangeStatement.{u}` concerns a field extension
`K/k` with both fields in `Type u` and `Algebra k K`, a smooth affine
group scheme `H` over `Spec k`, a commutative group scheme `Z`, and a
homomorphism `j : Z.toGrp ⟶ H`. Suppose `IsCentral j` (every point of
`Z` maps into the published centre of `H`) and `IsMaximalTorus j`. Then
the base-changed homomorphism `Z_K.toGrp ⟶ H_K` is again
`IsMaximalTorus`. The base change uses the published commutative and
ordinary group-scheme base-change functors along
`Spec K ⟶ Spec k`, exactly as in `MaximalTorusBaseChangeStatement`.

`IsMaximalTorus j` already contains `IsTorus Z.toGrp` and
`IsClosedSubgroup j`. Maximality over `K` is tested against every closed
torus of `H_K`, including tori that are not base changes of tori over
`k`.

This is the forward implication of Milne, *Algebraic Groups* (2017),
source ID `milne-2017-algebraic-groups`, Theorem 17.82, printed p.379
(one-based PDF p.395): "Let G be a group variety over k and let k' be a
field containing k. A torus T in G is maximal if and only if T_{k'} is
maximal in G_{k'}." It is specialized in two ways:

1. Only the implication from `k` to `K` is stated.
2. The torus is central. This is the case to which Milne's proof reduces
   the theorem: `T` is maximal in `G` if and only if it is maximal in the
   centralizer `C_G(T)`, and `T` is central there.

The ambient group is smooth and affine over a field, hence of finite type,
hence a group variety in Milne's sense. Connectedness is not required, as
the source first passes to the identity component. The extension `K/k`
is arbitrary; it may be inseparable or transcendental.

The source's proof of this case uses that `T` is maximal in `C` exactly
when `C/T` contains no nontrivial torus (16.43), Grothendieck's theorem
that a connected group variety without nontrivial tori is unipotent
(17.81), and invariance of unipotence under field extension (14.9). None of
these is formalized here.

This file only defines a proposition and proves nothing. The statement is
a premise of `MaximalTorusBaseChangeForwardReductionStatement`.
