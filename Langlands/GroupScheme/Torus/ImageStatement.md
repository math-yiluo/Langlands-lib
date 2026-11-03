# A homomorphism from a torus factors through a closed torus: statement

Worker 1395.

`TorusImageClosedTorusStatement.{u}` concerns a field `k : Type u`, a group
scheme `H` over `Spec (CommRingCat.of k)` such that `H.X.hom` is smooth and
affine, and a group scheme `E` over `Spec k` with `IsTorus E`. It asserts
that every homomorphism `e : E ⟶ H` factors as `f ≫ j = e`, where
`Z` is a commutative group scheme over `Spec k` with `IsTorus Z.toGrp`,
`j : Z.toGrp ⟶ H` satisfies `IsClosedSubgroup j` (the underlying morphism
of schemes is a closed immersion), and `f : E ⟶ Z.toGrp` is a homomorphism.

This file only defines a proposition and proves nothing. It is a premise
of [`CentralMaximalTorusQuotientReductionStatement`](CentralMaximalQuotientReduction.md).

## Source

Milne, *Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`.
The statement is derived; it is not a numbered result of Milne in this
form.

- Theorem 5.39 (homomorphism theorem), printed p.108 (one-based PDF
  p.124): "Every homomorphism of algebraic groups φ: G → H factors into a
  composite of homomorphisms G → I → H with q faithfully flat and i a
  closed immersion." Milne calls `I` the image of `φ`.
- §12.e, after Definition 12.14, printed p.236 (one-based PDF p.252): "A
  quotient of a split torus is again a split torus. ... It follows that a
  quotient of a torus is a torus."

## Derivation

`H` is smooth, hence locally of finite type, and affine over `Spec k`, so
it is an algebraic group. A torus is an algebraic group. Theorem 5.39
factors `e` as `E → I → H` with `E → I` faithfully flat and `I → H` a
closed immersion. `I` is a quotient of the torus `E`, so it is a torus,
and it is commutative because `E` is. Take `Z = I`, `j` the closed
immersion and `f` the quotient map.

## Correspondence with the source

- `IsTorus` is the Library's definition from `Torus.Lattice`: split after
  base change to some field extension of `k` (Milne, Definition 12.14).
- The conclusion asks only for some closed torus through which `e`
  factors, not for the image itself, and does not ask `f` to be faithfully
  flat. This weaker form is what its consumer needs: it compares the closed
  torus `j` with a maximal torus.
- `E` is not required to be commutative as a group scheme object; it is
  commutative because it is a torus.
