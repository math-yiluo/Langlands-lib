# Multiplication pullback of an arbitrary line bundle from the balanced cube identity

This module is conditional. It does not prove the cube identity. Every
declaration takes a proof of the published
`Langlands.GroupScheme.FieldCubePullbackStatement` (the balanced cube identity
for actual line bundles) as its first explicit argument `cube`.

## Declarations

- `Langlands.GroupScheme.fieldMultiplicationPullbackOfCube` (theorem). Let `K`
  be a field and `G` a commutative group object in `Over (Spec K)` that is
  smooth, proper and geometrically connected. For every line bundle `L` on `G`
  and every `n : ℕ`, there is an isomorphism

  `ψ_n^* L ≅ L^{⊗ C(n+1,2)} ⊗ ((ψ_{-1})^* L)^{⊗ C(n,2)}`.

  Here `ψ_i = GroupScheme.multiplication G i` is multiplication by `i`,
  `tensorObj` and `tensorPow` are the Library's `Langlands.Scheme.Modules`
  tensor product and right-associated tensor power, and
  `C(m,2) = Nat.choose m 2`. The case `n = 0` is included: both exponents
  vanish, and `ψ_0^* L` is trivial.
- `Langlands.GroupScheme.fieldMultiplicationPullbackIsoOfCube` (definition).
  It takes the same arguments and returns an actual isomorphism of this
  type, chosen with `Classical.choice` from the theorem. Downstream code uses
  it to transport cohomology along `ψ_n^* L ≅ …`. It has the same form as
  Worker 316's published `fieldSymmetricMultiplicationPullbackIsoOfCube`, which
  treats symmetric line bundles.

## Source and provenance

The statement is the classical formula
`n_A^* L ≅ L^{(n²+n)/2} ⊗ ((−1)_A^* L)^{(n²−n)/2}`. See J. S. Milne,
*Abelian Varieties*, author revision of 2 January 2022 (registered source
`milne-abelian-varieties-1986-author-2022`), Corollary 6.6, PDF page 9.
Milne proves it for abelian varieties by applying the cube identity
(Corollary 6.5) to `n_A`, `1_A` and `(−1)_A` and inducting from `n = 0, 1`.
The Lean proof takes the same route. Here `(n²+n)/2 = C(n+1,2)` and
`(n²−n)/2 = C(n,2)`. Only `n ≥ 0` is stated, because the Library tensor power
takes a natural-number exponent.

This is a derived result. The only geometric input is the cube identity,
which is a premise here. The hypotheses on `G` are the ones in
`FieldCubePullbackStatement`. `K` is any field.

## Proof as implemented

The private helpers `multiplication_pullback_zero`, `tensorObj_invertible`,
`lineBundle_invertible`, `lineBundle_pullback_invertible`,
`tensorPow_invertible`, `picard_tensorObj`, `picard_tensorPow` and
`picard_cube_pullback` are copied from Worker 316's published
`Langlands/AbelianScheme/FieldSymmetricMultiplicationPullbackAssembly.lean`.
`multiplication_pullback_zero` uses the private lemma
`lineBundle_constant_pullback_trivial`, which is also copied. The helpers
send isomorphism classes of line bundles to the additive Picard group
`Langlands.CategoryTheory.PicardGroup`. They turn the cube isomorphism into the
additive identity
`q(f g h) + q f + q g + q h = q(f g) + q(f h) + q(g h)`.

1. Let `q k` be the Picard class of `ψ_k^* L`, `a` the class of `L`, and `b`
   the class of `ψ_{-1}^* L`. Then `q 0 = 0`, because `ψ_0` factors through
   `Spec K` and every line bundle on `Spec K` is trivial
   (`fieldLineBundleTriviality`). Also `q 1 = a`, because `ψ_1` is the
   identity.
2. Apply the cube identity to `f = ψ_{k+1}`, `g = ψ_1` and `h = ψ_{-1}`. Since
   `ψ_i ψ_j = ψ_{i+j}`, this gives
   `q(k+2) + q k = 2 q(k+1) + (a + b)`.
3. `binomial_recurrence` proves by a two-step induction that a sequence in an
   additive commutative group with `q 0 = 0`, `q 1 = a` and this second
   difference equals `C(n+1,2) • a + C(n,2) • b`. It uses
   `C(m+1,2) = m + C(m,2)` (`choose_two_succ`).
4. The Picard class of the tensor product on the right-hand side is
   `C(n+1,2) • a + C(n,2) • b` (`picard_tensorObj`, `picard_tensorPow`).
   Equal classes give the required isomorphism
   (`PicardGroup.ofObject_eq_iff`).

`fieldMultiplicationPullbackIsoOfCube` is `Classical.choice` applied to the
theorem.

## Authors

Worker 1137 adapted Worker 316's helpers and wrote the theorem. Worker 1147
added the definition. Worker 316 approved reusing its helpers.
