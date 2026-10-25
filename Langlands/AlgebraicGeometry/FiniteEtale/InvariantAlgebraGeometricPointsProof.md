# Geometric points of finite invariant algebras

The theorem
`Langlands.AlgebraicGeometry.FiniteEtale.invariantAlgebraGeometricPoints`
proves the published proposition `InvariantAlgebraGeometricPoints R A G Ω`.
It retains all four type parameters in one arbitrary universe `u` and all
instances from the statement: a noetherian commutative base ring `R`, a finite
étale commutative `R`-algebra `A`, a finite group `G` acting by compatible
semiring automorphisms, and an algebraically closed `R`-field `Ω`.

Write `C = FixedPoints.subalgebra R A G`. The result says that restriction
from `A →ₐ[R] Ω` to `C →ₐ[R] Ω` is surjective, and that two restrictions
are equal exactly when `y = x.comp (MulSemiringAction.toAlgHom R A g)` for
some `g : G`. This is equality of complete algebra homomorphisms, including
their specified values in `Ω`, not merely equality of kernels.

## Implemented proof

Three private helpers are proved in this module.

1. `exists_orbit_value` concerns ring homomorphisms `x,y : A →+* K` into a
   domain, agreeing on every invariant element. For `a : A`, the orbit
   polynomial `∏ g, (T - g • a)` has invariant coefficients, by Mathlib's
   `MulSemiringAction.smul_coeff_charpoly`. Its images under `x` and `y`
   therefore agree. Evaluation at `y a` is zero, so one factor is zero:
   `y a = x (g • a)` for some `g`. No division by the group order occurs.
2. `exists_orbit_hom` makes this group element independent of `a`. If no
   group element works on all inputs, choose a witness `a g` against each
   `g`. Enumerate `G` by `e : G ≃ Fin (Fintype.card G)` and put these witnesses
   in distinct coefficients of `p = ∑ g, monomial (e g).val (a g)` in `A[X]`.
   Extend `x` and `y` coefficientwise to `K[X]`, which is still a domain.
   An invariant polynomial has invariant coefficients, so these extended
   maps agree on invariant polynomials. Applying the first helper to `p`
   produces a `g` with `map y p = map x (g • p)`. Its coefficient at `e g`
   contradicts the chosen witness for that same `g`. Consequently a single
   `g` matches the entire original homomorphism.
3. `exists_extension_of_integral` treats an injective integral extension
   `C → A` and a ring homomorphism `f : C →+* K` into an algebraically closed
   field. The prime `P = ker f` has a prime `Q` above it by Mathlib's
   `Ideal.nonempty_primesOver`. Both quotient rings are domains; `A/Q` is
   integral over `C/P`, and the kernel lift embeds `C/P` into `K`.
   `IsAlgClosed.lift` supplies a `C/P`-algebra map from `A/Q` into `K`.
   Composing with the quotient map gives an extension of exactly `f`.

For the main theorem, the actual inclusion `C → A` is injective, and every
invariant element is by definition in its image. Thus
`Algebra.IsInvariant.isIntegral C A G` supplies integrality. Apply the third
helper to a given `R`-algebra homomorphism `C → Ω`; its extension respects
`R` because its restriction to `C` is the original map. This proves
surjectivity. For the forward orbit implication apply the second helper to
the underlying ring homomorphisms and use algebra-homomorphism extensionality.
The reverse implication follows directly because `g` fixes every element of
`C`.

The private arguments work without noetherianity, module finiteness or
étaleness; the public theorem retains these hypotheses to match the exact
published interface. They require no faithful or free group action, no
invertible group order, and no assumed geometric quotient or Galois-category
classification. The statement module and its imports are unchanged.

## Source and provenance

The original source is Grothendieck et al., *SGA 1, Revêtements étales et
groupe fondamental*, recomposed edition, arXiv `math/0206203v2`, registered
as `sga1-arxiv-math-0206203v2`, SHA256
`8e64218d356456c534eebf996940f0f957e43b54f1a080241debe12cbaf60d3c`.
Exposé V, Proposition 1.1(i)–(iii), printed page 88 / one-based PDF page 104,
gives integrality, prime-orbit fibres, and the residual normality and
stabilizer-surjectivity statements underlying the geometric-Hom translation.

This module proves the published derived translation by a different,
elementary route. Its polynomial witness argument proves the full Hom-orbit
assertion directly, so it does not need to construct residual automorphisms.
The three private helpers are internal derivations for this proof, not
additional claims quoted verbatim from SGA 1. Their ingredients are the
Mathlib orbit-polynomial and integral-extension APIs, principally
`Mathlib.RingTheory.Invariant.Basic`, `Mathlib.RingTheory.Ideal.GoingUp`, and
`Mathlib.FieldTheory.IsAlgClosed.Basic`, at the project's pinned environment.

The implementation uses no proof holes or new axioms; its inspected
assumptions are `propext`, `Classical.choice`, and `Quot.sound`.
