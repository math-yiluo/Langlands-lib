# Raynaud's criterion for semiabelian reduction

## Rational geometric torsion

`Langlands.AbelianScheme.HasRationalGeometricTorsion B n` concerns an
abelian variety `B` over a field `K` and a natural number `n`. A point of
`B` with values in the algebraic closure `AlgebraicClosure K` is a morphism
from `Spec (AlgebraicClosure K)`, viewed over `Spec K`, to `B`. The
predicate asserts that every such point killed by `n` (an element of
`Langlands.GroupScheme.torsionPoints B.toGrp n`) is the composite of the
spectrum map `Spec (AlgebraicClosure K) → Spec K` with a section of `B`
over `Spec K`. In other words, all `n`-torsion points of `B` over an
algebraic closure are defined over `K`.

When `n` is invertible in `K`, the `n`-torsion of `B` is finite étale over
`K`. Its points over the algebraic closure are then its points over the
separable closure. The predicate is thus the usual condition that the
`n`-torsion subgroup `B_n ⊆ B(K_s)` consists of `K`-rational points.

## The statement

`Langlands.AbelianScheme.RaynaudSemiabelianCriterionStatement` fixes a
discrete valuation ring `V` with fraction field `K`, an abelian variety `B`
over `K`, and a Néron model `N` of `B` over `V` with its generic
identification. It takes a natural number `n` with `3 ≤ n` that is a unit
of `V`. Since `V` is local, the second condition says that the residue
characteristic of `V` does not divide `n`. If all `n`-torsion points of `B`
over an algebraic closure of `K` are defined over `K`, the statement
asserts `N.HasGeometricSemiabelianReduction`. This is the Library's
predicate from `Langlands.AbelianScheme.PotentialSemistableReductionStatement`.
It says that the identity component of the geometric special fibre of `N`,
over the algebraic closure of the residue field, is an extension of an
abelian variety by a split torus. The torus is the scheme-theoretic kernel
of a smooth surjective homomorphism onto the abelian variety.

## Provenance

This is Raynaud's criterion in the form of Silverberg and Zarhin,
*Semistable reduction and torsion subgroups of abelian varieties*, Ann.
Inst. Fourier 45 (1995), §3, printed p. 406 (PDF p. 5), Theorem 3.5, for
`n ≥ 3`. Their proof reference is SGA 7 I, Exposé IX, Proposition 4.7. The
source states the theorem for an abelian variety over a field with a
discrete valuation. There `n` is not divisible by the residue
characteristic, and the points of `X_n` are defined over an extension
unramified over `v`. The conclusion is semistable reduction at `v`, defined
in §3, printed p. 405 (PDF p. 4), Definition 3.1 (ii). That definition
requires the identity component of the special fibre of the Néron model to
be an extension of an abelian variety by an affine torus. `X_n` is the
`n`-torsion of `X(F_s)`, by the notation of §2, printed p. 404 (PDF p. 3).

The Lean statement makes the following choices.

- The valuation is that of the discrete valuation ring `V`, and `K` is its
  fraction field. This is the source's valuation ring `R` of `v`.
- The hypothesis takes the trivial unramified extension `K` itself, so the
  statement is the special case of the source in which the `n`-torsion is
  already rational over `K`.
- Semistable reduction is expressed over the algebraic closure of the
  residue field. An extension of an abelian variety by a torus over the
  residue field stays one after this field extension, the torus becoming
  split. Bosch, Lütkebohmert and Raynaud, *Néron Models* (1990), §7.4,
  printed p. 181, define semi-abelian reduction by the same condition on
  the identity component of the special fibre.
- `N` is an arbitrary Néron model of `B` over `V` in the sense of the
  Library's `NeronModel`. Néron models are unique up to unique isomorphism,
  so the source's Néron model is one of them.
