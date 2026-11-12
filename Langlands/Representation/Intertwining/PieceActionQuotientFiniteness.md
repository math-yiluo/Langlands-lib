# Finite action quotients on geometric-lemma pieces

This module proves that a split component acts through a finite-dimensional quotient of
its group algebra in two settings: on admissible, finitely generated Jacquet modules, and
on the pieces `i^L_{Q'} ∘ ι ∘ r^M_{P'}` of the represented geometric lemma. These finiteness
facts are the hypotheses of the spectral criterion
`pqRegularity_of_disjoint_generalizedCharacters` (Renard VII.3). The provenance is
internal, and the module makes no literature claim of its own. It uses the helpers of
`Langlands.Representation.Intertwining.CentralActionQuotientFiniteness`.

## Ambient statements

These are stated for a represented parabolic `P = MN` of `G` (`p, l, r, hp, hl, hr, hmul`).

- `groupAlgebraKernel_le_leviInduction`: let `b : B → M` be a map whose composite
  `aG = b ≫ l ≫ p` lands in the center of `G(F)`. Then every element of `ℂ[B(F)]` that kills
  `τ ∘ b` also kills `i_P^G(τ) ∘ aG`. In the proof, the central elements `j t` of `P(F)`
  act on the inducing representation through `τ ∘ b`, because the modulus half-character
  is trivial on the center (`closedHalfCharacter_eq_one_of_mem_center`). The
  evaluations `f ↦ f(x)` (`Induction.centralEvaluation`) are then `B(F)`-equivariant. They
  are jointly injective by `Induction.exists_smoothInduced_eval_ne_zero`, and
  `groupAlgebraKernel_le_of_jointlyInjective` applies. The proof sets the finite heartbeat
  limit `4000000`.
- `finite_actionQuotient_leviJacquet`: if the Jacquet module `r_P(π)` is admissible and
  finitely generated over `ℂ[M(F)]`, then a split component `a : A → M` acts on it through
  a finite-dimensional quotient. Admissibility makes the center act locally finitely
  (`CentralDecomposition.admissible_centerFinite`), and
  `finite_actionQuotient_of_locallyFinite` applies.
- `finite_normalizedJacquetExponents_of_leviJacquet`: under the same hypotheses, the set of
  normalized Jacquet exponents of `π` along `a` is finite. Each exponent is a generalized
  eigencharacter of `r_P(π) ∘ a` (`isNormalizedJacquetExponent_iff_leviJacquet`), and
  `finite_generalizedEigencharacters` applies.

## Pieces of the geometric lemma

`GeometricLemmaIntersectionDatum.finite_actionQuotient_piece` takes a datum `D` for the
double coset of `z` and a split component `a : A → L` of the Levi of `Q`. It also takes a
factorization `b ≫ D.lQ' ≫ D.q' = a` through the Levi `L'` of `Q' = Q ∩ z⁻¹Pz`. Suppose the
Jacquet module `J = r^M_{P'}(σ)` is admissible and finitely generated over `ℂ[M'(F)]`. Then
`a` acts on the piece `D.pieceFunctor.obj σ` through a finite-dimensional quotient.

The image of `b` is central in `L'(F)`. This follows from the injectivity of
`L'(F) → L(F)` and the centrality of `a`. Transporting along the conjugation isomorphism
`D.e : L'(F) ≃ M'(F)` gives the map `κ = b ≫ φ : A(F) → M'(F)` with central image.
Admissibility of `J` and `finite_actionQuotient_of_locallyFinite` give a finite action
quotient for `J ∘ κ`. `groupAlgebraKernel_le_leviInduction`, applied to the induction from
`Q'` to `L`, shows that the kernel for `J ∘ κ` is contained in the kernel on the piece.
Finally `finite_actionQuotient_of_kernel_le` transfers finiteness to the piece.
