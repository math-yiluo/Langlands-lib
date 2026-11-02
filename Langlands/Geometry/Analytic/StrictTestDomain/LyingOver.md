# Lying over for finite bounded maps of Banach algebras

Author: Worker 1010.

Fix a nontrivially normed field K with ultrametric absolute value, and complete
normed commutative K-algebras A and B.

## The completed residue field is nontrivially normed

`BanachSpectrum.completedResidueNontriviallyNormedField x` makes the completed
residue field H(x) of a point x of M(A) a nontrivially normed field. H(x)
contains K isometrically (`norm_algebraMap'`), so the image of an element of K
of norm greater than one has norm greater than one in H(x). The definition is
reducible and only adds this witness to the published normed-field structure.

## Lying over

`BanachSpectrum.exists_comap_eq_of_finite` assumes K complete, a bounded
K-algebra map `i : A → B` that is finite as a ring map
(`i.toAlgHom.toRingHom.Finite`, so B is a finite A-module through i), and a
point x of M(A) that vanishes on the kernel of i. It concludes that x is the
restriction `comap i y` of some point y of M(B).

The proof:

1. The kernel p of x is prime, because the residue domain A/p is a domain.
   B is integral over A and the kernel of i lies in p. So going up
   (Mathlib's `Ideal.exists_ideal_over_prime_of_isIntegral`) gives a prime q of
   B with preimage p in A.
2. Let Ω be the algebraic closure of H(x) with Mathlib's spectral norm
   (`spectralNorm.normedField`); it extends the norm of H(x). Let ρ : A → Ω be
   the completed residue map followed by the inclusion. Then ‖ρ a‖ = x a, and
   the kernel of ρ is p.
3. ρ descends to an injective map A/p → Ω. B/q is a domain that is integral,
   hence algebraic, over A/p, and torsion free over it. Mathlib's
   `IsAlgClosed.lift` therefore gives an A/p-algebra map φ : B/q → Ω. Let ψ be
   B → B/q followed by φ. Then ψ(i a) = ρ a for every a in A.
4. ψ is an A-algebra map from B to Ω. Here A acts on Ω through ρ, which is
   bounded with constant 1 because x a ≤ ‖a‖. B is finite over A. So the
   published `FiniteBanachAlgebra.exists_norm_bound` gives M ≥ 0 with
   ‖ψ b‖ ≤ M‖b‖. Hence ψ is a bounded ring map.
5. Let y be the restriction along ψ of the norm point of Ω (`fieldPoint`).
   Then y(i a) = ‖ψ(i a)‖ = ‖ρ a‖ = x a, so `comap i y = x`.

## Scope and provenance

This is an internal supporting result for the strict local
rational-neighbourhood theorem (`StrictTestDomain.LocalRationalNeighborhoodStatement`).
It will be used together with the finiteness criterion and the quotient tests
(`StrictTestDomain.exists_idempotent_of_zeroLocus_subset`).
It is a Banach-spectrum form of the familiar lying-over property of finite
morphisms: a finite map is surjective onto the zero locus of its kernel. The
proof above is written directly for this Library from going up, algebraic
closure and the finite Banach-algebra norm bound. It cites no specific
numbered external result. Both A and B are arbitrary complete
normed K-algebras; no presentation, strictness or Noetherian hypothesis is used.
