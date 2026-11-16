# Local division algebras isomorphic to their opposites

This internal contribution generalizes the published residue argument in
`LocalUnitaryResidue` from involutions to scalar-fixing algebra
anti-equivalences. It proves an arithmetic obstruction; it does not prove
the local rank-one Tits-index enumeration.

`Langlands.HasAlgebraAntiEquivalence K D` is the proposition
`Nonempty (D ≃ₐ[K] Dᵐᵒᵖ)`. Here `K` is a field, `D` is a division ring
and `D` is an algebra over `K`. Thus an actual algebra isomorphism with
the multiplicative opposite is required. Its underlying map fixes the
scalar field. It need not be involutive.

The theorems
`Langlands.AlgebraAntiEquivalence.reducedDegree_dvd_two` and
`Langlands.HasAlgebraAntiEquivalence.reducedDegree_dvd_two` state that
the reduced degree divides two when `K` is a nonarchimedean local field
and `D` is a finite-dimensional central division algebra over `K`.
The first takes a specified algebra anti-equivalence; the second takes
the proposition above. The corollary
`Langlands.not_hasAlgebraAntiEquivalence_of_two_lt` excludes such an
anti-equivalence whenever the reduced degree is greater than two.
These results hold at every universe parameter and impose no restriction
on field or residue characteristic.

The proof is implemented as follows.

1. For an algebra equivalence `f : D ≃ₐ[K] Dᵐᵒᵖ`, `tau f` is
   `MulOpposite.unop ∘ f`. It is injective and additive, fixes scalars,
   and reverses products. Polynomial induction proves compatibility with
   evaluation in one element. Mapping the minimal-polynomial equation
   forward gives one divisibility; injectivity applied to the equation
   for the image gives the reverse divisibility. Monicity gives equality
   of minimal polynomials.
2. The published dimension formula
   `UnitaryInvolution.finrank_eq_natDegree_mul_adjoinRank` and positivity
   of the minimal-polynomial degree identify the two adjoin ranks.
   `UnitaryInvolution.norm_eq_minpoly_coeff` then proves equality of the
   regular norms. These two imported formulas do not assume an involution.
3. The published comparison between the valuation of the regular norm
   and a positive power of `localReducedNormValuation` proves valuation
   preservation. Therefore `tau` preserves the integer subring and its
   strict ideal. The induced `tauResidue` is a ring endomorphism: reversal
   of multiplication disappears in the commutative division residue field.
4. Write `t` for this residue map and `ψ` for conjugation on the residue
   field by a unit `j`. Product reversal gives
   `conjResidue (tauUnit f j) (t (ψ s)) = t s`.
   Valuation preservation and
   `DivisionValuation.conjResidue_eq_of_value_eq` identify conjugation
   by `tauUnit f j` with `ψ`. Endomorphisms of the finite residue field
   commute, by `UnitaryInvolution.finiteField_ringHom_comm`.
   Consequently `t (ψ (ψ s)) = t s`; injectivity of the ring
   endomorphism `t` implies `ψ (ψ s) = s`. This cancellation uses no
   assertion that `t` or `tau` is involutive.
5. The published
   `CentralDivision.exists_unit_conjResidue_faithful` supplies a unit
   whose residue conjugation detects divisibility by the reduced degree.
   Applying its criterion to exponent two proves the bound.

The helper definitions and theorems are in
`Langlands.AlgebraAntiEquivalence`. The purely algebraic evaluation
lemmas need no locality or centrality; minimal-polynomial and norm
comparison additionally require finite dimensionality. The valuation and
residue arguments have the local and central hypotheses stated above.
`tauUnit` is a function on units, with no claim that it preserves their
multiplication.

The provenance is an internal generalization of the existing implemented
norm and residue arguments, rather than a transcription of an additional
literature assertion. No relative-Weyl symmetry is converted here into an
anti-equivalence of an anisotropic kernel algebra. That geometric bridge
and the remaining Tits-index exclusions remain open.
