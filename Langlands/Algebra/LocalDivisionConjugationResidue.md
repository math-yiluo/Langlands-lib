# Conjugation on the residue ring of a division-ring valuation

Helper module for the proof of `Langlands.LocalUnitaryDivisionCommutativeStatement`.

## General valuations (`Langlands.DivisionValuation`)

Let `v : Valuation D Γ₀` be a valuation on a division ring with values in a linearly ordered
commutative group with zero, and `Residue v` its residue division ring (the quotient of
`v.integer` by the strict ideal, from `Langlands.Algebra.DivisionValuationResidue`).

* `conj_value`: `v (j * x * j⁻¹) = v x` for a unit `j`, since the values commute.
* `conjInteger v j : v.integer →+* v.integer` is `x ↦ j x j⁻¹`, and
  `conjResidue v j : Residue v →+* Residue v` the induced map (it preserves the strict ideal).
* `conjResidue_mul`, `conjResidue_one`, `conjResidue_pow` (`conjResidue v (j ^ n)` is the
  `n`-th iterate) follow from the corresponding identities in `D`.
* `conjResidue_of_value_eq_one`: if the residue ring is commutative and `v j = 1`, then
  conjugation by `j` acts trivially (it is conjugation by the residue unit of `j`).
* `conjResidue_eq_of_value_eq`: if the residue ring is commutative and `v j = v k`, then
  `conjResidue v k = conjResidue v j`, because `k = j · (j⁻¹ k)` with `v (j⁻¹ k) = 1`.

## Local central division algebras (`Langlands.CentralDivision`)

`exists_unit_conjResidue_faithful K D`: for a central division algebra `D` over a
nonarchimedean local field `K`, with valuation `localReducedNormValuation K D`, there is a unit
`u` such that whenever `conjResidue (u ^ n)` is the identity, `reducedDegree K D ∣ n`.

Proof. The Library theorem `exists_localDivision_fullResidue_polynomial_subfield` gives an
integral `b` whose subfield `E = K(b)` has full residue field and `[E : K]` equal to the residue
degree, together with a monic integral polynomial with separable reduction. Repeating the
argument of `exists_localDivision_fullResidue_cyclic_subfield` shows that `E/K` is Galois and
that the reduction map `localDivisionSubfieldGaloisReduction` from `Gal(E/K)` to the residue
automorphisms is injective (`localDivisionSubfieldGaloisReduction_injective`); hence `Gal(E/K)`
is cyclic, and by `localDivisionResidue_finrank_eq_reducedDegree` a generator `g` has order
`reducedDegree K D`. Skolem–Noether (`fieldEmbeddingsConjugate`) gives a unit `u` with
`g a = u a u⁻¹` for `a ∈ E`, hence `g^n a = u^n a u^{-n}`. If `conjResidue (u ^ n)` is the
identity, then the reduction of `g ^ n` fixes every residue (the residue map of `E` is
surjective), so `g ^ n = 1` by injectivity and the order of `g` divides `n`.
