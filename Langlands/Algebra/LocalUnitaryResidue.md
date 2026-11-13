# Unitary involutions on local division algebras: residue action and degree bound

Helper module for the proof of `Langlands.LocalUnitaryDivisionCommutativeStatement`.

## Finite fields

* `finiteField_ringHom_comm`: any two ring endomorphisms of a finite field commute. They are
  automorphisms, hence `ZMod p`-algebra automorphisms (`RingHom.ext_zmod`), and the Galois group
  of a finite field is cyclic.
* `finiteField_involution_eq`: if `ψ` and `t` are involutive ring endomorphisms of a finite
  field and `ψ` is not the identity, then `t` is the identity or `t = ψ`. In the cyclic group
  `Gal(F/ZMod p)` at most two elements square to one (`IsCyclic.card_pow_eq_one_le`), while
  otherwise `1`, `ψ`, `t` would be three distinct such elements.

## The local setting

`L` is a nonarchimedean local field, `D` a finite-dimensional central division `L`-algebra,
`v = localReducedNormValuation L D`, `σ : L →+* L` preserves the valuation of `L`
(`hσ : ∀ c, valuation L (σ c) = valuation L c`), and `τ` is a unitary involution relative to `σ`.
The residue field of `D` is finite and commutative (Library).

* `valuation_tau`: `v (τ x) = v x`. The Library identity
  `valuation L (Algebra.norm L x) = v x ^ reducedDegree L D` together with `norm_tau` and `hσ`
  gives equal powers, and powers are injective in the value group.
* `tauInteger`, `tauReductionHom`, `tauResidue`: `τ` preserves the integers and the strict ideal,
  so it induces a map of residue fields, which is a ring homomorphism because the residue field
  is commutative; `tauResidue_tauResidue` says it is involutive.
* `tauResidue_conj`: `conjResidue (τ j) ∘ tauResidue ∘ conjResidue j = tauResidue`, from
  `τ (j x j⁻¹) = (τ j)⁻¹ (τ x) (τ j)`.
* `conjResidue_conjResidue`: conjugation by any unit `j` acts on the residue field as an
  involution. Since `v (τ j) = v j`, `conjResidue (τ j) = conjResidue j`; combining with
  `tauResidue_conj` and the commutation of all endomorphisms of the finite residue field gives
  `ψ (ψ (t s)) = t s`, and `t` is surjective.
* `reducedDegree_dvd_two` (**Part I**): `reducedDegree L D ∣ 2`, by applying
  `exists_unit_conjResidue_faithful` with `n = 2`.
* `false_of_residue_moved` (**unramified case**): if `reducedDegree L D = 2` and some `θ ∈ L`
  has `valuation L θ ≤ 1` and `valuation L (σ θ - θ) = 1`, contradiction. With `u` from
  `exists_unit_conjResidue_faithful`, `ψ = conjResidue u` is a nontrivial involution, so by
  `finiteField_involution_eq` the residue involution `tauResidue` is the identity or `ψ`. Both fix
  the residue of `θ` (`ψ` because `θ` is central), whereas `tauResidue` moves it because
  `v (σ θ - θ) = valuation L (σ θ - θ) ^ 2 = 1`.
