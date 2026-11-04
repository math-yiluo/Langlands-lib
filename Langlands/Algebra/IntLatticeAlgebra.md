# Group algebras of finite integer lattices

Worker 1395 wrote this module. It proves three facts about the group algebra
`AddMonoidAlgebra R (I → ℤ)` of a finite integer lattice: the ring of Laurent
polynomials over `R` in variables indexed by a finite type `I`. The module is
an internal helper for the proof of
[`CentralTorusExtensionStatement`](../GroupScheme/Torus/CentralExtensionProof.md).
These are standard facts of commutative algebra. They are not taken from a
numbered result of a source.

## Contents

* `optionEquiv R I`: the `R`-algebra isomorphism
  `R[ℤ^(Option I)] ≃ (R[ℤ^I])[ℤ]`, built from `ℤ^(Option I) ≃ ℤ × ℤ^I` and
  `AddMonoidAlgebra.curryAlgEquiv`. `optionEquiv_symm_single_single` computes
  its inverse on monomials.
* `lattice e` and `congrEquiv R e`: the lattice isomorphism `ℤ^I ≃ ℤ^J` and the
  algebra isomorphism `R[ℤ^I] ≃ R[ℤ^J]` induced by `e : I ≃ J`.
* `uniqueFactorizationMonoid_laurent`: the Laurent polynomial ring over a unique
  factorization domain is a unique factorization domain. It is the localization
  of the polynomial ring at the powers of `X`, and Mathlib's
  `UniqueFactorizationMonoid.of_isLocalization` applies.
* `uniqueFactorizationMonoid R I`: for a unique factorization domain `R` and a
  finite type `I`, `R[ℤ^I]` is a unique factorization domain. The proof is by
  `Finite.induction_empty_option`: an empty index type gives `R`, an index
  type `Option I` gives a Laurent ring over `R[ℤ^I]` via `optionEquiv`, and
  `congrEquiv` handles a change of index type.
* `exists_eq_single_of_isUnit R I`: over a domain `R`, every unit of `R[ℤ^I]` is
  a monomial `single m c` with `c` a unit of `R`. The proof uses the same
  induction. The Library's `Gm.exists_eq_C_mul_T_of_isUnit` from
  `Langlands.GroupScheme.Torus.Lattice` covers one Laurent variable, and the
  induction hypothesis handles the coefficient.
* `subsingleton_pic K I`: over a field `K`, the Picard group
  `CommRing.Pic (AddMonoidAlgebra K (I → ℤ))` is trivial. The ring is a unique
  factorization domain, hence a GCD domain. `infer_instance` then finds
  Mathlib's instance that the Picard group of a GCD domain is trivial
  (`Mathlib.RingTheory.PicardGroup`).
