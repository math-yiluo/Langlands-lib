# Rational points of finitely generated algebras over an algebraically closed field

Worker 1497.

Three general commutative-algebra facts used in the proof of the
Kostant–Rosenlicht theorem
(`Langlands.GroupScheme.UnipotentAffineOrbitClosedStatement`; Milne,
*Algebraic Groups* (2017), Theorem 17.64). They are standard; this module
derives them from Mathlib and introduces no definitions.

Throughout the first section `k` is an algebraically closed field and `A` a
finitely generated commutative `k`-algebra.

- `exists_algHom_ker_eq` (Hilbert's Nullstellensatz): every maximal ideal `m`
  of `A` is the kernel of a `k`-algebra map `χ : A →ₐ[k] k`. Proof: `A ⧸ m` is
  a field that is a finitely generated `k`-algebra, hence a finite extension
  (`finite_of_finite_type_of_isJacobsonRing`); since `k` is algebraically
  closed, `k → A ⧸ m` is bijective
  (`IsAlgClosed.algebraMap_bijective_of_isIntegral`). Composing the quotient
  map with the inverse isomorphism gives `χ`.
- `eq_zero_of_forall_algHom`: if `A` is moreover reduced and `a : A` vanishes
  at every `k`-point, then `a = 0`. Proof: `A` is a Jacobson ring
  (`isJacobsonRing_of_finiteType`), every maximal ideal is the kernel of a
  `k`-point, so `a` lies in the Jacobson radical of `⊥`, which equals the
  nilradical; reducedness gives `a = 0`.

The last result has no field:

- `eq_empty_of_isConstructible`: in the prime spectrum of a Jacobson ring, a
  constructible set containing no maximal ideal is empty. Proof: write the
  set as a finite union of pieces `zeroLocus (range g) \ zeroLocus {f}`
  (`PrimeSpectrum.exists_constructibleSetData_iff`). Each piece is locally
  closed, and in a Jacobson space a nonempty locally closed set contains a
  closed point (`nonempty_inter_closedPoints`); closed points of the
  spectrum are the maximal ideals
  (`PrimeSpectrum.isClosed_singleton_iff_isMaximal`).
