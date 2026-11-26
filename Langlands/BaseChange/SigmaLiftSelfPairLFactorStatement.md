# Local self-pair Euler identity for a σ-lift

`Langlands.BaseChange.SigmaLiftSelfPairLFactorStatement.{u, v, uV, uW}` is a
proposition over bundled finite extensions `F : PadicField.{u} p` and
`E : PadicField.{v} p` of `Padic p`. It takes the relative algebra structure
and scalar tower, `IsModuleTopology F.Carrier E.Carrier`, a cyclic algebra
certificate `IsCyclicAlgebra σ l`, and a residue degree certificate
`IsResidueDegree F.Carrier E.Carrier f`. The cyclic degree `l` is arbitrary.
Both fields use their `canonicalTopologicalData`, which fixes the topologies,
valuative relations, and local-field instances.

At any positive rank `n`, the lower action `π` on `V : Type uV` is irreducible
and satisfies `JacquetLanglands.IsSquareIntegrable`. The upper action `P` on
`W : Type uW` satisfies `IsSigmaDiscreteSeries σ n P`. Both have supplied
admissibility proofs for the induced matrix group topologies.
The lift hypothesis is `IsSigmaLift σ l π hπ P hP A c`, using a
`SigmaIntertwiner σ n P` and the distributional comparison constant `c`.
For this hypothesis, `LocalFieldTopology.generalLinear_t2Space`,
`generalLinear_locallyCompactSpace`, and
`generalLinear_totallyDisconnectedSpace` supply the instances on each
general linear group. `IsSigmaLift` installs the corresponding group Borel
structures internally.

Henniart–Lemaire II.2.9, Remarque (5), gives the lift of \(\pi^\vee\) as
\(P^\vee\), with intertwiner on the dual given by precomposition with
\(A^{-1}\). The contragredients remain discrete and σ-discrete, respectively.
Taking these as the second pair in II.4.6, Théorème (4), gives
\[
  L_E(z,P\times P^\vee)
    = \prod_{\kappa\in K(E/F)}
        L_F(z,\pi\times((\kappa\circ\det)\otimes\pi^\vee)).
\]
Lean uses `smoothContragredient` for both duals. Membership in the supplied
`Finset` `X` is equivalent to `IsNormTrivial E.Carrier κ`, which means
triviality on \(N_{E/F}(E^\times)\). This realizes the full character group
\(K(E/F)\) from II.1.3. In this p-adic setting the norm subgroup is open
and of finite index, so these homomorphisms are smooth characters.

Over a field \(K\) with residue cardinality \(q_K\), the absolute value is
normalized by \(\lvert\varpi_K\rvert_K=q_K^{-1}\) for a uniformizer
\(\varpi_K\). `IsPadicRankLPolynomial` certifies the reciprocal polynomial
description \(L_K(z)=1/Q_K(q_K^{-z})\) with constant coefficient one.
The residue degree certificate gives \(q_E=q_F^f\), so
\(q_E^{-z}=(q_F^{-z})^f\). With \(T=q_F^{-z}\), equality of the reciprocal
Euler factors gives \(Q_E(T^f)=\prod_{\kappa\in X}Q_F(\kappa)(T)\) by
inverting the nonzero rational functions. Lean states this polynomial
equality as `Q_E.comp (Polynomial.X ^ f) = ∏ κ : X, Q_F κ`, where `κ : X`
indexes the subtype of characters in the `Finset`.

On each field the statement quantifies over a `UnitaryAdditiveCharacter`
(which includes nontriviality) and its `SelfDualHaar` for the canonical
topology and Borel structure. These choices are independent across the
fields. The equal-rank zeta integrals use the quotient Haar measure, and
character scaling preserves the normalized polynomial, as in
`RankinSelberg.isPairLPolynomial_characterChange_canonical`.
The certificates for the upper polynomial and all the lower polynomials
are hypotheses of the equality.

## Sources

- G. Henniart and B. Lemaire, *Changement de base et induction automorphe pour
  GLₙ en caractéristique non nulle*, Mém. SMF 124 (2011). II.4.6, Théorème (4),
  printed p. 89 (PDF p. 97), gives the pair comparison. II.2.9, Remarque (5),
  printed p. 70 (PDF p. 78), gives the dual lift, and II.4.12, Proposition,
  printed p. 96 (PDF p. 104), displays the self-pair formula. II.1.3, printed
  p. 56 (PDF p. 64), defines \(K(E/F)\). II.6.19, printed pp. 133–134 (PDF
  pp. 141–142), proves the comparison in positive characteristic. The retained source ID is
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`
  and its SHA-256 is `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.
  [NUMDAM edition](https://www.numdam.org/item/MSMF_2011_2_124__1_0/)
- J. Arthur and L. Clozel, *Simple Algebras, Base Change, and the Advanced
  Theory of the Trace Formula* (1989), Chapter 1, Proposition 6.9(i), printed
  p. 60 (PDF p. 74), gives the characteristic-zero comparison. The
  determinant-twist convention is on printed p. 61 (PDF p. 75), and the
  proof of (i) is in §6.4, printed pp. 61–69 (PDF pp. 75–83).
  The retained source ID is `arthur-clozel-1989-base-change`
  and its SHA-256 is `c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
  [Arthur's collected works copy](https://www.claymath.org/library/cw/arthur/pdf/30.pdf#page=74)
