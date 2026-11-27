# From the close-fields Galois quotients to Weil orbit counts

## Statement

`Langlands.Henniart.CloseFieldsTwistCountFromGaloisQuotientStatement.{u, uW}`
asserts that the filtered absolute Galois quotient comparison implies the count
form of E1a. Its premise is
`Langlands.Ramification.Local.CloseFieldsGaloisQuotientStatement.{u}` and its
conclusion is `Langlands.Henniart.CloseFieldsTwistCountStatement.{u, uW}`.
The implication uses the same field universe `u` in both statements and the
independent representation-carrier universe `uW` in the count statement.

For every prime \(p\) and p-adic field \(K\), let \(e=e_K\) be its absolute
ramification index and \(X=\mathbb F_q((t))\) the Laurent-series field over its
residue field. The premise gives an isomorphism of topological groups
\(\phi\colon G_K/G_K^e \simeq G_X/G_X^e\) carrying the image of \(G_K^v\) onto
that of \(G_X^v\) for \(0\le v\le e\). The conclusion is \(T_K(d,s)=T_X(d,s)\)
for \(d\ge 1\) and \(0\le s<de\). Here \(T\) is the extended cardinality of the
stratum of unramified-twist orbits of irreducible complex Weil representations
of rank \(d\), Swan exponent \(s\) and torsion number one. Lean uses \(d=k+1\)
for \(k\in\mathbb N\).
[`CloseFieldsStatement`](../LocalFactor/Ramification/CloseFieldsStatement.md),
[`HenniartCloseFieldsStatement`](HenniartCloseFieldsStatement.md).

Applying this implication to the published theorem
`Langlands.Ramification.Local.closeFieldsGaloisQuotient` gives E1a in the form
of `CloseFieldsTwistCountStatement`. The Lean module defines the implication.
[`CloseFieldsGaloisQuotientProof`](../LocalFactor/Ramification/CloseFieldsGaloisQuotientProof.md).

## Mathematical origin

- *Formalizing the large external inputs of the local Langlands correspondence
  for GL_n*, `external-inputs-plan.tex`, §4.3, lines 574–576, gives the Galois
  form of E1a and passes to orbits via finite-image representatives and
  finite-order unramified characters. Source `operator-external-inputs-plan-2026-11-16`,
  registered SHA-256 `c429afd5b4f28270a0619b3292f8825a9bfa77c3d842ac3a2a81fc2042cc0463`.
- *The numerical local Langlands correspondence for GL_n*, `numerical-LLC-route.tex`,
  proof of Proposition `prop:LD`, lines 826–830, gives the corresponding
  passage from filtered Weil quotients to count equality. Theorem `thm:Deligne`,
  lines 861–872, gives the count comparison, whose torsion-number-one case is
  \(T_K(d,s)=T_X(d,s)\) by §2.2, lines 182–201.
  Source `operator-numerical-llc-route-2026-11-16`,
  registered SHA-256 `faece16e4d4722c37c1ba0e7ebba30a11d94b64639f20f19a6aa7ccff3faba3f`.
- Henniart, *La conjecture de Langlands locale numérique pour GL(n)* (1988),
  §5.1, printed p. 512, transports irreducible classes of the specified rank
  and Swan exponent across the filtered Galois quotient isomorphism,
  compatibly with unramified twists. Source `henniart-1988-numerical`,
  SHA-256 `3de93884b6c4b26106d614e648cfb7f293f9f40a66ef352c0751e222a602f25c`.

## Proof route

1. Fix \(K,k,s\) with \(s<(k+1)e\) and choose \(\phi\) from the premise. On
   each field, the orbit dictionary carries `LocalNumerical.weilRefinedStratum`
   at \(k,s,1\) onto `LocalNumerical.galoisRefinedStratum` at the same indices.
   For `F : PadicField p`, the p-adic stratum unfolds to the general one on
   `F.Carrier` with `AlgebraicClosure F.Carrier` and the canonical local-field
   data. On \(X\) use `SeparableClosure X`.
   [`HenniartGaloisDictionaryStatement`](HenniartGaloisDictionaryStatement.md),
   [`HenniartLocalNumerical`](HenniartLocalNumerical.md).
2. For an irreducible Galois class in this stratum, use its Weil pullback to
   read the upper break. The single break \(\lambda\) satisfies \(s=d\lambda\)
   for \(d=k+1\). In the Lean count, the Swan exponent is the Artin exponent
   minus \(d\) in \(\mathbb N\). The Artin–Swan identity recovers this exponent
   from the Swan conductor at a finite inertia presentation. By normality
   and irreducibility the inertia-fixed space is zero or the whole carrier.
   In the latter case both conductors vanish and the natural subtraction
   gives zero. At nonnegative indices the Weil upper group is the preimage
   of the corresponding Galois upper group, and the Weil projection maps
   onto that group because it maps onto inertia. On the p-adic side the
   comparison of the upper filtrations reduces to comparing the canonical
   valuation rings on each finite Galois subextension of `F.Carrier`.
   Since \(\lambda=s/d<e\), the Galois representation is trivial on \(G^e\)
   and factors through \(G/G^e\).
   [`LocalWeilBreakStatement`](../LocalFactor/Ramification/LocalWeilBreakStatement.md),
   [`Herbrand.GeneralAbsolute`](../LocalFactor/Ramification/Herbrand/GeneralAbsolute.md).
3. Precomposition with \(\phi\) and its inverse gives inverse transports on
   finite-image irreducible classes factoring through the quotients, preserving
   rank. A class trivial on \(G^e\) has break bounded by \(e\). The break is
   the infimum of the nonnegative indices of trivial action, so the test on
   \(0\le v\le e\) alone recovers it on the quotient. The filtration comparison
   preserves those tests, hence the break. It also preserves the dimension
   of the inertia-fixed space at \(v=0\). The Swan formula and Artin–Swan
   identity therefore preserve the integer Artin witness used in
   `LocalNumerical.HasWeilSwan`. The comparison at \(v=0\) identifies
   the images of absolute inertia. Since
   \(G^e\subseteq G^0=I\), it induces \(G_K/I_K\simeq G_X/I_X\). Continuous
   complex characters of these profinite quotients have finite image.
   Precomposition identifies the unramified character groups, and
   equivariance for twisting identifies the stabilizers and hence the torsion
   numbers.
   [`Herbrand.LocalAbsoluteStatement`](../LocalFactor/Ramification/Herbrand/LocalAbsoluteStatement.md).
4. The transport therefore gives a bijection of the Galois refined strata.
   Apply the two orbit dictionaries to obtain a bijection of the Weil refined
   strata. Their `Set.encard` values are the two counts.

## Published statements used in the route

| Declaration | Role |
| --- | --- |
| `Langlands.Ramification.Local.CloseFieldsGaloisQuotientStatement` | Supplies the filtration-preserving topological isomorphism. |
| `Langlands.Henniart.WeilGaloisOrbitDictionaryStatement` | Identifies the refined strata via an equivalence of orbit types. The theorem is `Langlands.Henniart.weilGaloisOrbitDictionary`. |
| `Langlands.Ramification.Local.WeilIrreducibleUpperBreak` and `Langlands.Ramification.Local.WeilIrreducibleSwanBreak` | Identify the single break and compute the Swan conductor as rank times that break. |
| `Langlands.Ramification.Local.WeilIrreduciblePositiveThresholds` and `Langlands.Ramification.Local.FiniteUpperBreakArtinIdentity` | Give the strict triviality threshold at positive indices and relate the Artin exponent to the Swan conductor and the inertia-fixed codimension. |
| `Langlands.Ramification.Local.ContinuousWeilFiniteInertiaPresentationStatement` and `Langlands.Ramification.Local.WeilInertiaRestrictionSurjectivityStatement` | Supply the finite presentations with surjective inertia restriction used in the conductor definitions. |
| `Langlands.Ramification.Local.AbsoluteUpperInertia` | Identifies \(G^0\) with absolute inertia over either field. The theorem is `Langlands.Ramification.Local.absoluteUpperInertia`. |
