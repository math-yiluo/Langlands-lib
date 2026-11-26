# Herbrand's subgroup formula for the absolute Galois group of a finite subextension

`Langlands.Ramification.Local.absoluteHerbrandSubgroupFormula` proves
`AbsoluteHerbrandSubgroupFormula` from
`Langlands.LocalFactor.Ramification.Herbrand.LocalSubextensionStatement`, in
three independent universes `u₀`, `uK`, `uΩ` and with no hypothesis on the
characteristic. For a finite intermediate field \(E\) of a separable closure
\(\Omega/K\), every real \(u\ge -1\) and every
\(\tau\in\operatorname{Aut}_E(\Omega)\), it gives
\[
  \tau|_K\in G_K^{u}\iff \tau\in G_E^{\psi_{E/K}(u)},
  \qquad\text{that is}\qquad G_K^{u}\cap G_E=G_E^{\psi_{E/K}(u)},
\]
where the absolute groups are `absoluteUpperRamificationGroup` over the base
\(K_0\) with the norm comparison `hbase`, \(\tau|_K\) is
`τ.restrictScalars K`, and \(\psi_{E/K}\) is `relativeHerbrandPsi`. With
\(K_0=K\) a nonarchimedean local field of either characteristic this is the
formula for `localAbsoluteUpperRamificationGroup` and
`localRelativeHerbrandPsi`.

The proof uses three published results:

- `upperRestrictionCompatibility` (`Herbrand.LocalTowerProof`): for a tower
  \(K\to E'\to L\) of finite Galois extensions and arbitrary realizations
  \(T\) of \(L\) and \(S\) of \(E'\) over \(K_0\), the image of the upper group
  \(G(L/K)^v\) under normal restriction is \(G(E'/K)^v\), for \(v\ge -1\)
  (Serre IV §3, Proposition 14, deduced there from Lemma 5, "Herbrand's
  theorem");
- `finiteHerbrandSubgroupFormula` (`Herbrand.LocalFiniteSubgroupProof`): in one
  realization \(T\) of a finite \(M\) and for \(\sigma\in\operatorname{Aut}_E(M)\),
  \(\sigma|_K\in G(M/K)^u\) exactly when
  \(\sigma\in G(M/E)^{\varphi_{M/E}(\psi_{M/K}(u))}\);
- `relativeHerbrandPsiIndependence`
  (`Herbrand.LocalRelativePsiIndependenceProof`): \(\psi_{E/K}(u)\) equals
  `relativeIndex K₀ K hbase M h u`, that is
  \(\varphi_{M/E}(\psi_{M/K}(u))\) computed in the canonical realization of
  \(M\) viewed over \(E\), for every finite Galois intermediate field
  \(M\supseteq E\) of \(\Omega/K\).

The module does not use `FiniteHerbrandTransport`
(`Herbrand.LocalTransportStatement`); the one comparison of realizations it
needs is obtained from `upperRestrictionCompatibility`, as described below.

## Restriction along an algebra map (section `Restriction`)

The fields \(K\), \(L\), \(E'\) carry the hypotheses of
`upperRestrictionCompatibility`: \(L\) and \(E'\) are finite over \(K_0\),
\(K\to E'\to L\) is a scalar tower compatible with \(K_0\), and \(L/K\),
\(E'/K\), \(L/E'\) are Galois.

- `restrictNormalHom_eq_of_commutes`: if \(\rho\in\operatorname{Aut}_K(L)\) and
  \(\rho'\in\operatorname{Aut}_K(E')\) satisfy
  \(\iota(\rho'(x))=\rho(\iota(x))\) for the algebra map
  \(\iota\colon E'\to L\), then \(\rho'\) is the normal restriction
  `AlgEquiv.restrictNormalHom E' ρ`. The proof is
  `AlgEquiv.restrictNormal_commutes` and injectivity of \(\iota\).
- `mem_upperRamificationGroup_of_commutes`: for such a compatible pair and
  \(v\ge -1\), \(\rho\in G(L/K)^v\) (realization \(T\)) implies
  \(\rho'\in G(E'/K)^v\) (realization \(S\)). By the previous lemma \(\rho'\) is
  the restriction of \(\rho\), which lies in the image computed by
  `upperRestrictionCompatibility K L E' T S v`.
- `mem_upperRamificationGroup_iff_of_surjective`: if moreover \(\iota\) is
  surjective, the implication is an equivalence. Given \(\rho'\in G(E'/K)^v\),
  `upperRestrictionCompatibility` gives \(\rho_1\in G(L/K)^v\) whose
  restriction is \(\rho'\). For \(y=\iota(x)\),
  \(\rho_1(y)=\iota(\rho'(x))=\rho(y)\) by `AlgEquiv.restrictNormal_commutes`
  and the compatibility, so \(\rho_1=\rho\).

The last lemma is the comparison of two realizations: when \(\iota\) is an
isomorphism, the kernel of the restriction is trivial, and Herbrand's quotient
theorem says that \(\rho\) and \(\rho'\) have the same upper depth.

## Finite Galois subfields of the ambient field (section `Ambient`)

`restrictNormalHom_mem_canonicalUpperRamificationGroup_of_le` takes a base field
\(F\) finite over \(K_0\), an extension \(\Omega/F\) with compatible tower
\(K_0\to F\to\Omega\), finite Galois intermediate fields \(N\le M\) of
\(\Omega/F\), \(v\ge -1\) and \(\tau\in\operatorname{Aut}_F(\Omega)\). If the
restriction of \(\tau\) to \(M\) lies in
`canonicalUpperRamificationGroup K₀ M hbase F v`, then its restriction to \(N\)
lies in `canonicalUpperRamificationGroup K₀ N hbase F v`. The proof makes \(M\)
an algebra over \(N\) by `IntermediateField.inclusion`; \(M/N\) is Galois by
`IsGalois.tower_top_of_isGalois`. The restrictions of \(\tau\) to \(N\) and to
\(M\) are a compatible pair, since both act as \(\tau\) on elements of
\(\Omega\) (`AlgEquiv.restrictNormalHom_apply`), and
`mem_upperRamificationGroup_of_commutes` applies with the two canonical
realizations. The lemma is used with \(F=K\) and with \(F=E\).

## One finite Galois field (section `Subextension`)

Fix \(M\), a finite Galois intermediate field of \(\Omega/K\), and
`h : ∀ x : E, algebraMap E Ω x ∈ M`. The field `extendFiniteGalois h` is \(M\)
viewed as a finite Galois intermediate field of \(\Omega/E\); write
\(N\) for it. The carriers of \(M\) and \(N\) are different types with the same
elements, and `relativeIndex K₀ K hbase M h u` is computed in the canonical
realization \(T\) of \(N\).

- `neg_one_le_relativeIndex`: for \(u\ge -1\),
  \(-1\le\)`relativeIndex K₀ K hbase M h u`. After unfolding, the index is
  \(\varphi^T_{N/E}(\psi^T_{N/K}(u))\); both functions are strictly monotone
  (`herbrandPsi_strictMono`, `herbrandPhi_strictMono`) and fix \(-1\)
  (`herbrandPsi_neg_one`, `herbrandPhi_neg_one`).
- `restrictNormalHom_restrictScalars_mem_iff`: for \(u\ge -1\) and
  \(\tau\in\operatorname{Aut}_E(\Omega)\), the restriction of \(\tau|_K\) to
  \(M\) lies in `canonicalUpperRamificationGroup K₀ M hbase K u` exactly when
  the restriction of \(\tau\) to \(N\) lies in
  `canonicalUpperRamificationGroup K₀ N hbase E (relativeIndex K₀ K hbase M h u)`.
  The proof makes \(N\) an algebra over \(M\) by the identity of carriers
  `extendFiniteGaloisEquiv h`, whose algebra map is surjective; \(N/M\) is
  Galois by `IsGalois.tower_top_of_isGalois`. The restriction of \(\tau|_K\) to
  \(M\) and the automorphism `(τ restricted to N).restrictScalars K` of \(N\)
  are a compatible pair, both acting as \(\tau\). Hence
  `mem_upperRamificationGroup_iff_of_surjective` turns the left side into
  membership of `(τ restricted to N).restrictScalars K` in the upper group of
  \(N/K\) at \(u\) for the realization \(T\). The finite formula
  `finiteHerbrandSubgroupFormula` for \(K\to E\to N\) and \(T\) turns this into
  membership of the restriction of \(\tau\) to \(N\) in the upper group of
  \(N/E\) at \(\varphi^T_{N/E}(\psi^T_{N/K}(u))\), which is
  `relativeIndex K₀ K hbase M h u` by definition.

## The theorem

After the three instances of the statement (\(E\) finite over \(K_0\), the
tower \(K_0\to E\to\Omega\), `IsSepClosure E Ω`), write
\(\psi=\psi_{E/K}(u)\). It satisfies \(\psi\ge -1\) by
`neg_one_le_relativeIndex` for the normal closure `galoisClosure E`, which is how
`relativeHerbrandPsi` is defined. Both sides are rewritten by
`mem_absoluteUpperRamificationGroup_iff` into conditions on all finite Galois
intermediate fields.

- (⇒) Let \(N\) be a finite Galois intermediate field of \(\Omega/E\). Then
  \(N\) is finite over \(K\) (`FiniteDimensional.trans K E N`), and its normal
  closure \(M\) over \(K\) in \(\Omega\) is a finite Galois intermediate field
  of \(\Omega/K\) (`normalClosure.is_finiteDimensional`,
  `IsGalois.normalClosure`, with \(\Omega/K\) Galois as a separable closure).
  It contains \(N\) (`AlgHom.fieldRange_le_normalClosure`), hence \(E\). The
  hypothesis at \(M\) and `restrictNormalHom_restrictScalars_mem_iff` put the
  restriction of \(\tau\) to `extendFiniteGalois h` in the upper group of
  \(E\) at `relativeIndex K₀ K hbase M h u`, which equals \(\psi\) by
  `relativeHerbrandPsiIndependence`. Since \(N\le\)`extendFiniteGalois h`,
  `restrictNormalHom_mem_canonicalUpperRamificationGroup_of_le` over \(F=E\),
  at the index \(\psi\ge -1\), gives the condition at \(N\).
- (⇐) Let \(L\) be a finite Galois intermediate field of \(\Omega/K\), and
  \(M=L\sqcup\)`galoisClosure E`, which contains \(E\)
  (`algebraMap_mem_galoisClosure`). The hypothesis at `extendFiniteGalois h`,
  with \(\psi\) rewritten by `relativeHerbrandPsiIndependence` as
  `relativeIndex K₀ K hbase M h u`, and
  `restrictNormalHom_restrictScalars_mem_iff` put the restriction of
  \(\tau|_K\) to \(M\) in the upper group of \(K\) at \(u\). Since \(L\le M\),
  `restrictNormalHom_mem_canonicalUpperRamificationGroup_of_le` over \(F=K\),
  at \(u\ge -1\), gives the condition at \(L\).

## Source

Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg, GTM 67,
Springer (1979), Chapter IV, §3, registered as `serre-1979-local-fields`
(SHA256 `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`):
Proposition 14 (printed p. 74, proved p. 75 from Lemma 5, "Herbrand's
theorem"), Proposition 15 (printed p. 74, proved p. 75), Remarks 1, 2 and 3
(printed pp. 75–76). The statement is the profinite
form of Remark 3, with the upper filtration of Remark 1 and the function
\(\psi_{E/K}\) of Remark 2. The proof above passes to finite levels as Remark 1
does, and uses Herbrand's theorem both to move between finite Galois fields and
to compare the two realizations of one field.
