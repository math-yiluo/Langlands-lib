# Standardization of Eisenstein series from available Bruhat–Tits data

Module `Langlands.Global.AdelicEisensteinStandardizationReduction`. Its main theorem,
`eisensteinStandardization_of_bruhatTitsAvailability`, proves
`EisensteinStandardizationStatement` (module `AdelicEisensteinStandardizationStatement`) from
one hypothesis, `BruhatTitsAvailabilityStatement` (module
`Langlands.Geometry.Building.BruhatTitsAvailabilityStatement`, the corrected Definition 4.1.26
conclusion of Kaletha–Prasad, Theorem 9.2.7). The hypothesis is used only to obtain, at each
finite place, a local compact subgroup in good position. The module
`AdelicEisensteinStandardizationProof` discharges the hypothesis.

## Sources

- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*,
  J. Amer. Math. Soc. 37 (2024), 187–234 (literature id
  `bernstein-lapid-2024-meromorphic-continuation-eisenstein`): §2.1, pp. 189–190 (standard
  parabolics of a fixed minimal parabolic and a maximal compact subgroup in good position) and
  §2.2, p. 191 (the twist \(\varphi_\lambda\) and the series (2.1)).
- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series* (1995)
  (literature id `moeglin-waldspurger-1995-spectral-decomposition`): I.1.4, pp. 4–5 (maximal
  compact subgroups in good position).

Provenance: derived. These sources work from the outset with standard parabolics and a compact
in good position. The proof follows the passage from an arbitrary parabolic and an arbitrary
maximal compact described in the Markdown of `EisensteinSystemDominationStatement` (section
"Changing the Iwasawa compact") and of `EisensteinStandardizationStatement` (section "Why it
holds").

## Auxiliary results

- `IsUnipotentRadical.range_comp_eq_of_iso`: if `e : P' ≅ P` satisfies `e.hom ≫ p = p'`, then
  ground-field unipotent radicals `i` of `P` and `i'` of `P'` have the same image in the
  ambient group, `range (i ≫ p) = range (i' ≫ p')`. The radical `i'` transported along `e`
  (`IsUnipotentRadical.comp_iso`) is a radical of `P`, two radicals of one group have the same
  image (`IsUnipotentRadical.range_eq`), and composition with `p` preserves the inclusions
  (`SubgroupFunctor.range_comp_mono`).
- `parameterRestrict_id` and `parameterRestrict_comp`: restriction of complex parameters
  \(X^*(H)\otimes\mathbb C\to X^*(H')\otimes\mathbb C\) along the identity is the identity, and
  along a composite it is the composite of the restrictions in reverse order (checked on pure
  tensors from `characterRestrict_id` and `characterRestrict_comp`).
- `parameterRestrictEquiv e`: for an isomorphism `e : H' ≅ H`, restriction along `e.hom` as a
  complex linear isomorphism, with inverse the restriction along `e.inv`;
  `parameterRestrictEquiv_apply` records that it is `parameterRestrict e.hom`.
- `complexParameterPairingAt G H`: the complex linear form
  \(\lambda\mapsto\langle\lambda,H\rangle\) (`complexParameterPairing`) for a fixed
  \(H\in\operatorname{Hom}(X^*(G),\mathbb R)\), with `complexParameterPairingAt_apply`.
- `comap_ofInfinite_conjugate`: the archimedean factor of \(T^{-1}KT\), for \(T=(t,1)\), is
  \(t^{-1}K_\infty t\), where \(K_\infty\) is the archimedean factor of \(K\).
- `subgroup_map_conj_map_conj_inv`: conjugating a subgroup by \(t\) and then by \(t^{-1}\)
  gives back the subgroup.

## The proof of `eisensteinStandardization_of_bruhatTitsAvailability`

Let \(p:P\to G\) be the parabolic with unipotent radical `iU`, Levi `l`, split component `a`
and root presentation `r`, let \(K\) be maximal compact with `hK : IsIwasawaCompact p K`, and
let \(\varphi\) be automorphic on \(U(\mathbb A)M(F)\backslash G(\mathbb A)\) for the
archimedean factor \(K_\infty\) of \(K\).

**The standard family.** The presentation supplies a maximal split torus `r.data.i` and a
generic cocharacter `r.data.ν`. The family `fam` is
`StandardParabolicFamily.ofMaximalSplitTorus` for these, and the index is
\(I=\) `r.data.J`. Both `fam.p I` and \(p\) have image the standard parabolic of
`r.data.J` (the `parabolic_eq` fields of the two compatibility proofs), so they have the same
image. Since both are closed subgroups, `IsClosedSubgroup.sourceIsoOfRangeEq` gives an
isomorphism \(e:P_I\cong P\) over \(G\), `e.hom ≫ p = fam.p I` (that is,
\(p\circ e=\) `fam.p I` in ordinary composition notation). Its homomorphism is the required
\(j\), and `iota` is `parameterRestrictEquiv e`, which is `parameterRestrict j`. The Levi images
agree (the `levi_eq` fields) and the unipotent radical images agree
(`IsUnipotentRadical.range_comp_eq_of_iso`), so the two inducing subgroups
\(U(\mathbb A)M(F)\) are equal (`parabolicQuotientSubgroup_eq_of_range_eq`).

**A compact in good position.** At each infinite place `infinitePlaceStandardLeviCompact`, and
at each finite place `finitePlaceStandardLeviCompactReduction` applied to the hypothesis, give
a local compact serving the minimal standard parabolic and meeting every standard Levi in a
maximal compact subgroup (`StandardParabolicFamily.IsStandardLeviCompact`).
`standardLeviCompactAssembly` assembles them into \(K'\) with
`IsParabolicIwasawaCompact` for the minimal standard parabolic \(P_\emptyset\) and maximal
compact intersections with all standard Levis. The minimal standard parabolic lies in \(P_I\)
(`StandardParabolicFamily.le_iff_range_le`), so `SubgroupFunctor.exists_factor_of_range_le` and
`IsParabolicIwasawaCompact.of_comp` give `hK' : IsIwasawaCompact (fam.p I) K'`, and
`IsIwasawaCompact.of_range_eq` gives the same for \(p\).

**The archimedean translate.** The archimedean factors of \(K\) and \(K'\) are maximal compact
in \(G(F_\infty)\) (`IsMaximalCompactSubgroup.isMaximalCompact_comap_ofInfinite`), so
`infiniteAdelicMaximalCompactConjugacy` gives \(t\) with \(K'_\infty=tK_\infty t^{-1}\). Put
\(T=(t,1)\), the point `ofInfinite F G t`. By `IsAutomorphicFunctionOn.infiniteRightTranslate`,
right translation by \(T\) carries functions automorphic for \(K_\infty\) to functions
automorphic for \(tK_\infty t^{-1}=K'_\infty\), with the same left invariance subgroup, `hcalc`
and `rho`. This is property 4.

**The finite change of compact.** Let \(C=T^{-1}K'T\). It is an Iwasawa compact for \(p\)
(`IsIwasawaCompact.conjInv`) and maximal compact (`IsMaximalCompactSubgroup.map_conj`, module
`AdelicEisensteinRootHyperplaneCompactReduction`). Its archimedean factor is
\(t^{-1}K'_\infty t=K_\infty\) (`comap_ofInfinite_conjugate`). For maximal compact subgroups
the archimedean factor is the infinite projection
(`IsMaximalCompactSubgroup.comap_ofInfinite_eq_map_infinite`, same module), so \(K\) and \(C\)
have the same infinite projection. Then
`IsAutomorphicFunctionOn.exists_parameterTwist_of_infinite_eq` (the proof of
`EisensteinFiniteCompactChangeStatement`) gives a finite set \(S\) of real dual elements and
functions \(\varphi_v\), \(v\in S\), automorphic on \(U(\mathbb A)M(F)\backslash G(\mathbb A)\)
for \(K_\infty\), such that
\[
\varphi_{\lambda,K}=\sum_{v\in S}e^{\langle\lambda,v\rangle}\,(\varphi_v)_{\lambda,C}
\]
for all \(\lambda\). Since \(K_\infty\) is also the archimedean factor of \(C\),
`EisensteinAbsoluteConvergenceStatement.exists_summable_eisensteinTerm` applied to
`eisensteinAbsoluteConvergence` gives for each \(v\) a threshold \(R_v\) above which the terms of
\(E_{P,C}(\varphi_v,\lambda)(x)\) are summable at every \(x\). Put
\(R=\sum_{v\in S}\max(R_v,0)\). An \(R\)-regular parameter is \(R_v\)-regular for every \(v\).

**New inducing data.** Enumerate \(S\) by \(\mathrm{Fin}\,m\) (`Finset.equivFin`). The function
\(\varphi'_i\) is \(x\mapsto\varphi_{v_i}(xT)\) and the linear form is
\(\ell_i(\lambda)=\langle\lambda,v_i+H_C(T)\rangle\), where \(H_C\) is the Iwasawa height of
\(C\). Each \(\varphi'_i\) is automorphic for \(K'_\infty\) by `infiniteRightTranslate`, with
the inducing subgroup of \(P\) replaced by the equal one of \(P_I\); the commutator datum enters
only as a proof of a proposition, so `hcalc` may be replaced by the one used by
`StandardParabolicFamily.IsAutomorphicOn`. This is property 3.

**Regularity.** The family's presentation of \(P_I\) has the same torus, cocharacter and
index as `r` and the same Weyl group instance (the instance is a subsingleton).
`eisensteinRegularityParabolicTransport`, applied to \(j\) with `j ≫ p = fam.p I` (that is,
\(p\circ j=\) `fam.p I`), shows that \(\lambda\) is \(R\)-regular for `r` exactly when \(\iota(\lambda)\) is \(R\)-regular for
the family's presentation. This gives property 5 with \(R'=R\).

**The comparison.** Let \(\lambda\) be \(R\)-regular and \(g\in G(\mathbb A)\).

1. By the twist identity and summability, `IsIwasawaCompact.eisensteinSeries_eq_finset_sum_of_twist` gives
   \(E_{P,K}(\varphi,\lambda)(gT)=\sum_{v\in S}e^{\langle\lambda,v\rangle}E_{P,C}(\varphi_v,\lambda)(gT)\).
2. By `IsIwasawaCompact.eisensteinSeries_mul_conjInv` (with \(K'\) and \(C=T^{-1}K'T\)),
   \(E_{P,C}(\varphi_v,\lambda)(gT)=e^{\langle\lambda,H_C(T)\rangle}E_{P,K'}(\varphi_v(\cdot\,T),\lambda)(g)\);
   the factor is `heightPower`.
3. By `IsIwasawaCompact.eisensteinSeries_eq_of_range_eq` along \(j\),
   \(E_{P,K'}(\psi,\lambda)(g)=E_{P_I,K'}(\psi,\iota\lambda)(g)\).

Reindexing the sum over \(S\) by \(\mathrm{Fin}\,m\) (`Fintype.sum_equiv`) and combining the two
exponentials gives property 6:
\[
E_{P,K}(\varphi,\lambda)(gT)=\sum_{i<m}e^{\ell_i(\lambda)}E_{P_I,K'}(\varphi'_i,\iota\lambda)(g).
\]
Properties 1 and 2 were established with the family and \(K'\).
