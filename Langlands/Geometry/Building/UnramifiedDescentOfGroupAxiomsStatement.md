# Group-valid data from unramified descent

`UnramifiedDescentOfGroupAxiomsStatement` starts with a datum \(D\) satisfying
the one-group clauses of corrected Definition 4.1.26. It asks for a datum
\(D'\) for the same group and field satisfying those clauses and
`SatisfiesUnramifiedDescent`. The `KPBuildingAssignment.DatumIndex` ranges
over connected reductive groups over nonarchimedean local fields of either
characteristic in universe `u`. The statement also asks for a
`KPBuildingDatum.BuildingEquivalence` from \(D\) to \(D'\), respecting facets
and apartments, affine in both directions on apartment charts, and
equivariant for the identity of \(G(F)\). For the same-group comparison see
KP Proposition 7.9.5 and
`ValuationBuildingData.exists_isEquivariantBuildingIso_id`.

This existential form follows the construction in KP §§9.2.1–9.2.5 and
the group-axiom verification in §9.5. `SatisfiesUnramifiedDescent` identifies
the reduced building and apartments of \(D'\) with the fixed loci of the
coefficient action and compares affine roots in the set form of UR 3.
For each actual nonempty bounded apartment subset of \(D'\), its two
models recover the smooth affine models over \(\mathcal O_K\) characterized
by the full and neutral fixer subgroups of the image. Corollary 2.10.11
uses these points over the strictly Henselian valuation ring, and §9.2.5
descends the corresponding models. The same witness \(D'\) must have these
models and satisfy every one-group axiom.
[Unramified descent of KP building data](FullValidity/UnramifiedDescent.md)

The one-group axioms permit a different full model over \(F\) with the
same \(\mathcal O_F\)-points. For example let \(F=\mathbb Q_5\),
\(E=F(r)\) with \(r^3=5\), and \(H=\operatorname{Res}^{1}_{E/F}\mathbb G_m\).
The cubic remains Eisenstein over \(K\), so \(H\) is anisotropic over
both fields and its reduced building is a point. The integral norm-one
model \(M\) has equation \(N_{E/F}(a+br+cr^2)=1\). This equation is monic
in \(a\), giving flatness, and its special-fibre equation \(a^3=1\) is
smooth in characteristic 5. All norm-one elements over \(K\) are units
in \(\mathcal O_K[r]\), so \(M(\mathcal O_K)=H(K)^1\). By Theorems
8.3.2 and 8.3.13 and Corollary 2.10.11, the relative identity component
\(P\) of \(M\) gives \(H(K)^0\) over \(\mathcal O_K\). Its special fibre
is the unipotent group of principal units in the truncated polynomial ring.

The only cube root of unity in \(\mathbb F_5\) is \(1\), so every
\(H(F)\)-point reduces into the neutral component. Definition 2.5.13 gives
\(H(F)^0=H(F)^1=P(\mathcal O_F)\). On the one-point building \(P\) can thus
be used as both models for the integral-point clauses of Axiom 4.1.20.
The comparisons are identities, and the neutral model, trivial split
torus and trivial reductive quotient give the same one-group clauses.
Over \(K\) a primitive cube root of unity belongs to \(H(K)^1\) and has
nontrivial reduction in the component group. The base change of \(P\)
therefore misses that element of the full fixer. The existential statement
selects models with the two required base changes.

Sources are Kaletha and Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Definition 2.5.13 and Corollary 2.10.11 (pp. 90 and 124, PDF pp. 121 and 155),
Definition 4.1.26 and Axiom 4.1.27 (pp. 165–166, PDF pp. 196–197),
Proposition 7.9.5 (p. 276, PDF p. 307), Theorems 8.3.2 and 8.3.13 (pp. 296
and 299, PDF pp. 327 and 330), §§9.2.1–9.2.5 (pp. 325–328, PDF pp. 356–359),
Proposition 9.4.28 (pp. 359–360, PDF pp. 390–391) and §9.5 (pp. 363–364,
PDF pp. 394–395). See the authors' *Corrections and additions* (1 November
2024), PDF pp. 27, 37 and 39, for the corrected axiom list, connected-model
point characterization and Galois fixed-point arguments.
