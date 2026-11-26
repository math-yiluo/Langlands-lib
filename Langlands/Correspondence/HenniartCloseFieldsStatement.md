# Close-fields comparison of torsion-number-one Weil orbit counts

## Statement

Let \(p\) be a prime and \(K\) a p-adic field with absolute ramification index
\(e_K=v_K(p)\) and residue field \(\mathbb F_q\), and let
\(X=\mathbb F_q((t))\) be the Laurent-series field over that residue field.
For every rank \(d\ge 1\) and every Swan exponent \(s\ge 0\) with
\(s<d\,e_K\),
\[
T_K(d,s)=T_X(d,s).
\]
For a nonarchimedean local field \(E\), \(T_E(d,s)\) is the number of
unramified-twist orbits of continuous irreducible complex \(d\)-dimensional
representations of the Weil group of \(E\) with Swan exponent \(s\) and torsion
number \(1\), that is, fixed by no nontrivial unramified twist. There is no
condition \(s\ge 1\): Swan exponent zero is included.

`Langlands.Henniart.CloseFieldsTwistCountStatement.{uK, uW}` states this for every
prime `p`, every `F : PadicField.{uK} p` and all natural numbers `k` and `s`
with `s < (k + 1) * F.canonicalTopologicalData.ramificationIndex`, for the rank
\(d=k+1\):

```lean
Numerical.weilTwistIrreducibleCount.{uK, uW} F k s =
  LocalNumerical.weilTwistIrreducibleCount
    (LaurentSeries (Weil.Local.localResidueField F))
    (SeparableClosure (LaurentSeries (Weil.Local.localResidueField F))) k s
```

The statement asserts the equality only. It does not assert that the counts
are finite.

## The Lean names

- **The count for \(K\).** `Langlands.Henniart.Numerical.weilTwistIrreducibleCount.{uK, uW} F k s`
  is the p-adic count of the module
  [`Langlands.Correspondence.HenniartRefinedStrata`](HenniartRefinedStrata.md):
  the extended cardinality in `ℕ∞` of the stratum
  `Numerical.weilRefinedStratum F k s 1` of unramified-twist orbits of the Weil
  group of `F.Carrier` over `AlgebraicClosure F.Carrier`. It is the count used by
  the (LD) statement `Langlands.Henniart.LaumonDeligneCountStatement`
  ([HenniartLaumonDeligneStatement](HenniartLaumonDeligneStatement.md)). It is,
  by unfolding of definitions, the general count below at `F.Carrier` and
  `AlgebraicClosure F.Carrier` with the canonical local-field data of `F`; the
  section "P-adic specialization" of
  [`Langlands.Correspondence.HenniartLocalNumerical`](HenniartLocalNumerical.md)
  checks this by `rfl`.
- **The count for \(X\).** `Langlands.Henniart.LocalNumerical.weilTwistIrreducibleCount K Ω k s`
  is the general count of
  [`Langlands.Correspondence.HenniartLocalNumerical`](HenniartLocalNumerical.md)
  for a nonarchimedean local field `K` and a separable closure `Ω`: the
  extended cardinality in `ℕ∞` of the set of unramified-twist orbits of
  rank-`k + 1` classes of continuous irreducible complex representations of the
  Weil group with Swan exponent `s` and torsion number `1`. The Weil group,
  geometric degree and unramified characters are those of
  `Langlands.Weil.Local.SepClosed`; the Artin exponent, from which the Swan
  exponent is the rank subtracted in `ℕ`, uses the finite inertia presentations
  of `Langlands.Ramification.Local.SepClosed`. Both sides of the statement are
  therefore the same definition, evaluated at two fields.
- **The field \(X\).** `X` is `LaurentSeries (Langlands.Weil.Local.localResidueField F)`.
  The statement installs the valuative relation
  `Langlands.LocalField.Laurent.valuativeRel` of
  [`Langlands.LocalField.LaurentSeries`](../LocalField/LaurentSeries.md) by
  `letI`. Instance inference supplies Mathlib's `X`-adic topology on Laurent
  series (the topology of `LaurentSeries.instUniformSpace`) and the local-field
  instance `Langlands.LocalField.Laurent.localField`, which uses the finiteness
  instance `Langlands.Weil.Local.localResidueField_finite`. The separable closure
  is Mathlib's `SeparableClosure X` with its algebra and `IsSepClosure`
  instances.
- **The residue field and the ramification index.**
  `Langlands.Weil.Local.localResidueField F` is the residue field
  `F.residueField F.canonicalTopologicalData` of the canonical topological data
  of `F`. `F.canonicalTopologicalData.ramificationIndex` is
  `Langlands.PadicField.TopologicalData.ramificationIndex`, the natural number
  `(T.ord (p : F.Carrier)).toNat`, the normalized order of \(p\), that is
  \(e_K=v_K(p)\). The fields `X` and `SeparableClosure X` are the same as in the
  group form of the close-fields comparison,
  `Langlands.Ramification.Local.CloseFieldsGaloisQuotientStatement` and
  `Langlands.Ramification.Local.CloseFieldsWeilQuotientStatement`
  ([CloseFieldsStatement](../LocalFactor/Ramification/CloseFieldsStatement.md)),
  which the Library proves as `Langlands.Ramification.Local.closeFieldsGaloisQuotient`
  and `Langlands.Ramification.Local.closeFieldsWeilQuotient`.
- **Universes.** `uK` is the universe of the p-adic field; `X` and
  `SeparableClosure X` live in `uK` as well, so the general count is taken at
  the levels `uK, uK, uW`. `uW` is the universe of the carriers of the Weil
  representations, the same on both sides.

## Provenance

The statement is the count consequence of Deligne's theory of close local fields.

- **Route note.** The operator route note *The numerical local Langlands
  correspondence for GL_n* (`operator-numerical-llc-route-2026-11-16`,
  `numerical-LLC-route.tex`) states as Theorem `thm:Deligne` (lines 861–872),
  for a p-adic field \(K\) with \(e=e_K\) and a local field \(K'\) of
  characteristic \(p\) with the same residue field, a filtered isomorphism
  \(\mathcal W_K/\mathcal R_K(e)\cong\mathcal W_{K'}/\mathcal R_{K'}(e)\)
  compatible with the unramified characters, and in its last display (line 870)
  \[
  |\mathbf W_K(n,s,f)|=|\mathbf W_{K'}(n,s,f)|\qquad\text{whenever } s<n\,e_K .
  \]
  The statement above is the case \(f=1\) and \(K'=X\), since
  \(T_K(n,s)=|\mathbf W_K(n,s,1)|\) (§2.2, lines 182–201, which also define the
  Swan exponent, the torsion number and the strata \(\mathbf W_K(n,s,f)\)). The
  paragraph after the theorem gives the reason: a representation of
  \(\mathcal W_K\) is trivial on \(\mathcal R_K(e)\) if and only if its slope
  is \(<e\). The proof of Proposition `prop:LD` (lines 820–830) uses the count
  as "\(T_E(d',s)=T_{E'}(d',s)\) whenever \(s<d'e_E\)", with
  \(E'=\mathbb F_{q_E}((t))\), at \(d'=d\) and at \(d'=d+s\).
- **Henniart.** Guy Henniart, *La conjecture de Langlands locale numérique pour
  GL(n)*, Ann. Sci. ÉNS (4) 21 (1988), 497–544 (`henniart-1988-numerical`),
  §5.1, printed p. 512: an isomorphism \(K^\times/U_K^e\cong K'^\times/U_{K'}^e\)
  preserving the ramification is chosen; by Deligne's work it determines, up to
  inner automorphisms, an isomorphism \(G_K/G_K^e\cong G_{K'}/G_{K'}^e\) that
  carries \(G_K^\lambda/G_K^e\) to \(G_{K'}^\lambda/G_{K'}^e\) for every real
  \(\lambda\le e\). For \(n\ge 1\) and \(0\le j<n\,e\), this isomorphism of
  Galois quotients induces a bijection between \(\mathscr G^{00}_K(n,j)\) and
  \(\mathscr G^{00}_{K'}(n,j)\) compatible with the action of the unramified
  characters. Here \(\mathscr G^{00}_K(n,j)\) is the set of classes of
  dimension \(n\) and Swan conductor \(j\) whose restriction to inertia is
  irreducible (§1.3, printed p. 498); by Proposition 2.2(c) (printed p. 504)
  these are the classes fixed by no nontrivial unramified twist, that is, of
  torsion number \(1\).
- **Deligne.** Pierre Deligne, *Les corps locaux de caractéristique p, limites
  de corps locaux de caractéristique 0*, in Bernstein, Deligne, Kazhdan and
  Vignéras, *Représentations des groupes réductifs sur un corps local*, Hermann,
  1984 (`bdkv-1984-representations-local-field`). To a local field \(E\) and an
  integer \(e\ge 1\) Deligne attaches the truncated triple
  \(\mathrm{Tr}_e(E)=(\mathcal O_E/\mathfrak p_E^e,\ \mathfrak p_E/\mathfrak p_E^{e+1},\ \varepsilon_E)\),
  where \(\varepsilon_E\) is induced by the inclusion
  \(\mathfrak p_E\subset\mathcal O_E\) (Introduction, printed p. 124). Section
  3.4 (printed p. 142) starts from an isomorphism
  \(u\colon\mathrm{Tr}_e(F')\to\mathrm{Tr}_e(F'')\), from which Deligne obtains an
  equivalence \(U\) between the categories \((\mathrm{ext}\,F')^e\) and
  \((\mathrm{ext}\,F'')^e\) of finite separable extensions with ramification
  bounded by \(e\). By §3.5 (printed p. 144), \(U\) induces an isomorphism
  \(\mathrm{Gal}(\overline{F'}/F')/\mathrm{Gal}(\overline{F'}/F')^e\cong
  \mathrm{Gal}(\overline{F''}/F'')/\mathrm{Gal}(\overline{F''}/F'')^e\), unique
  up to inner automorphism. The uniqueness is relative to the chosen \(u\): in
  general the triple is not determined up to unique isomorphism by
  \(\mathcal O_E/\mathfrak p_E^e\), since it can have nontrivial automorphisms
  that are trivial on \(\mathcal O_E/\mathfrak p_E^e\) (Introduction, printed
  p. 124). Whether it has any depends on \(E\) and \(e\): for \(E=\mathbb Q_2\)
  and \(e=1\), the ring is \(\mathbb F_2\), the module is free of rank one over
  it and \(\varepsilon_E=0\), so the only such automorphism is the identity. The
  isomorphism class of the triple is determined by the truncated ring
  \(\mathcal O_E/\mathfrak p_E^e\) (Introduction, printed p. 124); more
  precisely, every isomorphism of truncated rings lifts to an isomorphism of
  triples (§1.1, printed p. 126). An isomorphism of truncated rings therefore suffices for the
  existence of the comparison, which is all that the equality of counts uses.

As an equality of the twist counts \(T\), with this range \(s<d\,e_K\), the
statement is the route note's formulation (the last display of Theorem
`thm:Deligne` at torsion number \(1\)), not a numbered result of a source:
Henniart proves the twist-compatible bijection inside §5.1, and Deligne's §§3.4
and 3.5 give the comparison of Galois quotients from which it follows. Henniart and the
route note allow any local field \(K'\) of characteristic \(p\) with the residue
field of \(K\); the statement takes \(K'=X\).
