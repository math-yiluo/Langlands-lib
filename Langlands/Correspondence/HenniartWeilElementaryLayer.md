# The truncated Weil-side elementary layer of the numerical LLC route

This module states the elementary layer on the Weil side of the operator route
note `operator-numerical-llc-route-2026-11-16`. The layer is unit 3 of the
note's §7.1, in the truncated form that the base case of Option II needs (the
operator's amendment of 17 November 2026 calls it "the truncated elementary
layer"). The module contains two definitions and six Prop-valued statements in
namespace `Langlands.Henniart`. It proves nothing; separate proof tasks prove
the six statements under their fixed names.

## Notation

Fix a prime \(p\) and a p-adic field \(K\) : `PadicField.{uK} p`. The rank is
\(n=k+1\), with Lean index `k`.

- \(q_K\) is `K.canonicalTopologicalData.residueCardinality`, the cardinality
  of the residue field.
- \(e_K\) is `K.canonicalTopologicalData.ramificationIndex`, the absolute
  ramification index \(v_K(p)\).
- \(W_K(n,s,f)\) is `Numerical.weilRefinedStratum K k s f`. It is the set of
  unramified-twist orbits of irreducible Weil classes of rank \(n\), Swan
  exponent \(s\) and torsion number \(f\). The torsion number is the number of
  unramified characters \(\chi\) with \(\chi\sigma\cong\sigma\).
- \(T_K(n,s)\) is `Numerical.weilTwistIrreducibleCount K k s`, the count of
  \(W_K(n,s,1)\) in `ℕ∞`. These are the orbits of classes whose restriction to
  inertia is irreducible (route note, Proposition `prop:unram`(i)).
- \(C_K(n,j)\) is `Numerical.weilConductorCount K k j`. This is Henniart's
  \(C_K(n,j)=\sum_{d\mid n}\sum_{0\le s,\ ns\le dj}T_K(d,s)\), the number of
  orbits of classes of dimension dividing \(n\) and slope at most \(j/n\) whose
  restriction to inertia is irreducible.

These counts come from [Refined orbit strata](HenniartRefinedStrata.md).
\(\nu(n,f,s;q)\) and \(\tau(n,s;q)=\nu(n,1,s;q)\) are
`Numerical.polarPartCount q n f s` and `Numerical.polarTwistCount q n s`, from
[Polar parts](HenniartPolarPart.md). By the convention there, \(\nu=0\) unless
\(f\ge1\), \(f\mid n\) and \(f\mid s\). (LD) is `LaumonDeligneCountStatement`, from
[The Laumon–Deligne count](HenniartLaumonDeligneStatement.md). Every count is
an extended natural number (`ℕ∞`). The universes `uK` of fields and `uW` of
Weil representations are independent.

An extension \(L/K\) is given as in the Library: a field
`L : PadicField.{uK} p` and a `Padic p`-algebra embedding
`ι : K.Carrier →ₐ[Padic p] L.Carrier`. The degree \([L:K]\) is
`Weil.Local.extensionDegree K L ι`, and the residue degree \(f(L/K)\) is
`Weil.Local.extensionResidueDegree K L ι`.

## Definitions

1. `Numerical.IsUnramifiedOfDegree K L ι i`: \(L/K\) is unramified of degree
   \(i\). That is, \([L:K]=i\) and \(f(L/K)=i\), so the relative ramification
   index is \(1\).
2. `Numerical.IsTameTotallyRamifiedOfDegree K L ι m`: \(L/K\) is tamely and
   totally ramified of degree \(m\). That is, \([L:K]=m\), \(f(L/K)=1\) and
   \(p\nmid m\). For a totally ramified extension, tame ramification means
   \(p\nmid e(L/K)=[L:K]\).

Both predicates hold for every embedding with the stated degrees. The
statements quantify over all such \((L,\iota)\), so the choice of a model of the
extension does not matter. Neither definition is taken from a numbered source
result; both are the standard notions that the route note and the sources use.
Since \(e(L/K)f(L/K)=[L:K]\)
(`PadicField.ramificationIndex_mul_extensionResidueDegree`), a tamely and
totally ramified \(L/K\) of degree \(m\) has \(e_L=m\,e_K\).

## The six statements

### 1. Unramified descent: `WeilUnramifiedDescentCountStatement.{uK, uW}`

This is the conjunction of two parts, each quantified over all \(p\), \(K\) and
all naturals \(k,s,f\).

- (a) If \(W_K(n,s,f)\) is nonempty, then \(f\ge1\), \(f\mid n\) and \(f\mid s\).
  In Lean the torsion number is a `Nat.card`, so \(f\ge1\) also asserts that
  the stabilizer is finite.
- (b) Let \(f\ge1\), \(f\mid n\) and \(f\mid s\). Suppose that for every
  \(i\mid f\) and every unramified extension \(L/K\) of degree \(i\),
  \(T_L(n/f,s/f)=\tau(n/f,s/f;q_L)\). Then
  \(|W_K(n,s,f)|=\nu(n,f,s;q_K)\) in `ℕ∞`.

In Lean the rank \(n/f\) has index `(k + 1) / f - 1`. Since \(f\mid n\) and
\(f\ge1\), \(n/f\ge1\), so the index represents \(n/f\) exactly.

Provenance. This is route note Proposition `prop:unram` (lines 664–683 of
`numerical-LLC-route.tex`) in the form of Proposition `prop:tworeductions`(a)
(lines 276–283). Part (a) collects `prop:unram`(i), (ii). An unramified
\(\chi\) with \(\chi\sigma\cong\sigma\) satisfies \(\chi^n=1\), and one of exact
order \(d\) fixes \(\sigma\) exactly when \(\sigma\) is induced from \(K_d\).
So a class with torsion number \(f\) is \(\operatorname{Ind}_{K_f}^K\tau\) with
\(\mathrm{sw}(\sigma)=f\,\mathrm{sw}(\tau)\). Henniart (1988), Proposition 2.2
(a)–(c) is the source of (i):
[p. 504](https://www.numdam.org/article/ASENS_1988_4_21_4_497_0.pdf#page=9).
Part (b) follows from the Möbius formula of `prop:unram`(iii),
\(|W_K(n,s,f)|=\frac1f\sum_{i\mid f}\mu(f/i)\,T_{K_i}(n/f,s/f)\), together with
the same relation
\(\nu(n,f,s;q)=\frac1f\sum_{i\mid f}\mu(f/i)\,\tau(n/f,s/f;q^{i})\) between
\(\nu\) and \(\tau\). That relation follows from the closed formula of Lemma
`lem:nu` (line 234), since \(q_{K_i}=q_K^{\,i}\). The Möbius formula is Koch
(1984), §7, Satz 3 and its proof, printed pp. 111–112
(`koch-1984-numerical-langlands-remarks`). The hypothesis of (b) asks only for
the values the formula uses, at \((n/f,s/f)\) and over unramified extensions
of degree dividing \(f\). Statement 6 needs exactly this form.

### 2. Rank one: `WeilRankOneCountStatement.{uK, uW}`

\(T_K(1,0)=q_K-1\), and \(T_K(1,s)=(q_K-1)^2q_K^{\,s-1}\) for every \(s\ge1\).

The Swan exponent of a rank-one class is its conductor minus one, truncated at
zero. So \(T_K(1,0)\) counts the unramified orbit together with the \(q_K-2\)
orbits of ramified tame characters.

Provenance. Route note Proposition `prop:rank1` (lines 684–686); this is local
class field theory. Henniart (1988), §3.1 treats the same case as
\(C_K(1,j)=(q_K-1)q_K^{\,j}\):
[p. 507](https://www.numdam.org/article/ASENS_1988_4_21_4_497_0.pdf#page=12).

### 3. Tame reduction, truncated: `WeilTameReductionStatement.{uK, uW}`

Let \(n=p^rm\) with \(p\nmid m\). Suppose the following holds for every
\(r'\le r\), every tamely and totally ramified extension \(L/K\) of degree
dividing \(m\), and every \(j<p^{r'}e_L\):
\(C_L(p^{r'},j)=(q_L-1)q_L^{\,j}\). Then \(C_K(n,j)=(q_K-1)q_K^{\,j}\) for
every \(j<n\,e_K\).

In Lean, "of degree dividing \(m\)" is `d ∣ m` together with
`IsTameTotallyRamifiedOfDegree K L ι d`. The ranks have indices `p ^ r' - 1`
and `p ^ r * m - 1`. These are exact: \(p^{r'}\ge1\), and \(m\ge1\) because
\(p\nmid m\) excludes \(m=0\).

Provenance. Route note Proposition `prop:tame` (lines 688–692): Koch (1984),
§8, Satz 4, printed pp. 112–113, and Henniart (1988), §1.4 and §3.1,
[p. 499](https://www.numdam.org/article/ASENS_1988_4_21_4_497_0.pdf#page=4)
and [p. 507](https://www.numdam.org/article/ASENS_1988_4_21_4_497_0.pdf#page=12). Those
results are stated for all \(j\). The truncated form, with \(j<p^{r'}e_L\) and
\(j<n\,e_K\), is the route note's: it is part (c) of the proof of Proposition
`prop:LDcount` (lines 840–845).

Check against Koch (1984), §8. The note's remark after `prop:LDcount` (lines
849–850) says the truncation was checked only against the structure of the
argument. The task asked for a check against Koch, §8, which was done for this
candidate. Koch proves Satz 4 by comparing, at one fixed \(j\), the count
\(B_{j,n}\) over \(K\) (where \(B_{j,n}=n\,C_K(n,j)\), Henniart 1988, §2.4) with
the counts \(B_{j,p^r}\) over the tamely and totally ramified extensions \(L\)
of degree \(m\), using the same \(j\) (Lemmas 5–8 and equations (25)–(28)).
Koch's counts bound the normalized Swan conductor
\((n/\dim\rho)\,\mathrm{sw}(\rho)\). Induction from such an \(L\) preserves
the Swan conductor and multiplies the dimension by \(m\), so this quantity is
the same on both sides. The argument uses its hypothesis only at the same
\(j\), at \(r'=r\) and for degree exactly \(m\). Since \(e_L=m\,e_K\),
\(j<p^rm\,e_K\) holds exactly when \(j<p^re_L\). So the argument proves the
truncated form. The statement assumes the hypothesis for all \(r'\le r\) and
all degrees dividing \(m\), as the task specifies. This is more than the
argument uses, and the induction in the proof of statement 5 supplies all of
it.

### 4. Henniart's Corollaire 1.4: `WeilConductorCountStepStatement.{uK, uW}`

For \(n=p^r\) and every integer \(\lambda\ge1\),
\(C_K(p^r,p^r\lambda)=q_K\cdot C_K(p^r,p^r\lambda-1)\) in `ℕ∞`.

In Lean \(\lambda\) is the variable `l`, since `λ` is a Lean keyword. The
statement holds for every \(r\ge0\). For \(r=0\) it follows from rank one,
since \(C_K(1,j)=(q_K-1)q_K^{\,j}\).

Provenance. Route note Corollary `cor:14` (lines 717–723) and Henniart (1988),
Corollaire 1.4,
[p. 499](https://www.numdam.org/article/ASENS_1988_4_21_4_497_0.pdf#page=4),
derived again in §3.4,
[p. 509](https://www.numdam.org/article/ASENS_1988_4_21_4_497_0.pdf#page=14).
Henniart states it for \(n=p^r>1\) and \(j=p^rk\), printed as "\(k\geqq0\)".
For \(k=0\), however, \(C_K(n,j-1)\) is undefined, and Henniart's argument
needs a non-zero Swan conductor. So the condition must be \(k\ge1\), and the
route note writes \(\lambda\in\mathbb Z_{\ge1}\). The statement follows the
route note.

The proof of this statement uses Henniart's Proposition 3.3(ii) (route note
Proposition `prop:H33`(ii), lines 694–715; Henniart 1988, Proposition 3.3,
[pp. 508–509](https://www.numdam.org/article/ASENS_1988_4_21_4_497_0.pdf#page=13)).
That proposition is not stated separately in this module. It says: for
\(\sigma\) of dimension \(p^r\) with \(\sigma|_{P_K}\) irreducible and integral
slope \(\lambda>0\), there is a unique character \(\eta_0\ne1\) of
\(U_K^{\lambda}/U_K^{\lambda+1}\) such that \(\mathrm{sw}(\chi\sigma)<\mathrm{sw}(\sigma)\)
exactly when \(\chi^{-1}|_{U_K^\lambda}=\eta_0\). The proof of `cor:14` combines it
with a count of orbits of the group of characters of
\(U_K^\lambda/U_K^{\lambda+1}\), which has order \(q_K\).

### 5. Truncated Théorème 1.3: `WeilTruncatedConductorCountStatement.{uK, uW}`

Assume (LD). Then for every prime \(p\), every p-adic field \(K\), every rank
\(n=k+1\), and every \(j<n\,e_K\), \(C_K(n,j)=(q_K-1)q_K^{\,j}\).

Provenance. Henniart (1988), Théorème 1.3,
[p. 498](https://www.numdam.org/article/ASENS_1988_4_21_4_497_0.pdf#page=3),
asserts this for all \(j\). The truncated form, restricted to \(j<n\,e_K\) and
assuming (LD), is the route note's: steps (b) and (c) of the proof of
Proposition `prop:LDcount` (lines 836–845). It is not a numbered result of a
source.

The route note proves it as in Proposition `prop:H43` (Henniart 1988,
Proposition 4.3 and §4.4,
[p. 511](https://www.numdam.org/article/ASENS_1988_4_21_4_497_0.pdf#page=16)).
The proof uses statements 2, 3 and 4 and the difference identity
\(C(n,j)-C(n,j-1)=\sum_{m\mid\gcd(n,j)}T(n/m,j/m)\), with (LD) applied in the
range \(j<n\,e\). It also uses the value \(C_K(n,0)=q_K-1\) to start the
induction on \(j\) (Henniart 1988, §3.2,
[p. 508](https://www.numdam.org/article/ASENS_1988_4_21_4_497_0.pdf#page=13)).
That value is not stated separately here.

### 6. The close-range count from (LD): `LaumonDeligneWeilCountStatement.{uK, uW}`

Assume (LD). Then for every prime \(p\), every p-adic field \(K\), and all
\(k,s,f\) with \(s<(k+1)\,e_K\), \(|W_K(k+1,s,f)|=\nu(k+1,f,s;q_K)\) in `ℕ∞`.

The route note assumes \(f\mid\gcd(n,s)\); the statement does not. Strata
outside that range are covered by statement 1(a) and by the convention
\(\nu=0\) there, so both sides are \(0\).

Provenance. Route note Proposition `prop:LDcount` and its proof (lines
832–857). This is the route note's own proposition, proved in the note from
(LD), and not a numbered result of a source. Its proof combines statement 1,
the truncated uniqueness of the polar-part task
(`PolarPartTruncatedUniquenessStatement`) and statement 5. Every field met in
the proof is an unramified extension of \(K\), which has the same \(e\).

## Route-note line ranges

All line numbers refer to `numerical-LLC-route.tex` in the route note's folder
(source `operator-numerical-llc-route-2026-11-16`). The elementary layer is §5.1,
lines 662–743; Proposition `prop:LDcount` and its proof, with the closing
remark, are lines 832–857.

## Deferred units

The route note's truncation lemma `lem:trunc`, Theorem `thm:reduction` (the
wild core statement \(\mathrm W(r,j)\)) and Corollary `cor:kummer` are not
stated here; the Option II assembly does not use them. They are reported to the
operator as deferred.
