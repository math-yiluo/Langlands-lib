# Reduction of the regular σ-descent to two global statements and a local criterion

`Langlands.BaseChange.SigmaDiscreteRegularDescentReductionStatement.{u, v, uV, uW}`
is the implication

```
SigmaDiscreteTwistedGlobalizationStatement.{0, 0, uW, 0} →
  CyclicStableCuspidalDescentTraceIdentityStatement.{0, 0, 0, 0} →
    RegularSigmaLiftSquareIntegrableStatement.{0, 0, 0, uW} →
      SigmaDiscreteRegularDescentStatement.{u, v, uV, uW}
```

between four propositions of the Library. The first two are in the namespace
`Langlands.TraceFormula`, the last two in `Langlands.BaseChange`; each is used
as it stands, at the universe levels shown. The implication says that the
descent of σ-discrete series of \(\mathrm{GL}_n\) on regular test functions
follows from two global statements, the twisted globalization of a σ-discrete
series and the weak descent with a trace identity of a σ-stable cusp, and from
a local criterion, the square-integrability of a generic unitarizable regular
σ-descent. This file states the implication and does not prove it.

## The four propositions

The summaries below fix notation; the files of the four propositions are
authoritative for their exact hypotheses. In the two global statements the
Lean files call the number fields `F` and `E`; here they are \(K\) and \(L\),
to keep \(F\) and \(E\) for the local fields of the conclusion.

- **The conclusion**, `SigmaDiscreteRegularDescentStatement.{u, v, uV, uW}`
  (`Langlands.BaseChange.SigmaDiscreteRegularDescentStatement`). Let \(F\)
  (in `Type u`) be a nonarchimedean local field of characteristic zero, and
  \(E\) (in `Type v`) a field with an \(F\)-algebra structure and the module
  topology, cyclic of degree \(l\) over \(F\) with generator \(\sigma\)
  (`IsCyclicAlgebra σ l`). Let \(\rho\) be an admissible σ-discrete series of
  \(\mathrm{GL}_n(E)\) on a complex vector space in `Type uW`, and \(A\) a
  σ-intertwiner of \(\rho\). Then there are an irreducible admissible
  square-integrable representation \(\pi\) of \(\mathrm{GL}_n(F)\) on a space
  in `Type uV` and a constant \(c\) with `IsRegularSigmaLift σ l π hπ ρ hρ A c`:
  \(c \neq 0\) and, for all Haar measures, the twisted trace of \(\rho\)
  against \(A\) equals \(c\) times the trace of \(\pi\) on concordant pairs
  of test functions supported in the σ-regular and regular semisimple sets,
  the second with determinants in the norm group.
- **Twisted globalization**,
  `SigmaDiscreteTwistedGlobalizationStatement.{uF, uE, uR, uW}`
  (`Langlands.TraceFormula.SigmaDiscreteTwistedGlobalizationStatement`). Let
  \(L/K\) be a cyclic extension of number fields (in `Type uF` and
  `Type uE`) of degree \(l\) with generator \(\sigma\), with compact adele
  quotients, split at every infinite place; let \(v\) be a finite place of
  \(K\) with exactly one place \(w\) of \(L\) above it, and \(v_1, v_2,
  v_3\) pairwise distinct split finite places different from \(v\). Then every
  σ-discrete series of \(\mathrm{GL}_{r+1}(K_v \otimes_K L)\) on a space in
  `Type uR` is isomorphic, through the \(w\)-component
  \(K_v \otimes_K L \to L_w\), to the local component at \(w\) of a spectral
  presentation (local spaces in `Type uW`) of a cuspidal operator realization
  of \(\mathrm{GL}_{r+1}\) over \(L\) with unitary central character and
  σ-stable class, whose components above \(v_1\) and \(v_2\) are
  supercuspidal and whose component at \(w\) is irreducible and admissible.
- **Descent with a trace identity**,
  `CyclicStableCuspidalDescentTraceIdentityStatement.{uF, uE, uV, uW}`
  (`Langlands.TraceFormula.CyclicStableCuspidalDescentTraceIdentityStatement`).
  In the same global setting, with two distinct split finite places \(v_1,
  v_2\), let \(T\) be a cuspidal operator realization of
  \(\mathrm{GL}_{r+1}\) over \(L\) with unitary central character and
  σ-stable class, and \(P\) a spectral presentation of \(T\) (spaces in
  `Type uW`) with supercuspidal components above \(v_1\) and \(v_2\) and an
  irreducible admissible component \(\Pi_w\) at \(w\). Then the class of
  \(T\) is a weak base change of the class of a cuspidal operator realization
  \(S\) of \(\mathrm{GL}_{r+1}\) over \(K\) with unitary central character,
  with a spectral presentation \(D\) (spaces in `Type uV`) whose component
  \(\pi_v\) at \(v\) is irreducible and admissible, and \(\pi_v\) and
  \(\Pi_w\) (on \(\mathrm{GL}_{r+1}(K_v \otimes_K L)\)) satisfy the regular
  trace identity for some σ-intertwiner of \(\Pi_w\) and some constant
  \(c \neq 0\).
- **Square-integrability** (the local criterion),
  `RegularSigmaLiftSquareIntegrableStatement.{u, v, uV, uW}`
  (`Langlands.BaseChange.RegularSigmaLiftSquareIntegrableStatement`). With
  \(F\) (in `Type u`) and \(E\) (in `Type v`) as in the conclusion, an
  admissible representation \(\pi\) of \(\mathrm{GL}_{r+1}(F)\) on a space in
  `Type uV` that is generic for some unitary additive character, unitarizable, and
  satisfies `IsRegularSigmaLift` with a σ-discrete series of
  \(\mathrm{GL}_{r+1}(E)\) on a space in `Type uW` is square-integrable.

## Universes

The universe levels of the hypotheses are those at which the argument below
uses them. The number fields \(K\) and \(L\) that globalize \((F, E)\) lie in
`Type`: the Library's `Langlands.TraceFormula.cyclicFieldGlobalization`, the
proof of `CyclicFieldGlobalizationStatement`, produces them there. Hence the
local field \(K_v\) and the algebra \(K_v \otimes_K L\) lie in `Type`. The
spaces of the global presentations, and of the local component \(\pi_v\) to
which the square-integrability criterion is applied, are taken in `Type`. Only
the space of the σ-discrete series keeps its universe `uW`: the σ-discrete
series of \(\mathrm{GL}_n(E)\) is carried to \(\mathrm{GL}_n(K_v \otimes_K L)\)
on the same space, and this is the representation that the first and third
hypotheses receive. The conclusion holds at arbitrary universes
`u, v, uV, uW`.

## Why the implication holds

Henniart–Lemaire (2011), II.6.16–II.6.17, printed pp. 131–132, prove the
descent in positive characteristic by a global argument; in characteristic
zero they refer to Arthur–Clozel (1989), Chapter 1, §6.3, printed pp. 54–57
(Henniart–Lemaire, II.6.1, printed p. 118). The argument runs as follows. The
local field \(F\) and the extension \(E\) are realized as \(K_v\) and
\(K_v \otimes_K L\) for a cyclic extension of number fields \(L/K\) and a
finite place \(v\) of \(K\) with a single place of \(L\) above it. The
σ-discrete series is globalized as the local component of a σ-stable cusp
(the first hypothesis). That cusp is a weak base change of a cuspidal
representation of \(\mathrm{GL}_{r+1}\) over \(K\) whose component at \(v\)
satisfies the regular trace identity with it (the second hypothesis). That
component, a local component of a cuspidal representation with unitary
central character, is generic and unitarizable, so it is square-integrable
by the local criterion (the third hypothesis). Carrying the result back to
\(F\) and \(E\) along the isomorphisms \(K_v \cong F\) and
\(K_v \otimes_K L \cong E\) gives the conclusion for \(n \geq 1\); for
\(n = 0\) the group \(\mathrm{GL}_0\) is trivial and the conclusion needs none
of the hypotheses.

The conditions at the auxiliary places are those of the two global statements
of the Library, not those of the sources. In Arthur–Clozel, §6.3, printed
p. 57, the σ-stable cusp \(\Pi\) has a supercuspidal component
\(\Pi_{v_1} = (\pi_{v_1})^{\otimes l}\) at a split place \(v_1\), a
component \(\Pi_{v_2} = (\pi_{v_2})^{\otimes l}\) at a split place \(v_2\)
(because \(\Pi_{v_2}\) is σ-stable), and a Steinberg component at an inert
place \(v_3\). The place \(v_2\) is where the test functions satisfy the
support condition (4′) of Lemma 2.5, printed p. 14: the product of the
supports of the factors has regular elliptic image in
\(\mathrm{PGL}_n(K_{v_2})\). Henniart–Lemaire, II.6.16, use instead functions
built from level-zero data at the split place \(v_1\) of II.6.7 and restrict
supports at a further place \(v_2\). The statements
`SigmaDiscreteTwistedGlobalizationStatement` and
`CyclicStableCuspidalDescentTraceIdentityStatement` both ask for supercuspidal
components above two split places \(v_1\) and \(v_2\) (the first also names a
third split place \(v_3\)), and neither asks for a Steinberg component. This is
the formulation of those two statements, which the implication uses as they
stand.

## Sources

- Henniart and Lemaire, *Changement de base et induction automorphe pour GLₙ
  en caractéristique non nulle*, Mém. SMF 124 (2011), II.6.1 (p. 118) and
  II.6.16–II.6.17 (pp. 131–132). Pages are printed, with PDF offset +8.
  Source ID
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`.
- Arthur and Clozel, *Simple Algebras, Base Change, and the Advanced Theory of
  the Trace Formula* (1989), Chapter 1, Lemmas 2.4–2.5 (pp. 13–15) and §6.3
  (pp. 54–57). Pages are printed, with PDF offset +14. Source ID `arthur-clozel-1989-base-change`.
