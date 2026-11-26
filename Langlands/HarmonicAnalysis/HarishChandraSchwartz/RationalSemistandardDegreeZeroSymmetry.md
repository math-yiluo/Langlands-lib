# Remark VIII.2.2 for the degree-zero operator

Remark VIII.2.2 (printed p. 322) states, for \(f\in\mathcal C(G)\) and
\(\chi\in\operatorname{Im}X(G)\),
\[({}^\circ f)\check{}={}^\circ(\check f),\qquad \overline{{}^\circ f}={}^\circ\bar f,
\qquad ({}^\circ f)\chi={}^\circ(f\chi),\]
and says that these follow from the definitions and from the identities
\(\theta^G_\omega(\lambda(g^{-1})\check f)=\theta^G_{\check\omega}(\lambda(g)f)\),
\(\overline{\theta^G_\omega(\lambda(g)\check f)}=\theta^G_{\bar\omega}(\lambda(g)\check{\bar f})\),
\(\chi(g)\theta^G_\omega(\lambda(g)\check f)=\theta^G_{\omega\otimes\chi}(\lambda(g)(f\chi)\check{})\)
and \(\mu(\omega\otimes\chi)=\mu(\omega)\), for a semistandard \(P=MU\), \(\omega\in E_2(M)\) and
\(g\in G\).
[Waldspurger, *La formule de Plancherel pour les groupes p-adiques* (2003),
p. 322](https://doi.org/10.1017/S1474748003000082)

The operator is `rationalSemistandardDegreeZero` of the module
`RationalSemistandardDegreeZero`, \({}^\circ f=f-\kappa(\psi)\), with all of its
parameters and inputs. The three operations are the existing ones on the actual
rational Schwartz space: `Space.check` (\(\check f(x)=f(x^{-1})\)), the pointwise
complex conjugation `Space.complexConj`, which is conjugate linear and is used only
as a function on the space, and `rationalSchwartzUnitaryTwist`, multiplication by a
unitary unramified character \(\chi\) of `G` (an element of
`rationalUnitaryUnramifiedCharacters G`, trivial on \(G^1\) and of absolute value one).

## Declarations

| Declaration | Content |
| --- | --- |
| `rationalSemistandardDegreeZero_properSmooth`, `rationalSemistandardDegreeZero_properFiniteSupport` | The smoothness and proper finite-support witnesses used by the lift, from the full smoothness target and from strictly lower-rank finiteness. |
| `rationalSemistandardDegreeZero_apply_eq_sub_properFourierSynthesis` | \({}^\circ f(g)=f(g)-\) `GlobalSynthesis.properFourierSynthesis … f g`, for every choice of these witnesses. |
| `RationalSemistandardDegreeZeroSymmetryStatement` | The three identities, as equalities of Schwartz functions, under the character and orbit comparisons. |
| `rationalSemistandardDegreeZero_symmetry` | Proof of that statement. |
| `rationalSemistandardDegreeZero_checkLaw`, `_conjLaw`, `_twistLaw` | The laws `RationalDegreeZeroCheckLaw`, `RationalDegreeZeroConjLaw`, `RationalDegreeZeroTwistLaw` of `RationalCuspidalUnit` for the operator, under the same premises. |

## Statement and premises

`RationalSemistandardDegreeZeroSymmetryStatement` asserts, for every Schwartz `f`
and every \(\chi\),
`checkC (°f) = °(checkC f)`, `Space.complexConj (°f) = °(Space.complexConj f)` and
`rationalSchwartzUnitaryTwist χ (°f) = °(rationalSchwartzUnitaryTwist χ f)`, given two
named comparisons of the Library:

- `SemistandardInducedCharacterSymmetryStatement`: the three character identities
  above at every semistandard index, for the traces
  `semistandardInducedSchwartzCharacter` of the actual finite-rank normalized induced
  Schwartz actions, with \(\check\omega\), \(\bar\omega\) and \(\omega\otimes\chi\) realized
  by the smooth contragredient, the conjugate complex representation and the twist by
  the restriction of \(\chi\) to the literal Levi;
- `GlobalSynthesis.ProperOrbitSymmetryStatement`: at every proper index, orbit
  transports for the contragredient, the complex conjugate and the twist by \(\chi\)
  that preserve the source-normalized orbit measure and the formal degree and leave
  the density invariant (for the twist this is \(\mu(\omega\otimes\chi)=\mu(\omega)\)),
  together with reality of the density.

Neither premise contains a commutation property of the operator.

## Proof

The value of \({}^\circ f\) at \(g\) is \(f(g)\) minus the weighted synthesis of the lift
at \(g\). The lift's underlying smooth family is, by definition, the Library's
`rationalSemistandardFourierThetaProperSmoothFamily` at the witnesses above, and the
value of that family does not depend on the witnesses, so the subtracted term is
`GlobalSynthesis.properFourierSynthesis f g`. The Library's
`GlobalSynthesis.properFourierSynthesis_symmetry` proves, from the two premises, the three
identities for this subtracted term: its value at \(g^{-1}\) is the term of \(\check f\)
at \(g\), its conjugate is the term of \(\bar f\), and its product with \(\chi(g)\) is the
term of \(f\chi\). The identities for \(f\) itself hold by definition of the three
operations, and subtraction gives the three identities pointwise; equality of Schwartz
functions follows by extensionality.

The laws of `RationalCuspidalUnit` are stated for every pair of Schwartz functions
related pointwise by the operation; such a pair is the pair \((f,\check f)\),
\((f,\bar f)\) or \((f,f\chi)\) by extensionality, and the law is the corresponding
identity evaluated at a point.

## Scope

The field is any nonarchimedean local field with finite residue field, of any
characteristic; the group is any affine locally finite type connected reductive group
scheme, with no split or quasi-split assumption and including relative rank zero
(where the operator is the identity). The field and representation-carrier universes are
independent.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques (d'après
Harish-Chandra)*, Journal of the Institute of Mathematics of Jussieu 2 (2003), 235–333,
Remark VIII.2.2, printed p. 322 (PDF p. 88). Registered source
`waldspurger-2003-plancherel`. [DOI](https://doi.org/10.1017/S1474748003000082)
