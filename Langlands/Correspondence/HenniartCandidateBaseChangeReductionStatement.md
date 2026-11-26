# Henniart's route with the candidate compatible with cyclic base change

This module states one proposition in `Langlands.Henniart` and proves nothing.
It is the final form of the route to the supercuspidal local Langlands
correspondence for `GL_n` along Option II of the operator's route note *The
numerical local Langlands correspondence for GL_n: counts on the two sides and
the recommended route of proof* (`operator-numerical-llc-route-2026-11-16`,
`numerical-LLC-route.tex`), §7.1 `sec:units`, last paragraph (lines 1317–1320),
when input (I4) is obtained from Henniart's candidate (source (b) of §6.5).

The universes of p-adic fields (`uK`), of Weil representation carriers (`uW`)
and of supercuspidal representation carriers (`uV`) are independent.

## Statement

`SupercuspidalCorrespondenceHenniartCandidateBaseChangeStatement.{uK, uW, uV}`
is the implication with these six premises, in this order, and the conclusion
`Correspondence.SupercuspidalCorrespondenceStatement.{uK, uW, uV}` (for every
prime `p` and every p-adic field `F` there is exactly one supercuspidal
correspondence over `F`, module `Langlands.Correspondence.SupercuspidalSpecification`):

1. `CandidateExistenceStatement.{uK, uW, uV, uW, uK}`: Henniart's candidates
   exist at every finite quotient (Henniart 2000, Théorème 3.1 with §§3.7–3.8;
   module `Langlands.Correspondence.HenniartStableMapStatement`);
2. `CandidateBaseChangeCompatibilityStatement.{uK, uW, uV}`: the candidate is
   compatible with cyclic base change of prime degree, (CI1) and (CI2), with one
   weak cyclic base change per step (module
   `Langlands.Correspondence.HenniartCandidateBaseChangeCompatibility`);
3. `SupercuspidalStratumUpperBoundStatement.{uK, uV}`, input (I1): the GL-side
   refined counts are bounded by the polar-part counts;
4. `LaumonDeligneCountStatement.{uK, uW}`, input (I2) in the Laumon–Deligne
   form (LD): for \(1\le s<d\,e_K\), the counts of Weil orbits with torsion
   number one and Swan exponent \(s\) in ranks \(d\) and \(d+s\) agree;
5. `SupercuspidalTwistSwanBoundStatement.{uK, uV}`: the Swan exponent of a
   twist \(\chi\pi\) of a supercuspidal class of rank \(n\) is at most
   \(\max(\operatorname{sw}\pi,n\operatorname{sw}\chi)\), with equality when
   the two terms differ (route note, Lemma `lem:level`(ii));
6. `WeilArtinConductorExistenceStatement.{uK, uW}`: every irreducible Weil
   class has a natural Artin conductor.

Premises 3–6 are exactly the premises of the Library's
`NumericalDescentStatement` (module
`Langlands.Correspondence.HenniartNumericalDescentStatement`) other than input
(I4), `CompatibleNumericalInjectionsStatement`. Premises 1 and 2 take the
place of (I4).

## How the statement relates to the Library

The proposition is obtained by composing three implications, which the Library
states separately:

- `CandidateCompatibleNumericalInjectionsReductionStatement` (module
  `Langlands.Correspondence.HenniartCandidateBaseChangeCompatibility`):
  premises 1 and 2 give (I4);
- `NumericalDescentStatement`: premises 3–6 and (I4) give, among other
  things, `NumericalSurjectivityStatement`, the surjectivity half of Henniart's
  numerical theorem (Henniart 1988, Théorème 1.2);
- `Extension.SupercuspidalCorrespondenceHenniartSupercuspidalConductorStatement`
  (module `Langlands.Correspondence.HenniartSupercuspidalConductorReductionStatement`),
  proved by `Extension.supercuspidalCorrespondenceHenniartSupercuspidalConductor`:
  candidate existence, numerical surjectivity and the conductor theorem for
  supercuspidal representations of p-adic fields give the supercuspidal
  correspondence. The conductor theorem is proved in the Library
  (`Conductor.supercuspidalPadicConductorExponent`), so it is not a premise
  here.

This explanation is informal; the module contains no proof.

`NumericalSurjectivityStatement` itself does not mention the candidate. With
source (b) for (I4), however, its proof passes through the candidate, which
provides the compatible injections. The route note therefore recommends, as
the natural final form, a theorem whose premise on the candidate carries the
compatibility with cyclic base change: "candidate existence *with its
compatibility with cyclic base change*, (I1), (I2), (I3) and the conductor
theorem imply the supercuspidal correspondence". In the Lean statement, (I2)
is premise 4, (I3) is contained in premise 2 (the weak cyclic base
change of each step), and the conductor theorem is proved. Premises 5 and 6
are the two further local inputs of the descent. The proposition does not
replace the Library's statements with the unconditional premise
`NumericalSurjectivityStatement`.

## Provenance

- Route note (`operator-numerical-llc-route-2026-11-16`), §7.1 `sec:units`,
  last paragraph (lines 1317–1320): the natural form of the final theorem
  under Option II with source (b) for (I4). §6.5 `sec:ci` (lines 1150–1174):
  hypothesis (CI) and its source (b). §6.6, Theorem `thm:descent`: the descent,
  stated in the Library as `NumericalDescentStatement`.
- Guy Henniart, *Une preuve simple des conjectures de Langlands pour GL(n)
  sur un corps p-adique* (2000, `henniart-2000-simple-proof`): the candidate
  and the reduction of the correspondence to candidate existence and numerical
  surjectivity (§§3.7–3.8, 4.1–4.4).
- Guy Henniart, *La conjecture de Langlands locale numérique pour GL(n)*
  (1988, `henniart-1988-numerical`), Théorème 1.2: the numerical theorem whose
  surjectivity half the descent supplies.
