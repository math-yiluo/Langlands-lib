# Compatibility of Henniart's candidate with cyclic base change of prime degree

This module gives two definitions and one proposition. It proves nothing. The
proposition is interface E3 of the operator's plan note *Formalizing the large
external inputs of the local Langlands correspondence for GL_n*
(`operator-external-inputs-plan-2026-11-16`, `external-inputs-plan.tex`,
line 240), stated for the Library's candidate. It is the form of input (I4)
of Option II that source (b) of §6.5 of the operator's route note *The
numerical local Langlands correspondence for GL_n: counts on the two sides and
the recommended route of proof* (`operator-numerical-llc-route-2026-11-16`,
`numerical-LLC-route.tex`, lines 1150–1174) asks for.

## Setting

Throughout, `p` is a prime with `[Fact p.Prime]` and
`S : Numerical.CyclicPrimeStep.{uK} p` is a cyclic extension \(M/L\) of prime
degree of p-adic fields (module `Langlands.Correspondence.HenniartCyclicBaseChange`),
with \(L=\) `S.base`, \(M=\) `S.top` and \(\Gamma=\operatorname{Gal}(M/L)\)
the type `S.Gal`. A positive rank is \(n=k+1\), written `k.succPNat`. The
universes of fields (`uK`), of Weil representation carriers (`uW`) and of
supercuspidal representation carriers (`uV`) are independent.

**The candidate.** Over a p-adic field `K`, the candidate in rank \(n\) is
`Extension.rankExtension K hS`, a map from the irreducible Weil classes
`IrreducibleWeilClass K n` to the supercuspidal classes
`SupercuspidalAutomorphicClass K n` (module
`Langlands.Correspondence.HenniartRankExtension`; Henniart 2000, §4.4). It is
defined from a proof `hS : StableMap.StableExistsAt K n`, Henniart's 4.2 (a)
in rank \(n\): every finite-image unitary irreducible Weil class of dimension
\(n\) has a stable image, that is, a common value of all candidates at a
finite quotient of the absolute Galois group (module
`Langlands.Correspondence.HenniartStableMapStatement`). The map sends an
unramified twist \(z\cdot b_0\) of a finite-image unitary class \(b_0\) to the
twist by \(z\) of the stable image of \(b_0\). The universe of the auxiliary
data of the candidates is taken to be `uW`, that is,
`StableExistsAt.{uK, uW, uV, uW}`, as in the Library's
`Extension.SupercuspidalConductor.rankExtension_conductor`. Since
`StableExistsAt K n` is a proposition, `rankExtension K hS` does not depend on
the proof `hS`. "The candidate is defined in rank \(n\) over `K`" means that
`StableExistsAt K n` holds.

## Definitions in `Langlands.Henniart.Numerical`

### (CI1) for the candidate

`IsCandidateBaseChangeCompatible.{uK, uW, uV} S Ch`, for
`Ch : Numerical.CyclicBaseChangeMap.{uK, uV} S`, is the following proposition.
For every \(k\), every `hL : StableExistsAt S.base k.succPNat`, every
irreducible Weil class \(\sigma\) of rank \(k+1\) over \(L\), every multiset
\(m\) of irreducible Weil classes over \(M\) of arbitrary positive ranks with
`Numerical.IsRestrictionDecomposition S σ m`, and every
`hm : ∀ τ ∈ m, StableExistsAt S.top τ.1.succPNat`,

```text
Ch k (Extension.rankExtension S.base hL σ) =
  m.pmap (fun τ h => ⟨τ.1, Extension.rankExtension S.top h τ.2⟩) hm.
```

So: \(m\) lists the irreducible constituents of the restriction of \(\sigma\)
to \(W_M\), with multiplicities (`IsRestrictionDecomposition`, module
`Langlands.Correspondence.HenniartCompatibleInjections`). If the candidate is
defined over \(L\) in rank \(k+1\) and over \(M\) in the rank of every member
of \(m\), then `Ch` sends the candidate image of \(\sigma\) to the multiset of
the candidate images of the members of \(m\), each in its own rank and with
its multiplicity. `Multiset.pmap` applies the candidate over \(M\) to each
member with the proof given by `hm`; by proof irrelevance the result does not
depend on `hm`. As for `IsBaseChangeCompatible`, the multiset stands for the
cuspidal support of the base change. This is (CI1) of the route note,
\(\mathrm{Ch}_{M/L}(\varphi_L(\sigma))=\varphi_M(\operatorname{Res}_{M/L}\sigma)\),
read on cuspidal supports, and the first half of the plan note's E3,
\(\mathrm{Ch}_{M/L}(\Phi_L(\sigma))=\Phi_M(\sigma|_{W_M})\).

### (CI2) for the candidate

`IsCandidateGaloisEquivariant.{uK, uW, uV} S` is the following proposition.
For every \(k\), every `hM : StableExistsAt S.top k.succPNat`, every
\(w\in W_L\) (`Weil.Local.localWeilGroup S.base`) and every irreducible Weil
class \(\tau\) of rank \(k+1\) over \(M\),

```text
Extension.rankExtension S.top hM (Numerical.weilConjugate S w τ) =
  S.galoisConjugate
    (Weil.Local.finiteGaloisQuotient S.base S.top S.embedding S.isGalois w)
    k (Extension.rankExtension S.top hM τ).
```

The three operations and their conventions are those of the Library:

- `Numerical.weilConjugate S w τ` is \(\tau^w\), with
  \(\tau^w(y)=\tau(wyw^{-1})\) for \(y\in W_M\), where \(W_M\) is identified with
  its image in \(W_L\) (module `Langlands.Correspondence.HenniartCompatibleInjections`).
- `Weil.Local.finiteGaloisQuotient S.base S.top S.embedding S.isGalois w` is
  the image \(g\in\Gamma\) of \(w\): the restriction of \(w\) to \(M\), through
  the embedding of \(M\) into the separable closure of \(L\)
  (`Weil.Local.finiteGaloisQuotient_apply`).
- `S.galoisConjugate g k Π` is \(\Pi^g\), with \(\Pi^g(x)=\Pi(g(x))\), where
  \(g\) is applied to every matrix entry of \(x\in\mathrm{GL}_{k+1}(M)\)
  (module `Langlands.Correspondence.HenniartCyclicBaseChange`).

So the identity is \(\varphi_M(\tau^w)=\varphi_M(\tau)^{g}\) with \(g\) the
image of \(w\), and not its inverse. This is the identity that the local
Langlands correspondence satisfies. By the functoriality of local class field
theory, the reciprocity isomorphism
\(\theta_M\colon M^\times\to W_M^{\mathrm{ab}}\) (with either normalization)
satisfies \(\theta_M(g(x))=w\,\theta_M(x)\,w^{-1}\). For a character \(\chi\)
of \(M^\times\) and the character \(\tau\) of \(W_M\) with
\(\tau\circ\theta_M=\chi\), this gives
\(\tau^w(\theta_M(x))=\tau(\theta_M(g(x)))=\chi^g(x)\), so \(\tau^w\)
corresponds to \(\chi^g\). In higher ranks the same identity follows by
transport of structure along \(g\), because the correspondence is
characterized by invariants (local constants of pairs, twists) that are
preserved by it. Both \(\tau\mapsto\tau^w\) and \(\Pi\mapsto\Pi^g\) are right
actions, and \(w\mapsto g\) is a homomorphism, so the identity is compatible
with composition. This explanation is informal and is not a Lean proof.

Quantifying over all \(w\in W_L\) is equivalent to the route note's
\(\varphi_M(\tau^g)=\varphi_M(\tau)^g\) for \(g\in\operatorname{Gal}(M/L)\):
there \(\tau^g\) is the conjugate by any lift of \(g\) to \(W_L\), and the
conjugate by an element of \(W_M\) is isomorphic to \(\tau\). The module does
not prove this equivalence and does not use it. This is the second half of the
plan note's E3, "\(\Phi_M\) commutes with the action of
\(\operatorname{Gal}(M/L)\)".

## Statement in `Langlands.Henniart`

`CandidateBaseChangeCompatibilityStatement.{uK, uW, uV} : Prop` says: for every
prime `p` and every step `S : Numerical.CyclicPrimeStep.{uK} p` there is one
map `Ch : Numerical.CyclicBaseChangeMap.{uK, uV} S` with

- `Numerical.IsWeakCyclicBaseChange S Ch`, the weak cyclic base change
  (W1)–(W4) of the module `Langlands.Correspondence.HenniartCyclicBaseChange`;
- `Numerical.IsCandidateBaseChangeCompatible.{uK, uW, uV} S Ch`, (CI1) for the
  candidate;
- `Numerical.IsCandidateGaloisEquivariant.{uK, uW, uV} S`, (CI2) for the
  candidate.

The statement has no premises. The module does not prove it.

**Status of the mathematics.** That Henniart's candidate is compatible with
cyclic base change of prime degree is not a published result. Henniart (2000)
does not state it: there the bijectivity of the candidate is obtained from
Henniart's numerical theorem (Henniart 1988, Théorème 1.2). The route note,
§6.5, source (b) (lines 1164–1167), gives the assessment that it should
follow from the construction of the candidate by the usual global argument,
and marks this assessment as not a published statement. The proposition
records that assessment as a statement.

**One map for all ranks.** The same `Ch` serves every rank, and it is the map
of a weak cyclic base change, so that one witness supplies (W1)–(W4) and
(CI1) together, as `CompatibleNumericalInjectionsStatement` requires.

**Rank by rank.** (CI1) and (CI2) are asked only in the ranks where the
candidates are defined: each takes the proofs of `StableExistsAt` that the
candidate needs as hypotheses, and nothing else. The statement can therefore be
used inside an induction on the rank. In Henniart's induction (Henniart 2000,
§4.3; the Library's `RankInductionStepStatement` and
`ChoiceIndependenceStepStatement`) stable existence in rank \(n\) is obtained
from the ranks below \(n\), using the surjectivity of the candidate there.

**The full (CI2).** The proposition keeps (CI2) itself, not only the property
`Numerical.ReflectsGaloisInvariance` that the descent uses. That property
follows from (CI2) and the injectivity of the candidate, which
`Extension.rankExtension_injective` proves from `CandidateExistenceStatement`
and a geometric reciprocity map: if \(\varphi_M(\tau)\) is fixed by
every \(g\in\Gamma\), then
\(\varphi_M(\tau^w)=\varphi_M(\tau)^{g}=\varphi_M(\tau)\) for every
\(w\in W_L\), hence \(\tau^w=\tau\). This argument is not formalized here.

**Forgetting the compatibility.** Keeping `Ch` and its first property for every
`p` and `S` gives the Library's `LocalCyclicBaseChangeStatement`, input (I3).

## Provenance

- Plan note (`operator-external-inputs-plan-2026-11-16`), interface E3
  (line 240): "For the candidates \(\Phi_L\) of P1:
  \(\mathrm{Ch}_{M/L}(\Phi_L(\sigma))=\Phi_M(\sigma|_{W_M})\) for irreducible
  \(\sigma\), and \(\Phi_M\) commutes with the action of
  \(\operatorname{Gal}(M/L)\)." Its proof is global: the candidate is read off
  from the automorphic representations of Harris's proposition, and it needs
  B1–B3 for them, C2, and the compatibility of global base change with the
  local maps of E2 at the place of interest, Arthur–Clozel III.5.1 (line 241;
  Section 4.6, lines 704–773, with the recommendation to state III.5.1 in a
  restricted form). In the Library these inputs are the statements
  `Automorphic.Unramified.CyclicStableDescentStatement`,
  `Automorphic.Unramified.CyclicRegularInductionStatement`,
  `Automorphic.Unramified.CyclicRegularOrbitLiftStatement`,
  `Automorphic.Unramified.CuspidalSpectralRigidityStatement`,
  `LocalCyclicBaseChangeStatement` and
  `Automorphic.Unramified.RestrictedCyclicBaseChangeCompatibilityStatement`.
- Route note (`operator-numerical-llc-route-2026-11-16`), §6.5 `sec:ci`
  (lines 1150–1174): hypothesis (CI) with (CI1) and (CI2), source (b) and
  Remark `rem:CI2`. The route note states (CI) for numerical injections in
  the ranks \(d\le N\). This module states it for the candidate, in every rank
  where the candidate is defined. §7.1 `sec:units`, last paragraph
  (lines 1317–1320): with source (b), the natural final theorem has
  candidate existence *with its compatibility with cyclic base change* as a
  premise.
- Guy Henniart, *Une preuve simple des conjectures de Langlands pour GL(n)
  sur un corps p-adique* (2000, `henniart-2000-simple-proof`), §§3.7–3.8 and
  4.1–4.4, pp. 451–453: the candidate.
- Guy Henniart, *La conjecture de Langlands locale numérique pour GL(n)*
  (1988, `henniart-1988-numerical`), Théorème 1.9 (pp. 501–502) and §7
  (equivariance in 7.9, pp. 528–529): source (a) of the route note, injections
  compatible with base change built by another construction. This module does
  not follow source (a).
- James Arthur and Laurent Clozel, *Simple algebras, base change, and the
  advanced theory of the trace formula* (1989,
  `arthur-clozel-1989-base-change`), Chapter 3, Theorem 5.1 (printed p. 212):
  compatibility of local and global base change.
