# The two halves of the compatibility of Henniart's candidate with cyclic base change

Module `Langlands.Correspondence.HenniartCandidateBaseChangeCompatibilityReductionStatement`,
namespace `Langlands.Henniart`, universe parameters `uK uW uV`. It imports only
`Langlands.Correspondence.HenniartCandidateBaseChangeCompatibility`, which
defines `Numerical.IsCandidateBaseChangeCompatible`,
`Numerical.IsCandidateGaloisEquivariant` and
`CandidateBaseChangeCompatibilityStatement`; none of these is restated here.

The module gives two proposition definitions and proves nothing. Together
with candidate existence, the two propositions imply
`CandidateBaseChangeCompatibilityStatement` (see "How the halves compose"
below).

## Why the statement splits

`CandidateBaseChangeCompatibilityStatement.{uK, uW, uV}` is interface E3 of the
operator's plan note (`operator-external-inputs-plan-2026-11-16`,
`external-inputs-plan.tex`, line 240) for the Library's candidate
`Extension.rankExtension`. For every prime `p` and every cyclic prime-degree
step `S : Numerical.CyclicPrimeStep.{uK} p` (a cyclic extension \(M/L\) of
prime degree, \(L=\) `S.base`, \(M=\) `S.top`), it asks for

1. one map `Ch : Numerical.CyclicBaseChangeMap.{uK, uV} S` with
   `Numerical.IsWeakCyclicBaseChange S Ch` and
   `Numerical.IsCandidateBaseChangeCompatible S Ch` ((CI1) for the candidate),
   and
2. `Numerical.IsCandidateGaloisEquivariant S` ((CI2) for the candidate over
   \(M\)).

The second property does not mention `Ch`. It concerns the candidate over
\(M\) alone. The two properties are expected to have proofs of different
kinds, so they are stated separately.

- (CI2) is a local statement. An element \(w\in W_L\) acts on \(W_M\) by
  conjugation, and its image \(g\in\operatorname{Gal}(M/L)\) is an automorphism
  of \(M\) that fixes \(L\), hence \(\mathbb{Q}_p\). A candidate at a finite
  quotient of the absolute Galois group is, by definition
  (`StableMap.IsCandidate`), a map of unitary lattices whose domain contains
  the classes factoring through that quotient and which has the properties of
  Henniart (2000), 3.8 (a)–(c) (`LatticeMap.HenniartProperties`:
  compatibility with contragredients, twists, determinants and local factors
  of pairs, and the description of characters by local class field theory).
  These properties are formulated intrinsically in terms of the field, its
  Weil group and the groups \(\mathrm{GL}_n\) over it. Transport of structure
  along the pair (conjugation by \(w\), \(g\)) should therefore carry
  candidates to candidates, hence stable images to stable images, hence the
  candidate image of \(\tau\) to that of \(\tau^w\). The Markdown of
  `HenniartCandidateBaseChangeCompatibility` ("(CI2) for the candidate")
  gives an informal argument of the same kind for the local Langlands
  correspondence. This is not a proof, and it is not a published result.
- (CI1) with a weak cyclic base change is global. The route note
  (`operator-numerical-llc-route-2026-11-16`, `numerical-LLC-route.tex`, §6.5,
  source (b), lines 1164–1167) and the plan note (line 241; Section 4.6,
  lines 704–773) expect it from the global construction of the candidate
  (Harris's proposition), the global cyclic transfer B1–B3, the rigidity C2,
  the local maps of E2 and their compatibility with global base change
  (Arthur–Clozel, Chapter 3, Theorem 5.1). The route note marks this as an
  assessment and not a published statement.

Both halves take candidate existence as a premise. The candidate
`Extension.rankExtension K hS` is defined by a choice of a stable decomposition
\(\sigma=z\cdot b_0\) and of a stable image of \(b_0\). In the Library, the
independence of the value from these choices is
`Extension.rankExtensionBasis_eq`, which takes
`UnramifiedTwistIndependenceStatement` as a hypothesis; the Library derives
that statement from candidate existence and local reciprocity
(`Extension.unramifiedTwistIndependence_of_reciprocity`, whose reciprocity
hypothesis `LocalClassField.CommonClosureReciprocityExistence` is the theorem
`LocalClassField.commonClosureReciprocityExistence`). An identity between two
values of the candidate, as in (CI1) and (CI2), compares two such choices.
The universes of the premise,
`CandidateExistenceStatement.{uK, uW, uV, uW, uK}`, are those of
`Extension.rankExtension_injective` with the stable-image universe `uE := uW`
of the candidate (`StableMap.StableExistsAt.{uK, uW, uV, uW}`), and with the
quotient universe `uQ := uK` of the finite quotients in
`StableMap.IsStableImage`.

## Definitions in `Langlands.Henniart`

### `CandidateGaloisEquivarianceReductionStatement.{uK, uW, uV}`

```text
CandidateExistenceStatement.{uK, uW, uV, uW, uK} →
  ∀ (p : ℕ) [Fact p.Prime] (S : Numerical.CyclicPrimeStep.{uK} p),
    Numerical.IsCandidateGaloisEquivariant.{uK, uW, uV} S
```

If every finite quotient of the absolute Galois group of every p-adic field has
a candidate (Henniart 2000, Théorème 3.1 with §§3.7–3.8, in the local form of
`HenniartStableMapStatement`), then for every prime `p` and every step `S`,
(CI2) holds for the candidate over `S.top`. Unfolded: for every `k`, every
`hM : StableMap.StableExistsAt.{uK, uW, uV, uW} S.top k.succPNat`, every
\(w\in W_L\) and every irreducible Weil class \(\tau\) of rank \(k+1\) over
\(M\),

```text
Extension.rankExtension S.top hM (Numerical.weilConjugate S w τ) =
  S.galoisConjugate
    (Weil.Local.finiteGaloisQuotient S.base S.top S.embedding S.isGalois w)
    k (Extension.rankExtension S.top hM τ).
```

The conventions (\(\tau^w(y)=\tau(wyw^{-1})\), \(\Pi^g(x)=\Pi(g(x))\), and
\(g\) the image of \(w\), not its inverse) are those of the definition of
`Numerical.IsCandidateGaloisEquivariant`.

### `CandidateCompatibleWeakBaseChangeReductionStatement.{uK, uW, uV}`

```text
CandidateExistenceStatement.{uK, uW, uV, uW, uK} →
  ∀ (p : ℕ) [Fact p.Prime] (S : Numerical.CyclicPrimeStep.{uK} p),
    ∃ Ch : Numerical.CyclicBaseChangeMap.{uK, uV} S,
      Numerical.IsWeakCyclicBaseChange S Ch ∧
        Numerical.IsCandidateBaseChangeCompatible.{uK, uW, uV} S Ch
```

If candidate existence holds, then every step has one weak cyclic base change
`Ch` ((W1)–(W4) of `HenniartCyclicBaseChange`) that satisfies (CI1) for the
candidate in every rank where the candidates are defined: for every `k`, every
`hL : StableExistsAt S.base k.succPNat`, every irreducible Weil class
\(\sigma\) of rank \(k+1\) over \(L\), every multiset \(m\) with
`Numerical.IsRestrictionDecomposition S σ m` and every proof `hm` that the
candidate over \(M\) is defined in the rank of each member of \(m\),

```text
Ch k (Extension.rankExtension S.base hL σ) =
  m.pmap (fun τ h => ⟨τ.1, Extension.rankExtension S.top h τ.2⟩) hm.
```

One `Ch` serves every rank. Forgetting (CI1) gives, for each step, the
conclusion of `LocalCyclicBaseChangeStatement.{uK, uV}`, input (I3). So this
proposition and candidate existence together imply
`LocalCyclicBaseChangeStatement.{uK, uV}`: this half contains local cyclic
base change of prime degree in the weak form.

## How the halves compose

Candidate existence and the two halves imply
`CandidateBaseChangeCompatibilityStatement.{uK, uW, uV}`. Fix `p` and `S`. The
second half, applied to candidate existence, `p` and `S`, gives `Ch` with
`IsWeakCyclicBaseChange S Ch` ((W1)–(W4)) and
`IsCandidateBaseChangeCompatible S Ch` ((CI1)); the first half, applied to the
same data, gives `IsCandidateGaloisEquivariant S` ((CI2)). These three facts
are the conclusion of `CandidateBaseChangeCompatibilityStatement` for `p` and
`S`, with the witness `Ch`. So a proof of
`CandidateBaseChangeCompatibilityStatement` at universes `uK, uW, uV` follows
from proofs of the two halves and of
`CandidateExistenceStatement.{uK, uW, uV, uW, uK}`. This module does not
formalize the composition.

## What is not claimed

This module proves neither half, and neither half is a published result. The
local half, (CI2), is expected from transport of structure along the
automorphism of \(M\) given by an element of \(W_L\). The global half, a weak
cyclic base change with (CI1), is the assessment of source (b) of the route
note, §6.5. The converse implications are not claimed.

## Sources

- Operator route note *The numerical local Langlands correspondence for GL_n:
  counts on the two sides and the recommended route of proof*
  (`operator-numerical-llc-route-2026-11-16`, `numerical-LLC-route.tex`),
  §6.5 `sec:ci`, lines 1150–1174: hypothesis (CI) with (CI1), (CI2), source
  (b) (lines 1164–1167) and Remark `rem:CI2`.
- Operator plan note *Formalizing the large external inputs of the local
  Langlands correspondence for GL_n* (`operator-external-inputs-plan-2026-11-16`,
  `external-inputs-plan.tex`), interface E3, lines 240–241, and Section 4.6,
  lines 704–773.
- Guy Henniart, *Une preuve simple des conjectures de Langlands pour GL(n)
  sur un corps p-adique* (2000, `henniart-2000-simple-proof`), Théorème 3.1
  and §§3.7–3.8 (printed pp. 448–451): candidate existence and the properties
  of the candidates; §§4.1–4.4 (pp. 452–453): stable images and their
  extension to all irreducible classes.
- James Arthur and Laurent Clozel, *Simple algebras, base change, and the
  advanced theory of the trace formula* (1989,
  `arthur-clozel-1989-base-change`), Chapter 3, Theorem 5.1: compatibility of
  local and global base change, cited by both operator notes for the global
  half.
