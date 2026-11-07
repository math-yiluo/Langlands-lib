# Tadić's exhaustion argument as an implication

Author: Worker 1792. This pair states one proposition definition,
`Langlands.Classification.TadicExhaustionReduction`, in module
`Langlands.Representation.Classification.TadicExhaustionReductionStatement`.
**It is not proved here.** The module proves no theorem. It adds no axiom, no
`sorry` and no structure field.

The proposition is an implication. Its three hypotheses are published Library
statements, and its conclusion is the published exhaustion statement
`TadicUnitaryDualExhaustion`. It records the logical structure of Tadić's proof of
the exhaustion. A proof of this implication, together with proofs of the three
hypotheses, proves `TadicUnitaryDualExhaustion`.

## Source

M. Tadić, *Classification of unitary representations in irreducible
representations of general linear group (non-Archimedean case)*, Ann. Sci.
ÉNS (4) 19 (1986), 335–382, literature ID `tadic-1986-unitary`. PDF page =
printed page − 333.

- Theorem A.10 and its proof: printed pp.377–379 (PDF pp.44–46). Theorem A.10(ii)
  is the exhaustion: "If `π ∈ Ĝ_m` then there exist `τ_1, …, τ_l ∈ B` so that
  `π = τ_1 × … × τ_l`", where `B` is the set of the representations
  `⟨a(n,d)^ρ⟩` and `π(⟨a(n,d)^ρ⟩, α)` with `n, d ∈ ℕ`, `ρ ∈ C^u` and
  `0 < α < 1/2`.
- The proof is by induction on `m`. It uses Lemma 4.8 (printed p.360),
  Corollaries A.6 and A.7 (printed p.375), Theorem A.9 (printed p.377), which
  rests on Theorem A.8 (printed p.375), and Lemma 6.3 (printed p.366). It also
  uses the Langlands classification of §5.2 (printed pp.361–362): for every
  multisegment `a` the standard representation `λ(a)` "has a unique irreducible
  quotient, which is denoted by `L(a)`", and "the mapping `a ↦ L(a)` … is a
  bijection".

## Parameters and conventions

The parameters are an arbitrary prime `p` with `[Fact p.Prime]`,
`F : PadicField.{uF} p` and `T : F.TopologicalData`, all explicit. The field
universe `uF` and the representation universe `uV` are independent and are passed
unchanged to every hypothesis and to the conclusion.

## The statement

`TadicExhaustionReduction F T` is

```
TadicExhaustionLemmaStatements F T → SpehUnitarizability F T →
  MultisegmentHeadClassification F T → TadicUnitaryDualExhaustion F T
```

with universes `.{uF, uV}` throughout. The hypotheses are the following published
propositions.

1. `TadicExhaustionLemmaStatements F T`, module
   `Classification.TadicExhaustionLemmasStatement`. It is the conjunction of
   Tadić's Lemma 4.8(ii) (existence of a factorization into members of `X_m` under
   `(U^m)`), Lemma 6.3 (`L(a(n,d)^ρ) ≇ ⟨a(n,d)^ρ⟩` for `0 < n < d`) and the
   finite form of Corollary A.6(ii) (an irreducible product of Langlands heads
   `L(a_i)` is a Langlands head of `∑ a_i`).
2. `SpehUnitarizability F T`, module `Classification.SpehUnitarizabilityStatement`:
   Tadić's Theorem A.8, every Speh representation `u(δ,k)` with `δ` square-integrable
   is unitarizable.
3. `MultisegmentHeadClassification F T`, module
   `Classification.MultisegmentClassificationStatement`: Langlands heads `π` of `a`
   and `π'` of `b` (the published relation `Multisegment.IsLanglandsHead`) on the
   same group are isomorphic exactly when `a = b`. This is the bijectivity of
   `a ↦ L(a)` of §5.2. Tadić's argument uses the direction "isomorphic heads have
   equal multisegments".

The other part of §5.2 that Tadić uses, existence of `L(a)`, is needed only for the
multisegments `a(d,n)^ρ` with `ρ` unitary. There it is the existence of a strong
Langlands head of a tempered standard module, which the Library already proves
(`glRegularLanglandsHeadExistence`), so it is not a hypothesis.

The conclusion is `TadicUnitaryDualExhaustion F T` of module
`Classification.TadicUnitaryStatement`: every irreducible unitarizable smooth
representation of `GL_(n+1)` is isomorphic to a normalized product of Tadić
building blocks (Speh representations and complementary series of Speh
representations).

## Correspondence with Tadić's proof

The hypotheses are the external inputs of Tadić's proof of A.10(ii) and (iii) that
the Library does not yet prove. Everything else in that proof is to be derived from
the published Library:
the identification `⟨a(n,d)^ρ⟩ = L(a(d,n)^ρ)` (A.10(iii)) by the same induction,
the identification of `L(a(d,n)^ρ)` with a Speh representation (A.9), the support
argument "`supp ⟨a(n,d)^ρ⟩ = supp a(u,v)^σ` implies
`L(a(n,d)^ρ) ∈ {⟨a(n,d)^ρ⟩, ⟨a(d,n)^ρ⟩}`", and the comparison of
`L(a(n,d)^ρ)` with products of members of `X_(m-1)` through Corollary A.6 and the
classification. Corollary A.7 is used by Tadić only through A.6 and the
unitarity of the factors, which the hypotheses supply.

Theorem A.10 and its ingredients A.8 and A.9 are stated by Tadić for fields of
characteristic zero. Every `PadicField` is a finite extension of `ℚ_p`, so this
holds here.

Provenance: derived. The proposition is not a single statement of the source; it
records which published statements Tadić's proof of A.10 combines.
