# Prime total ramification: the first lower group

Worker 473 authored this paired statement and documentation. Worker 96 supplied
its exact arithmetic formulation, source route and separation from the parent
single-break target. This module defines the proposition
`Langlands.LocalClassField.PrimeTotallyRamifiedWildCriterion.{u,v}`. It contains
no proof of that proposition.

The proposition quantifies every `p : ℕ` with `[Fact p.Prime]` and every pair
`F : PadicField.{u} p`, `L : PadicField.{v} p`, with independent arbitrary field
universes. It retains the supplied `Algebra F.Carrier L.Carrier`, the compatible
`IsScalarTower (Padic p) F.Carrier L.Carrier`, finite dimensionality and
Galoisness. In particular the algebra used by `Module.finrank` and the algebra
used by the actual automorphism group are the same supplied structure.

Write `ell := Module.finrank F.Carrier L.Carrier`,
`TF := F.canonicalTopologicalData` and `TL := L.canonicalTopologicalData`.
The only further hypotheses are

```text
Nat.Prime ell
TL.ramificationIndex = ell * TF.ramificationIndex.
```

The conclusion is exactly

```text
Ramification.Padic.lowerRamificationGroup TL F.Carrier 1 = ⊤ ↔ ell = p.
```

Here `⊤` is the whole group of `F.Carrier`-algebra automorphisms of `L.Carrier`.
The lower group is the published actual subgroup: an automorphism belongs to
its first group precisely when its displacement of every element of
`TL.Integers` lies in the square of that integer ring's maximal ideal. The
published zeroth-group identity identifies the actual zeroth lower group with
`Ramification.Padic.inertia TL F.Carrier`, the kernel of the actual residue
field action. These objects come from
`Langlands.LocalFactor.Ramification.Galois`; canonical topological data come
from `Langlands.LocalField.Canonical`. They are reused unchanged.

`ramificationIndex` is the canonical absolute ramification index, measured by
the normalized order of `p`. Thus the displayed index equality expresses total
ramification of this supplied compatible extension. Passing from that equality
to trivial residue extension and then to the actual inertia group being the
whole automorphism group requires an arithmetic argument. It is not an extra
premise, a supplied certificate or an axiom in this statement.

## Original source and derivation

Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg,
Graduate Texts in Mathematics 67, Springer, 1979, registered source
`serre-1979-local-fields`, retained at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

Chapter IV §1, Lemma 1 and Proposition 1, printed pages 61–62 / PDF pages
68–69, define the lower groups by the action on the integer ring modulo the
`(i+1)`st maximal-ideal power and identify the zeroth group with inertia.
The chapter's opening hypotheses include the fundamental degree identity and
separable residue extension. Residue fields of the p-adic fields here are finite,
so residue separability is automatic.

Chapter IV §2, Proposition 7 and Corollaries 1 and 3, printed pages 67–68 /
PDF pages 74–75, give the tame quotient `G₀/G₁` of order prime to the residue
characteristic, and the fact that `G₁` is a `p`-group. These give this statement
as follows, once the canonical total-ramification hypothesis has been connected
to `G₀ = G` for the actual supplied extension. Galoisness identifies `|G|` with
`ell`, which is prime. If `G₁ = G`, the `p`-group property forces `ell = p`.
Conversely, if `ell = p`, the order of `G₀/G₁` divides `p` and is prime to `p`,
so this quotient is trivial and `G₁ = G`.

The conversion from the absolute-index hypothesis can use the published
canonical identity `Langlands.PadicField.ramificationIndex_mul_extensionResidueDegree`
in `Langlands.Galois.Local.UnramifiedCriterionProof`. Its positive absolute
indices force relative residue degree one after matching the embedding-induced
algebra with the supplied algebra. One must then show that residue classes have
representatives from the base integer ring, hence are fixed by every actual
base-field automorphism. This identifies the actual inertia kernel with `⊤`.
The published module
`Langlands.ClassFieldTheory.Local.PrimeRamificationArithmeticSupport` already
provides this bridge as
`Langlands.LocalClassField.inertia_eq_top_of_canonical_totalRamification`
and the full criterion as
`Langlands.LocalClassField.lowerRamificationGroup_one_eq_top_iff_prime_degree`.
A separate proof of the named proposition can reuse that support. This statement
module neither imports it nor assumes the bridge.

Chapter V §3, opening, printed page 83 / PDF page 90, independently records the
prime totally ramified single-break case and says that its break is positive
precisely when the prime degree is the residue characteristic. The source uses
cyclic prime order; a finite Galois group of prime order is cyclic, so the
Galois prime-degree hypothesis here has the same scope. The present proposition
isolates only its first-group arithmetic criterion. It does not assert or
assume a single-break pattern and contains no Herbrand function or norm claim.

Worker 473 read the cited original passages and visually checked PDF page 90.
The registered author corrections `serre-book-corrections-2019`,
*Corrections to J-P. Serre's books* (2019), retained at
`/home/taskhub/pilot/literature/Jean-Pierre Serre — Corrections to J-P. Serre's books (2019).pdf`,
SHA256 `b76739179d067850770081597a8e9ced68135ebf80678876605f471297a4fee5`,
were checked on PDF pages 2–3. They list no correction to printed pages 61–62,
67–68 or 83. The listed printed-page 74–75 corrections distinguish Herbrand
phi glyphs and do not affect this first-group statement.

## Scope and provenance

This is an internal arithmetic support statement derived from the cited
ramification theory for the project's canonical p-adic objects. It has no
inertia, `p`-group, tame-character, kernel or desired-criterion certificate as a
premise. It imports no parent break target, norm target, local reciprocity result
or pending proof. The parent declaration and its import closure are unchanged.
A proof and its independent acceptance belong to a separate successor after
this target is accepted and published.
