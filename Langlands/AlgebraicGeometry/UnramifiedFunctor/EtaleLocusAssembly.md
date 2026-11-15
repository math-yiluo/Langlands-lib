# Openness of the étale locus of a closed subscheme of an étale chart (proof)

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.EtaleLocusAssembly`
proves

```
theorem EtaleLocus.closedEtaleLocusOpen_of_generic : ClosedOfGenericStatement.{u, v}
```

(namespace `Langlands.AlgebraicGeometry.UnramifiedFunctor`). The statement is
explained in `EtaleLocusClosedOfGeneric.md`. The proof uses only the standard
axioms `propext`, `Classical.choice` and `Quot.sound`. It imports
`EtaleLocusOpenA` and the statement module `EtaleLocusClosedOfGeneric`. The
supporting modules are, in dependency order:

- `EtaleLocusBasic`, `EtaleLocusStalk`, `EtaleLocusLevel`, `EtaleLocusStd`;
- `EtaleLocusGen`, `EtaleLocusCaseA`, `EtaleLocusStep`, `EtaleLocusOpenA`.

Each has its own Markdown.

## Overview of the proof

Fix the data of `ClosedEtaleLocusOpenStatement`:

- `R` noetherian;
- `F` with `MurreConditions F`, so strong (F5) holds;
- the representability hypotheses on `Spec 𝒪_{Spec R,s}` and on `Spec (R/I)`
  for `I ≠ 0`;
- `R'` étale over `R`, hence noetherian (`Algebra.FiniteType.isNoetherianRing`);
- `𝔍` and `ξ`.

Let `E` be the étale locus of `ξ` in `Spec (R'/𝔍)`.

1. Dictionary (`EtaleLocusBasic`). Étaleness at `w` is the condition `KillAt`
   on ring maps `R' → A` into local artinian rings.
2. Levels (`EtaleLocusLevel`, `EtaleLocusStd`). For a ring `D` under `R'` over
   which the base change of `F` is represented by `X`, a point `w` and a local
   datum `L` give a point of `X`. The stalk `Λ` there has maps
   `θ : D → Λ` and `ψ : Λ → L`. Étaleness at `w` for maps factoring through
   `D` is equivalent to the vanishing of `𝔍` under `θ`. Moreover
   `ker ψ = θ(𝔍)Λ`.
3. Generization (`EtaleLocusGen`). `E` is stable under generization.
4. Neighbourhoods. Every `y ∈ E` has an open neighbourhood `V` whose points
   specializing `y` lie in `E`:
   - If the prime of `R` below `y` is not nilpotent, this is
     `exists_open_of_not_le_nilradical` (`EtaleLocusCaseA`, `EtaleLocusStep`,
     `EtaleLocusOpenA`).
   - Otherwise the hypothesis of `ClosedOfGenericStatement` gives `V` on which
     `𝔍O_w` is nilpotent and `NoLargerLift O_w ξ` holds, and
     `infinitesimallyEtaleAt_of_noLargerLift` puts all of `V` into `E`.
5. Noetherian induction (`isOpen_of_specializes`, below).

## `isOpen_of_specializes`

Let `X` be a noetherian quasi-sober space and `E ⊆ X` a set that is stable
under generization. Suppose every `y ∈ E` has an open neighbourhood `V` with
`w ∈ E` for every `w ∈ V` specializing `y`. Then `E` is open.

Proof. By well-founded induction on closed sets (`Closeds X` is well-founded
since `X` is noetherian), `s \ E` is closed for every closed `s`. Take `s`.

- If `s` is empty, the claim is clear.
- If `s` is irreducible, let `η` be its generic point (`QuasiSober.sober`).
  - If `η ∉ E`, then `s ∩ E = ∅` by stability under generization, and
    `s \ E = s`.
  - If `η ∈ E`, take `V` for `η`. Every point of `s ∩ V` specializes `η`, so
    `s ∩ V ⊆ E`. Thus `s \ E = (s \ V) \ E`, where `s \ V` is a closed set
    strictly smaller than `s` (it misses `η`). Apply the induction
    hypothesis.
- Otherwise `s ⊆ z₁ ∪ z₂` with closed `z₁`, `z₂` and `s ⊄ z₁`, `s ⊄ z₂`
  (`isPreirreducible_iff_isClosed_union_isClosed`). Then
  `s \ E = (s ∩ z₁) \ E ∪ (s ∩ z₂) \ E` with both pieces smaller.

For `s = X` this says `Eᶜ` is closed.

This is the openness criterion Murre quotes (EGA III, chap. 0,
Corollary 9.2.6) in the form used here.

## `closedEtaleLocusOpen_of_generic`

Apply `isOpen_of_specializes` to `X = PrimeSpectrum (R'/𝔍)` (noetherian, as
`R'/𝔍` is a noetherian ring) and `E`. Specialization in `PrimeSpectrum` is
inclusion of primes (`PrimeSpectrum.le_iff_specializes`).

- Stability under generization: `infinitesimallyEtaleAt_of_le`.
- Neighbourhoods: case split as in step 4 above.

## Sources

J. P. Murre, *Representation of unramified functors. Applications (according
to unpublished results of A. Grothendieck)*, Séminaire Bourbaki exp. 294
(1964–65), registered as `murre-1965-bourbaki-294-unramified-functors`
(SHA-256 `e36edaf9f965bbc92b0bdc36d8026fd7c87d890b859841d1dd965193385227dd`).
Proof of Lemma 2: printed pp.250–252 (PDF pp.9–11). The implemented proof
follows Murre's plan:

- reduction to a closed subscheme of an étale scheme (published separately);
- stability under generization;
- the openness criterion;
- the two cases of a non-generic and a generic image point.

Two departures from Murre:

- Case (a) uses the stalks of the representing schemes of the thickenings
  `Spec (R/𝔭^{n+1})` and an Artin–Rees argument instead of the formal scheme
  `Ŷ → F̂`.
- The split between the cases is by whether the prime of `R` below `y` is
  nilpotent, rather than whether it is minimal.
