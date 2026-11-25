# Transport of reflections and root data along a field extension

This module is part of the proof of Borel–Tits 1965, Théorème 7.2 (`MaximalSplitSubgroupProof`).
That proof builds a subgroup `F` of `G` over `k` and proves it reductive after base change to an
extension `K`, such as an algebraic closure. This module moves two pieces of data from `k` to `K`
(parts A3a and A3b below): the Weyl points through lattice reflections, and the root combinatorics
in the form that the module `MaximalSplitGeneratedReductive` uses over `K`.

This is a technical module with no counterpart in the literature. It does not use Borel–Tits
3.22. Only `baseChange_mem_nonmultipliableBaseChange_iff`, `mem_closure_of_baseChange_mem_cone`
and A3b assume that `S` is a split torus, and only to know that base change of characters is
injective.

## Setting

Namespace `Langlands.GroupScheme.MaximalSplitSubgroup`. Throughout, `k` and `K` are fields in the
same universe `u` with `[Algebra k K]`, and `bc := algebraBaseMap k K : Spec K ⟶ Spec k`.
`S` is a commutative group scheme over `Spec k` and `H` a group scheme over `Spec k`; neither is
assumed reductive, smooth or affine. Write `ψ := characterLattice.baseChange bc S`, the published
additive map from the characters of `S` to the characters of `S_K`, and
`cocharacterLattice.baseChange bc S` for the published map on cocharacters. The published
`latticePairing_baseChange` says that `ψ` and the cocharacter map preserve the pairing.
`IsSplitTorus.characterLattice_baseChange_bijective` (published) says that `ψ` is bijective when
`S` is a split torus.

## Definition

- `nonmultipliableBaseChange K R` (entry definition): for a set `R` of characters of `S`, the set
  of characters of `S_K` given by `ψ '' {c | c ∈ R ∧ 2 • c ∉ R}`. When `R` is the set of relative
  roots of a maximal split torus, it is the base change of the nonmultipliable roots. This is the
  root set over `K` in A3b.
- `mem_nonmultipliableBaseChange_iff`: membership unfolds to
  `∃ c, (c ∈ R ∧ 2 • c ∉ R) ∧ ψ c = χ` (by `Iff.rfl`).
- `baseChange_mem_nonmultipliableBaseChange_iff`: for a split torus `S`,
  `ψ c ∈ nonmultipliableBaseChange K R ↔ c ∈ R ∧ 2 • c ∉ R`. This holds because `ψ` is injective.

## Results

- `baseChange_mapIso_latticeReflectionIso`: for `a` a character, `ν` a cocharacter and
  `h : latticePairing S a ν = 2`, the base change (`(CommGroupScheme.baseChange bc).mapIso`) of
  the published `latticeReflectionIso a ν h` equals
  `latticeReflectionIso (ψ a) (cocharacterLattice.baseChange bc S ν) h'`, where `h'` is `h`
  transported by `latticePairing_baseChange`. Proof: the homomorphisms are `𝟙 - a ≫ ν` and its
  base-changed counterpart (`latticeReflectionIso_hom`). The base-change functor is additive and
  preserves composition. The isomorphisms `Gm.commBaseChangeIso bc` inserted by the two
  base-change maps cancel.
- **(A3a)** `Langlands.GroupScheme.IsNormalizingPoint.baseChange_latticeReflection`: for
  `t : S.toGrp ⟶ H` and a rational point `n` of `H`, if
  `IsNormalizingPoint t n (latticeReflectionIso a ν h)`, then the base-changed point
  `baseChangeBasePoint bc H n` normalizes `(GroupScheme.baseChange bc).map t` through
  `latticeReflectionIso (ψ a) (cocharacterLattice.baseChange bc S ν) h'`. The declaration sits in
  the namespace `Langlands.GroupScheme.IsNormalizingPoint` (stated with `_root_`), so it is
  available as `hn.baseChange_latticeReflection`. Proof: the published
  `IsNormalizingPoint.baseChangeBasePoint` gives the statement for the base-changed isomorphism,
  which the previous lemma rewrites.
- `characterLattice_baseChange_reflection`: for characters `c`, `d` and a cocharacter `ν`,
  `ψ (c - ⟨c, ν⟩ • d) = ψ c - ⟨ψ c, ν_K⟩ • ψ d`, where `ν_K` is the base-changed cocharacter.
- `cone_baseChange`: for a finite set `D` of characters, the `cone` of the family
  `d ↦ ψ d` (indexed by `↥D`) is the image under `ψ` of `AddSubsemigroup.closure D`.
- `mem_closure_of_baseChange_mem_cone`: for a split torus `S`, if `ψ c` lies in that cone then
  `c ∈ AddSubsemigroup.closure D`.
- **(A3b)** `baseChange_rootData`: let `S` be a split torus, `R' ⊆ R` sets of characters with `R`
  stable under negation, `D` a finite set of characters, `lam` a cocharacter and `ν d` a
  cocharacter for each `d ∈ D`. Assume:
  - `hpos`: `0 < ⟨d, lam⟩` for `d ∈ D`;
  - `hgen`: `⟨c, lam⟩ ≠ 0` for `c ∈ R`;
  - `hclos`: if `c ∈ R` lies in `AddSubsemigroup.closure D`, then `2 • c ∉ R`;
  - `hsep`: for each `d₀ ∈ D` some cocharacter `mu` has `⟨d₀, mu⟩ = 0` and `0 < ⟨e, mu⟩` for the
    other `e ∈ D`;
  - `hν`: `⟨d, ν d⟩ = 2`;
  - `hrefl`: every property `Q` that holds on `D` and is preserved by the reflections
    `c ↦ c - ⟨c, ν d⟩ • d` (for `c ∈ R` with `2 • c ∉ R`) holds on every `c ∈ R` with
    `2 • c ∉ R`;
  - `hred`: two elements `α`, `β` of `R` with `2 • α, 2 • β ∉ R` and `m • β = n • α` for some
    `m ≠ 0` satisfy `β = α` or `β = -α`.

  Set `aK d := ψ d`, `νK d := cocharacterLattice.baseChange bc S (ν d)` (both indexed by `↥D`),
  `lamK := cocharacterLattice.baseChange bc S lam` and `ΦK := nonmultipliableBaseChange K R`.
  The conclusion has seven clauses, matching the hypotheses of `MaximalSplitGeneratedReductive`:
  1. `0 < ⟨aK d, lamK⟩` for every `d`;
  2. `⟨χ, lamK⟩ ≠ 0` for every `χ ∈ ψ '' R'`;
  3. every `d` has an isolating cocharacter: `∃ eta, IsIsolatingCocharacter aK d eta`;
  4. `⟨aK d, νK d⟩ = 2`;
  5. every `χ ∈ ψ '' R'` with `χ ∈ cone aK` or `-χ ∈ cone aK` lies in `ΦK`;
  6. `ΦK` is reduced: `α, β ∈ ΦK` with `m • β = n • α`, `m ≠ 0`, give `β = α` or `β = -α`;
  7. `LiesInReflectionClosure aK νK ΦK`.

  Proof. Clauses 1–4 are the hypotheses `hpos`, `hgen`, `hsep` and `hν` rewritten with
  `latticePairing_baseChange`. Clause 5: write `χ = ψ c` with `c ∈ R'`. By
  `mem_closure_of_baseChange_mem_cone`, `c` or `-c` lies in the closure of `D`. Then `hclos`
  (applied to `-c ∈ R` in the second case, with `2 • (-c) = -(2 • c)` and `hneg`) gives
  `2 • c ∉ R`. Clause 6: write `α = ψ a`, `β = ψ b`, pull `m • β = n • α` back along the injective
  map `ψ`, and apply `hred`. Clause 7: given `P` over `K`, apply `hrefl` to `Q c := P (ψ c)`, using
  `characterLattice_baseChange_reflection` for the reflection step.

The conclusion of A3b is a conjunction stated with `let` bindings for `aK`, `νK`, `lamK` and `ΦK`.
`ΦK` unfolds to `ψ '' {c | c ∈ R ∧ 2 • c ∉ R}` by definition.

## Imports

`MaximalSplitGeneratedReductive` (it
provides `cone`, `IsIsolatingCocharacter` and `LiesInReflectionClosure` through its imports),
together with the published `Rational.NormalizerGaloisAction`,
`CentralIsogeny.CorootCompatibility` and `Torus.SplitLatticeBaseChange`.
