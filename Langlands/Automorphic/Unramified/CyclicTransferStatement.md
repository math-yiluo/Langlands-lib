# Arthur–Clozel cyclic base change and automorphic induction for cuspidal classes

Source: J. Arthur and L. Clozel, *Simple Algebras, Base Change, and the Advanced
Theory of the Trace Formula*, Annals of Mathematics Studies 120 (1989), Chapter III
(literature `arthur-clozel-1989-base-change`; PDF page = printed page + 14):

- Definition 1.1 (p.199): weak base change, `t_{π,v}^{f_v} = t_{Π,w}` for almost all
  `v` and `w | v`;
- (2.4) (p.200): Jacquet–Shalika, Euler Products II, Theorem 4.4. If two
  representations induced from cuspidal data have the same Hecke matrices at
  almost all places, their cuspidal data are conjugate;
- Definition 4.1 and Theorem 4.2 (a), (b), (d), (e) (pp.202–203);
- Definition 6.1, Theorem 6.2 and Lemmas 6.3, 6.4 (pp.215–217).

This file states the clauses of these results that concern cuspidal
representations only. The objects are the project's actual ones:

- `CuspidalOperatorRealization F r`: an irreducible cuspidal automorphic
  realization of `GL_{r+1}(𝔸_F)`;
- `IsoClass F r`: such realizations up to full equivalence;
- `IsoClass.IsWeakBaseChangeOf` and `IsoClass.IsWeakInductionOf` (module
  `Automorphic.Unramified.WeakTransfer`): weak base change and weak induction
  of classes, witnessed by spectral systems attached through actual local
  components;
- `IsoClass.IsFiniteOrderDeterminantTwist χ c d`: `d ≅ c ⊗ (χ ∘ det)` for a
  finite-order Hecke character `χ`;
- `IsoClass.IsGaloisConjugate` and `IsoClass.IsGaloisStable` (module
  `Automorphic.ArithmeticTransportRelation`).

## Common hypotheses and conventions

- `F` and `E` are number fields in independent universes `uF` and `uE`, with
  `[Algebra F E]` and `[IsGalois F E]`. The source's "cyclic of prime degree"
  is `IsGalois` with `Module.finrank F E` prime. A group of prime order is
  cyclic. For Lemmas 6.3 and 6.4 of arbitrary degree `ℓ = Module.finrank F E`,
  cyclicity is a generator `σ : E ≃ₐ[F] E`: every automorphism lies in
  `Subgroup.zpowers σ`.
- `[CompactSpace (AdeleQuotient F)]` and `[CompactSpace (AdeleQuotient E)]` are
  the explicit compactness parameters of the published cuspidal classes. They
  hold for every number field.
- `η.HasNormKernel E`, defined here in namespace `Langlands.Global.HeckeCharacter`,
  says that the Hecke character `η` of `F` equals `1` exactly on the image of the
  idele-class norm `AdelicFunctoriality.ideleClassNorm` from `E`. This is the
  source's "character `η` of `𝔸^×` vanishing exactly on `F^× N(𝔸_E^×)`" (p.202),
  on idele classes. In Lemma 6.3 the source calls it a "generating character"
  of `F^× N 𝔸_E^× \ 𝔸_F^×`. The two agree because the quotient is cyclic. The
  lemmas `HasNormKernel.isTrivialOnNorm` and `HasNormKernel.hasFiniteOrder` are
  proved. The second supplies the finite-order condition of the twist relation.
- The source works with representations "induced from cuspidal" (Definition
  4.1), which requires *unitary* cuspidal data. Here unitarity of each
  cuspidal input is `RelativeWeilGroup.HasUnitaryCentralCharacter`: its central
  character is unitary. For a cuspidal representation this is equivalent to
  unitarity.
- The rank of `IsoClass F r` is `r + 1`. So the source's `GL(n)` with
  `n = ℓ m` appears as `r + 1 = ℓ (m + 1)`.
- Galois conjugacy follows `ArithmeticTransportRelation`:
  `IsGaloisConjugate σ c d` means `d ≅ c ∘ σ⁻¹`. Every use below quantifies
  over all `σ`, or over the powers `σ^i` with `0 < i < ℓ`, a set closed under
  inverses. So it agrees with the source's `Π^σ = Π ∘ σ`.
- The universes `uV` and `uW` are those of the local-component carriers in the
  spectral presentations that witness the weak relations over `F` and `E`.

## The statements

**`CyclicPrimeCuspidalLiftStatement` (Theorem 4.2(a)).** `E/F` is cyclic of prime
degree. `S` is unitary cuspidal over `F` and `π ≇ π ⊗ η`, that is,
`¬ IsFiniteOrderDeterminantTwist η π π`. Then there is a cuspidal class `d` over
`E` of the same rank such that:

- `d` is a weak base change of `π`;
- `d` is stable under every `σ ∈ Gal(E/F)`;
- every cuspidal weak base change `d'` of `π` equals `d`.

The source says that there is a unique `σ`-stable representation induced from
cuspidal lifting `π`, and that it is cuspidal. Here uniqueness is stated only
among cuspidal classes. Among them every weak base change is automatically
`σ`-stable: it has the same almost-everywhere Hecke matrices as its conjugate,
so (2.4) applies. Hence the restricted uniqueness is a consequence of the source.

**`CyclicPrimeSelfTwistStatement` (Theorem 4.2(b), through cuspidal data).**
`E/F` is cyclic of prime degree `ℓ`. `S` is unitary cuspidal over `F` with
`π ≅ π ⊗ η`. Then:

1. no cuspidal class over `E` is a weak base change of `π`;
2. there are `m` and a cuspidal class `d₁` of rank `m + 1` over `E` with
   `r + 1 = ℓ (m + 1)`;
3. `d₁` is not stable under any `σ ≠ 1`;
4. `π` is weakly automorphically induced from `d₁`;
5. every cuspidal `d₁'` of rank `m + 1` from which `π` is weakly induced is a
   Galois conjugate of `d₁`.

The source states this through the induced representation
`Π = Π₁ × Π₁^σ × ⋯ × Π₁^{σ^{ℓ-1}}`, the only lift of `π`, with `Π₁ ≇ Π₁^σ`.
Products of representations induced from proper parabolic subgroups are not
yet available in the Library (Task 8 owns isobaric realizations). This
statement records the cuspidal data instead. Its derivation from the source:

- (1): a cuspidal lift would be a lift induced from cuspidal, so (2.4) would
  make it conjugate to the properly induced `Π`. This is impossible for
  `ℓ > 1`.
- (3): in prime degree, every `σ ≠ 1` generates `Gal(E/F)`, so `Π₁ ≇ Π₁^σ` for
  one generator gives it for all nontrivial `σ`.
- (4): `Π` lifts `π`, and `π ≅ π ⊗ η` holds. At split places this is (6.1) of
  §6. At an inert place `η_v` has order `ℓ`, so the Hecke matrix of `π_v` is
  stable under multiplication by a primitive `ℓ`-th root of unity `ζ`. With
  `t_{π,v}^ℓ` equal to the Hecke matrix of `Π_w` (ℓ copies of `t_{Π₁,w}`), this
  forces `t_{π,v} = t_{Π₁,w}^{1/ℓ} ⊕ ζ t_{Π₁,w}^{1/ℓ} ⊕ ⋯`, which is (6.2). The
  computation is the one in the proof of Theorem 6.2, pp.216–217.
- (5): if `π` is weakly induced from `d₁'`, then
  `d₁' × d₁'^σ × ⋯ × d₁'^{σ^{ℓ-1}}` lifts `π`, by the same local computation.
  By (2.4) its cuspidal data are conjugate to those of `Π`.

**`CyclicStableDescentStatement` (Lemma 6.3; Theorem 4.2(d) in prime degree).**
`E/F` is cyclic of degree `ℓ` with generator `σ`. `T` is unitary cuspidal over
`E` and `σ`-stable. Then there is a cuspidal class `c` over `F` with:

- `T` a weak base change of `c`;
- for each `i < ℓ`, a twist of `c` by `η^i`;
- the cuspidal classes of which `T` is a weak base change are exactly these
  twists;
- twists by different exponents `i ≠ j < ℓ` are different classes.

These are the source's "exactly `ℓ` representations `π_F, π_F ⊗ η, …,
π_F ⊗ η^{ℓ-1}` lifted by `π_E`; `π_F` is cuspidal". The source prints
`π_F = π_F ⊗ η_{E/F}` at the end of Lemma 6.3 (p.217). This is a misprint: the
proof shows the `ℓ` twists are distinct, and Theorem 4.2(d) (p.202) states
`π ≇ π ⊗ η`. The Lean records distinctness. The source's count also excludes
noncuspidal representations induced from cuspidal lifted by `π_E`. Here the
characterization is stated among cuspidal classes only.

**`CyclicRegularInductionStatement` (Lemma 6.4 with Theorem 6.2; Theorem 4.2(e)
in prime degree).** `E/F` is cyclic of degree `ℓ` with generator `σ`. `T` is
unitary cuspidal over `E` of rank `m + 1`, and `π_E ≇ π_E^{σ^i}` for
`0 < i < ℓ`. Then there is a cuspidal class `c` over `F` of rank `(m + 1) ℓ` such
that:

- `c` is weakly automorphically induced from `T`;
- `c ≅ c ⊗ η`;
- every cuspidal class of that rank weakly induced from `T` equals `c`.

Lemma 6.4 gives a unique representation `π_F` lifted by
`π_E × π_E^σ × ⋯ × π_E^{σ^{ℓ-1}}`, cuspidal with `π_F ≅ π_F ⊗ η`. Theorem 6.2
gives one and only one representation automorphically induced from `π_E`
(Definition 6.1), induced from cuspidal. That representation is lifted by the
same product, so it is the `π_F` of Lemma 6.4. Hence `π_F` is cuspidal and
weakly induced from `π_E`. Uniqueness among cuspidal classes is the uniqueness
of Theorem 6.2. The printed target rank `n` in Theorem 6.2 is a slip for `nℓ`,
as Definition 6.1 and the proof show. The rank equation displayed here repeats
`IsWeakInductionOf.rank_eq` for readability.

Definition 6.1's association is the induced representation of the local Weil
groups at almost all places. The published numerical relation
`SpectralSystem.IsArithmeticWeakInductionOf` encodes it as the identity of
Euler polynomials `det(1 - t_{π,v} X) = ∏_{w|v} det(1 - t_{π_E,w} X^{f_w})` at
almost all unramified `v`. This is the characteristic polynomial of the
induced Frobenius.

**`CyclicTransferStatement`** is the conjunction of the four statements, with
universe parameters `uF uE uV uW`.

## Scope and source gaps

- Not stated:
  - Theorem 4.2(c) and (f) (existence and descent for representations induced
    from cuspidal);
  - the noncuspidal parts of (a), (b), (d) and (e);
  - Theorem 6.2 for noncuspidal `π_E`;
  - Theorem 6.2's general statement for `π_E` stable under a proper power of `σ`.

  They need realized products of representations induced from cuspidal data
  (AC89 Definition 4.1). These belong to the global definition branch (Task 8)
  and are not yet published.
- Every arithmetic input is a hypothesis or part of a conclusion: weak lifts
  and inductions, twists, Galois stability. In particular, the existence of the
  attached spectral systems (local components of cuspidal classes) is part of
  the conclusions `IsWeakBaseChangeOf` and `IsWeakInductionOf`, as in their
  published definitions. The existence of an `η` with `HasNormKernel` (global
  class field theory) is not assumed; `η` is a hypothesis.
- Strong base change (Definition 1.2) and archimedean components are not
  involved.
- These are proposition definitions. No proof is claimed. Proofs are separate
  obligations.
