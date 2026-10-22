# The two irreducible constituents attached to a segment

Author: Worker 47. These proposition definitions state Zelevinsky's
existence and uniqueness results for the two distinguished irreducible
constituents of the representation induced from a segment of supercuspidal
representations of general linear groups over finite extensions of p-adic
fields. The first is Zelevinsky's `⟨Δ⟩` (Ze80 §3.1). The second is the
special representation `⟨Δ⟩^t` (Ze80 §9.1), which H02 §2.6 calls
`St_m(ρ)`. The module also states that the two constituents differ for
segments with at least two elements, and it states Zelevinsky's rank-one
example (Ze80 §3.2). The definitions assert no proofs and assume no theorem
as data. No constituent is chosen or constructed.

## Objects

Fix a prime `p`, an actual finite extension `F` of `ℚ_p` (`PadicField p`) and
a compatible topological realization `T : F.TopologicalData`. All other
objects come from the published module
`Langlands.Representation.Classification.Segments`.

- A segment `Δ : T.Segment` is recorded by its beginning `Δ.base = ρ` and its
  number of elements `m = Δ.length ≥ 1`. Here `ρ` is a `CuspidalDatum`, the
  isomorphism class of an irreducible supercuspidal representation of
  `GL_r(F)` with `r = Δ.rank ≥ 1`. The support of `Δ` is
  `{ρ, νρ, …, ν^(m-1) ρ}`, and `Δ.degree = m r`. This is Ze80 §3.1 (p.180):
  a segment is a subset `{ρ, νρ, …, ν^k ρ}` of the set `𝒞` of cuspidal
  classes, with `k = m - 1`.
- `ν^s` is `T.determinantPowerCharacter d s`, the real power of `|det|` on
  `GL_d(F)` for the normalized absolute value of `F` (`|ϖ| = q^(-1)`).
- For an actual supercuspidal representative `A` of `ρ`,
  `T.segmentInduced A.obj m _` is the increasing product
  `ρ × νρ × ⋯ × ν^(m-1) ρ`. `T.segmentInducedDown A.obj m _` is the
  decreasing product `ν^(m-1) ρ × ⋯ × νρ × ρ`. Both are upper normalized
  parabolic induction from the standard block upper triangular parabolic
  subgroup with `m` blocks of size `r`, as in Ze80 §1.8 and BZ77 §2.3. Their
  carriers lie in universe `max uF uV`.
- `Δ.base.IsRepresentedBy A` means that `A` has isomorphism class `ρ`.
- The relations `T.IsSegmentSubrepresentation Δ π`, `T.IsSegmentSocle Δ π`,
  `T.IsSegmentQuotient Δ π` and `T.IsSegmentHead Δ π` say that some actual
  representative `A` of `ρ` exists for which `π` is, respectively:
  - an irreducible subrepresentation of the increasing product, witnessed by
    an injective intertwiner;
  - the unique irreducible subobject of the increasing product: an
    irreducible subrepresentation such that every injective intertwiner from
    an irreducible representation has the same image;
  - an irreducible quotient of the increasing product, witnessed by a
    surjective intertwiner;
  - the unique irreducible quotient object of the increasing product: an
    irreducible quotient such that every surjective intertwiner onto an
    irreducible representation has the same kernel.

  The published lemmas `isSegmentSocle_iff`, `isSegmentHead_iff` and their
  analogues show that these relations do not depend on the representative.
- `IsIrreducibleHead` and `IsIrreducibleSocle` from `ConstituentRelations`
  give the same unique-quotient and unique-subobject conditions for an
  arbitrary representation. Here they are applied to the decreasing product
  of each representative.
- `HasScalarCharacter ρ (MonoidHom.id _) ω` means that `ρ(g)` is
  multiplication by the scalar `ω(g)` for every group element `g`.

Every candidate `π` is a smooth complex representation of
`GL_{mr}(F)` with carrier in universe `max uF uV`, the universe of the
induced representations. The uniqueness clauses in `IsIrreducibleHead` and
`IsIrreducibleSocle` quantify over irreducible representations with carriers
in this same universe.

## Declarations

- `SegmentZelevinskyConstituentExistence F T` (Ze80 §3.1, by
  Proposition 2.10). For every segment `Δ` there is a `π` with two
  properties. First, `π` is the unique irreducible subobject of
  `ρ × νρ × ⋯ × ν^(m-1) ρ`. Second, for every actual representative of `ρ`,
  `π` is the unique irreducible quotient object of
  `ν^(m-1) ρ × ⋯ × νρ × ρ`. Ze80 p.181: "`⟨Δ⟩` is the unique irreducible
  submodule of `ρ × νρ × … × ρ'` (or the unique irreducible quotient module
  of `ρ' × ν^(-1)ρ' × … × ρ`), see 2.10."
- `SegmentZelevinskyConstituentUniqueness F T` (Ze80 §3.1). Any two
  irreducible subrepresentations of the increasing product are isomorphic.
- `SegmentSpecialConstituentExistence F T` (Ze80 §9.1, by Proposition 2.10).
  For every segment `Δ` there is a `π` with two properties. First, `π` is
  the unique irreducible quotient object of `ρ × νρ × ⋯ × ν^(m-1) ρ`.
  Second, for every actual representative of `ρ`, `π` is the unique
  irreducible subobject of `ν^(m-1) ρ × ⋯ × νρ × ρ`. Ze80 p.197:
  "`⟨Δ⟩^t` is the unique irreducible submodule of
  `ρ' × ν^(-1)ρ' × … × ρ` (or the unique irreducible quotient of
  `ρ × νρ × … × ρ'`), see 2.10."
- `SegmentSpecialConstituentUniqueness F T` (Ze80 §9.1). Any two irreducible
  quotients of the increasing product are isomorphic.
- `SegmentConstituentsDistinct F T`. If `m ≥ 2`, no irreducible
  subrepresentation of the increasing product is isomorphic to an
  irreducible quotient of it. Together with the existence statements, this
  says that `⟨Δ⟩` and `⟨Δ⟩^t` are not isomorphic. The derivation is given
  below.
- `SegmentRankOneZelevinskyCharacter F T` (Ze80 Example 3.2). Suppose that
  `r = 1` and that the representative `A` of `ρ` acts by `χ ∘ det` for a
  homomorphism `χ : F^× → ℂ^×`. Then every irreducible subrepresentation of
  `χ × νχ × ⋯ × ν^(m-1) χ` acts on `GL_m(F)` by the character
  `ν^((m-1)/2) · (χ ∘ det)`. Ze80 p.181: "`ω(g) = ν^(k/2)(g) · ρ(det g)`"
  for `Δ = [ρ, ν^k ρ]`, so `k = m - 1`. The hypothesis on `A` is a
  hypothesis; the statement does not claim that every representation of
  `GL_1(F)` has this form. The coefficient on `GL_m(F)` is
  `T.determinantPowerCharacter Δ.degree ((m - 1) / 2)`, and
  `Δ.degree = m` when `r = 1`.
- `SegmentConstituentTheorems F T` is the conjunction of the six
  statements above for one field and one topological realization.
- `PadicSegmentConstituentTheorems` quantifies that conjunction over every
  prime `p`, every actual finite p-adic extension `F` and every compatible
  topological realization `T`. The universes `uF` (field) and `uV`
  (supercuspidal carriers) are arbitrary. Every rank `r ≥ 1` and every
  length `m ≥ 1` is covered, because both are fields of `Segment`.

## Conventions

The products are taken in increasing order, `ρ, νρ, …, ν^(m-1) ρ`, as in
`Segments`. In that order `⟨Δ⟩` is the unique irreducible
*subrepresentation* and `⟨Δ⟩^t` is the unique irreducible *quotient*.
H02 §2.6 (p.595) uses the second convention: `i(ρ, νρ, …, ν^(n-1) ρ)` "a un
unique quotient irréductible", whose class is `St_n(ρ)`, and cites Ze80 §9.3
for it. H02 §2.5 (pp.594–595) defines `i(π_1, …, π_r)` by normalized
parabolic induction from the upper block triangular parabolic subgroup with
diagonal blocks of sizes `n_1, …, n_r`. That is the same product as in Ze80
§1.8 and in `Segments`, so `St_m(ρ)` of H02 is `⟨Δ⟩^t` here.

The rank-one case is a check on the orientation. By Ze80 Example 3.2, the
irreducible subrepresentation of `χ × νχ × ⋯ × ν^(m-1) χ` is one-dimensional.
By Ze80 Example 9.2 (p.198), for `χ = ν^(-(m-1)/2)` the irreducible quotient
`⟨Δ⟩^t` is the Steinberg representation. Exchanging subrepresentation and
quotient would break both checks. Example 9.2 is used here only as a check
and is not formalized.

## How the statements are encoded

**Uniqueness as subobject or quotient object.** Ze80 asserts more than
uniqueness of an isomorphism class: the increasing product has exactly one
irreducible submodule, and the decreasing product exactly one irreducible
quotient module. The existence statements keep this by using
`IsIrreducibleSocle` (equal images of all irreducible embeddings) and
`IsIrreducibleHead` (equal kernels of all irreducible quotient maps).

**Representatives.** For the increasing product the statements use the
published relations `IsSegmentSocle` and `IsSegmentHead`, which quantify
existentially over representatives of `ρ`. By `isSegmentSocle_iff` and
`isSegmentHead_iff`, this is the same as requiring the property for every
representative. No published relation exists for the decreasing product, so
the second clause quantifies over every actual representative `A` with
`Δ.base.IsRepresentedBy A`.

**Isomorphism-class uniqueness.** The two uniqueness statements are
separate conjuncts, in the form usually quoted. They follow from the
corresponding existence statements. For example, if `π₀` is the unique
irreducible subobject and `π, π'` are irreducible subrepresentations, then
`π` and `π'` embed with the same image as `π₀`, so both are isomorphic to
`π₀`. This works because the uniqueness clause of `IsIrreducibleSocle`
ranges over all carriers in universe `max uF uV`. The deduction is recorded
here as provenance; it is not a Lean proof.

**Irreducibility.** Each relation includes `Representation.IsIrreducible`
of the candidate `π`. This means the lattice of invariant subspaces is
simple, which includes nonzeroness. No admissibility or finite-dimensionality
is assumed of `π`.

## Derivation of distinctness

Ze80 §2 (pp.176–180) studies a product `π(λ) = λ(1) × ⋯ × λ(r)` of an
ordering `λ` of a finite set `R` of cuspidal classes. For a segment, `R`
consists of the `m` distinct classes `ρ, νρ, …, ν^(m-1) ρ`. They are distinct
because twisting by `ν^i` with `i ≠ 0` changes the central character.

Ze80 §2.2 (p.177) forms the graph `Γ` on `R` whose edges join `ρ_1` and
`ρ_2` when `ρ_2 = νρ_1` or `ρ_1 = νρ_2`. Theorem 2.2 gives a bijection
`Γ' ↦ ω(Γ')` from orientations of `Γ` onto the set of irreducible
constituents of `π(λ)`, which by §2.1 does not depend on `λ`. Proposition
2.10 (p.180) states that `π(λ)` has the unique irreducible submodule
`ω(Γ(λ))` and the unique irreducible quotient `ω(Γ(λ)^-)`. Here `Γ(λ)`
orients each edge from the earlier to the later element of `λ`, and
`Γ(λ)^-` reverses every edge.

For a segment with `m ≥ 2`, the graph has the edges `{ν^i ρ, ν^(i+1) ρ}`
for `0 ≤ i < m - 1`, so it has at least one edge. The increasing ordering
gives the orientation `ρ → νρ → ⋯ → ν^(m-1) ρ` for the submodule `⟨Δ⟩` and
the reversed orientation for the quotient `⟨Δ⟩^t` (Ze80 §§3.1, 9.1). These
orientations differ, so by the bijection of Theorem 2.2 the two constituents
are not isomorphic. For `m = 1` the graph has no edges and
`⟨Δ⟩ = ⟨Δ⟩^t = ρ` (Ze80 §3.1), so the hypothesis `2 ≤ Δ.length` is needed.

A second route uses Jacquet modules. By Ze80 §3.1 and §9.1(*), the Jacquet
module of `⟨Δ⟩` along the partition `(r, …, r)` is
`ρ ⊗ νρ ⊗ ⋯ ⊗ ν^(m-1) ρ`, and that of `⟨Δ⟩^t` is
`ν^(m-1) ρ ⊗ ⋯ ⊗ νρ ⊗ ρ`. For `m ≥ 2` the first tensor factors `ρ` and
`ν^(m-1) ρ` differ, so the two Jacquet modules are not isomorphic.

Both derivations are recorded as provenance; neither is a Lean proof.

## Original sources

- Zelevinsky, *Induced representations of reductive p-adic groups II.
  Irreducible representations of GL(n)*, Ann. Sci. ENS (4) 13 (1980). The
  relevant passages are:
  - §§2.1–2.2, pp.176–177 (PDF pp.13–14), with Theorem 2.2;
  - Proposition 2.10, p.180 (PDF p.17);
  - §3.1 and Example 3.2, pp.180–181 (PDF pp.17–18);
  - §9.1 and Example 9.2, pp.197–198 (PDF pp.34–35).

  Literature ID `zelevinsky-1980-induced-ii`, PDF SHA-256
  `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`. PDF
  page = printed page − 163.
- Henniart, *Une caractérisation de la correspondance de Langlands locale
  pour GL(n)*, Bull. Soc. Math. France 130 (2002). §2.5, pp.594–595
  (PDF pp.8–9), and §2.6, p.595 (PDF p.9), are cited only for the induction
  and special-representation conventions. Literature ID
  `henniart-2002-characterization`, PDF SHA-256
  `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.

## Remaining proof obligations

- Ze80 proves Theorem 2.2 and Proposition 2.10 in §§2.3–2.10 (pp.177–180).
  The proof describes the lattice of submodules of the multiplicity-free
  representation `π(λ)`. It uses the multiplicity-one statement §2.1, which
  rests on BZ77 2.13(c) (or Ze80 1.6), and the commutativity of composition
  factors (Ze80 Theorem 1.9). Through §§2.2 and 2.8 it also uses the
  two-element case, Ze80 Proposition 1.11 (p.175). For the reducibility of
  `ρ × νρ`, §1.11 gives only a sketch. That gap is recorded in
  `SupercuspidalProductStatement`, and it is a proof-source obligation here
  as well.
- For Example 3.2, Ze80 only remarks that the easiest check is to compute the
  Jacquet module `r_{(1, …, 1), (k+1)}(ω)` directly from the definition
  (citing BZ77 §1.8). No further proof is written.

None of these arguments is formalized here. Compiling the proposition
definitions establishes none of the statements.
