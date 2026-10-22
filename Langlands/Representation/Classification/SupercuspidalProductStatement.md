# Irreducibility of normalized products of supercuspidal representations

Author: Worker 47. These proposition definitions state the irreducibility
criterion of Bernstein and Zelevinsky (1977), Theorem 4.2, for actual general
linear groups over finite extensions of p-adic fields. They also state its
converse, which is announced in BZ77 Remark 4.2(2) and proved as the
length-one case of Zelevinsky (1980), Theorem 4.2. The definitions assert no
proofs and assume no theorem as data.

## Objects

Fix a prime `p`, an actual finite extension `F` of `ℚ_p` (`PadicField p`), a
compatible topological realization `T : F.TopologicalData`, and a rank `n`.

- A block shape `B : BlockShape n` is an ordered partition
  `n = n_1 + ⋯ + n_r` into positive block sizes `B.size i`, with
  `r = B.length`. It is BZ77's partition `P = (n_1, …, n_r)` of §4.1.
- Each block is an actual object `A i : SupercuspidalRep` of rank
  `B.size i`, with complex carrier in universe `uV`. A `SupercuspidalRep` is a
  smooth complex representation that is irreducible and satisfies
  `IsSupercuspidal`. That predicate means admissible, with zero Jacquet
  coinvariants for every proper standard block unipotent radical and every
  conjugate of it. This is BZ77 §2.4 (p.446): an admissible quasicuspidal
  representation is *cuspidal*. Vanishing for the standard radicals already
  forces vanishing for their conjugates. Hence an irreducible `ρ_i` here is
  exactly an element of BZ77's `Irr G_{n_i}` that is cuspidal.
- The product `ρ_1 × ⋯ × ρ_r` is
  `(T.normalizedProductInductionFunctor B).obj (fun i => (A i).obj)`. By the
  published lemma `normalizedProductInductionFunctor_obj`, which holds by
  `rfl`, its representation is `T.normalizedProductInduced B` of the blocks.
  That is upper normalized parabolic induction with right translation and
  covariance `f(pg) = δ_P(m)^(1/2) (ρ_1(m_1) ⊗ ⋯ ⊗ ρ_r(m_r)) f(g)`. This is
  BZ77 §4.1 with the conventions of §1.8(a) and §§2.2–2.3. Its carrier lies
  in universe `max uF uV`.
- Irreducibility is `SmoothRep.IsIrreducible`, meaning that the lattice of
  invariant subspaces is simple. This includes nonzeroness. No
  finite-dimensionality is required.

## The relation `ρ_j ≅ ν ρ_i`

BZ77 §4.2 defines `ν(g) = |det g|` with the standard (normalized) absolute
value of `F`. Here `ν^s` on `GL_d(F)` is the published
`T.determinantPowerCharacter d s`, the real power of `T.determinantNorm d`
with the residue-normalized absolute value, so `|ϖ| = q^(-1)`. The published
class map `T.supercuspidalClassRealPowerTwist d 1` sends the isomorphism class
of `ρ` to that of `ρ ⊗ ν`.

The blocks `ρ_i` and `ρ_j` may have different ranks. The relation is therefore
stated as an equality in the sigma type
`Σ d : ℕ, SupercuspidalClass (n := d)` of rank-indexed isomorphism classes:

`⟨B.size j, [ρ_j]⟩ = ⟨B.size i, [ν ρ_i]⟩`.

Equality of the first components is equality of ranks. Given that, equality
of the second components is the existence of an actual isomorphism
`ρ_j ≅ ρ_i ⊗ ν` (`SupercuspidalRep.isoClass_eq_iff`). Different ranks are
never related. This matches BZ77 Remark 4.2(1), which notes that
`ρ_j ≅ νρ_i` forces `n_j = n_i`. No cast of a representation between ranks is
needed.

## Declarations

- `SupercuspidalProductIrreducibilityCriterion F T n` (BZ77 Theorem 4.2).
  For every block shape `B` of `n` and every family of irreducible
  supercuspidal blocks, suppose that for all indices `i, j` the class of
  `ρ_j` differs from the class of `ν ρ_i`. Then the normalized product is
  irreducible. Both indices range over all of `Fin B.length`, as in the
  source's "for any i, j". This covers both `ρ_j ≅ νρ_i` and `ρ_i ≅ νρ_j`.
  The diagonal case `i = j` adds no restriction: BZ77 Remark 4.2(1) observes
  that `ρ ≇ νρ`, since the two differ on the center. The Lean statement keeps
  the source's unrestricted quantifier rather than excluding `i = j`.
- `SupercuspidalProductReducibilityTheorem F T n`, the converse. If
  `ρ_j ≅ ν ρ_i` for some indices `i, j`, the normalized product is not
  irreducible. BZ77 Remark 4.2(2) announces this and defers the proof to
  Part II.
- `PadicSupercuspidalProductIrreducibilityTheorems` is the conjunction of
  both over every prime `p`, every actual finite p-adic extension `F`, every
  compatible topological realization `T` and every positive rank `n`. The
  universes `uF` (field) and `uV` (block carriers) are arbitrary.

Together the two give the "if and only if" form of the criterion for products
of cuspidal representations of GL_n.

## Derivation of the converse from Ze80 Theorem 4.2

Ze80 §3.1 (pp.180–181) defines segments `[ρ, ν^k ρ]` of cuspidal classes and
the irreducible representation `⟨Δ⟩`. It notes that `⟨[ρ, ρ]⟩ = ρ`. Ze80 §4.1
(p.184) calls segments `Δ_1, Δ_2` *linked* when neither contains the other and
their union is a segment. Ze80 Theorem 4.2 (p.184) states that
`⟨Δ_1⟩ × ⋯ × ⟨Δ_r⟩` is irreducible if and only if no two `Δ_i, Δ_j` are linked.

For singletons `Δ_i = [ρ_i, ρ_i]`, neither containing the other means
`ρ_i ≠ ρ_j` as classes. The union `{ρ_i, ρ_j}` is then a segment exactly when
`ρ_j = ν ρ_i` or `ρ_i = ν ρ_j`. So "some pair is linked" is equivalent to "for
some `i, j`, `ρ_j ≅ ν ρ_i`", where the case `ρ_i = ρ_j` is excluded because
`ρ ≇ νρ`. Ze80's product is defined in §1.8 (p.174) as
`ρ_1 × ⋯ × ρ_r = i_{(n),(n_1,…,n_r)}(ρ_1 ⊗ ⋯ ⊗ ρ_r)`, using the induction
functors of BZ77 §2.3 (Ze80 §1.1). It is therefore the same normalized product
as in BZ77 §4.1. This is how the converse is derived. The derivation is
recorded here as provenance; it is not a Lean proof.

For two factors, Ze80 Proposition 1.11 (p.175) is the same criterion:
`ρ × ρ'` is irreducible when `ρ' ≇ νρ` and `ρ ≇ νρ'`, and it has length two
otherwise.

## Original sources

- Bernstein and Zelevinsky, *Induced representations of reductive p-adic
  groups I*, Ann. Sci. ENS (4) 10 (1977). The relevant passages are §2.4,
  p.446 (PDF p.7), which defines cuspidal representations, and §§4.1–4.2,
  p.454 (PDF p.15), which give the product, `ν`, Theorem 4.2 and
  Remarks (1)–(2). The literature index places Theorem 4.2 on p.453; it is
  actually on p.454. Literature ID: `bernstein-zelevinsky-1977-induced-i`,
  PDF SHA-256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
- Zelevinsky, *Induced representations of reductive p-adic groups II*,
  Ann. Sci. ENS (4) 13 (1980). The relevant passages are §1.1, p.170
  (PDF p.7); §§1.8–1.11, pp.174–175 (PDF pp.11–12); §3.1, pp.180–181
  (PDF pp.17–18); and §§4.1–4.6, pp.184–185 (PDF pp.21–22). Literature ID:
  `zelevinsky-1980-induced-ii`, PDF SHA-256
  `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.

## Remaining proof obligations

- BZ77 proves Theorem 4.2 in §§4.3–4.8 (pp.454–456) by restricting to the
  mirabolic subgroup. The proof uses derivatives and Lemma 4.7, and relies on
  the Gelfand–Kazhdan description of derivatives of cuspidal representations
  (§4.4). BZ77 cites that description from its reference [1], chapter III.
- Ze80 proves the direction "not linked ⇒ irreducible" through Proposition 4.3
  (§§4.3–4.5, pp.184–185). For the converse, Ze80 §4.6 (p.185) reduces to
  the reducibility of `⟨Δ⟩ × ⟨Δ'⟩` for a linked pair. For juxtaposed segments
  it uses §2, which starts from Proposition 1.11. Ze80 §1.11 (p.175) gives
  only a sketch of the basic reducibility of `ρ × νρ`, which is BZ77's
  announced Remark 4.2(2). The sketch uses an analytic family of Hermitian
  forms and an unbounded matrix coefficient. A complete written proof of that
  step is a remaining proof-source obligation.
- Passing from a reducible linked pair to the reducibility of the full
  product uses the commutativity of the product on composition factors
  (Ze80 Theorem 1.9) and exactness of induction (Ze80 §1.1(a)).

None of these arguments is formalized here. Compiling the proposition
definitions establishes neither direction.
