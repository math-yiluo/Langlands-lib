# The product of two supercuspidal representations

Author: Worker 745. These proposition definitions state Zelevinsky (1980),
Proposition 1.11, for actual general linear groups over finite extensions of
p-adic fields. They cover the irreducibility of `ρ × ρ'` in the non-adjacent
case. In the adjacent case they cover length two, the unique proper
submodule `ω`, the irreducibility of `ω` and of `ω' = (ρ × ρ') / ω`, and the
normalized `(k, k)` Jacquet modules of `ω` and `ω'`. The definitions assert no
proofs and assume no theorem as data. Compiling them proves nothing about
Proposition 1.11.

## The source statement

Ze80 §1.11 (printed p.175, PDF p.12) fixes `ν(g) = |det g|` on `G_n`, where
`| |` is the standard norm of `F`, and states:

> PROPOSITION. — Let `ρ ∈ Irr G_k`, `ρ' ∈ Irr G_l` be cuspidal:
>
> (a) If `ρ' ≄ νρ` and `ρ ≄ νρ'` (in particular if `k ≠ l`) then `ρ × ρ'` is
> irreducible.
>
> (b) Suppose that `k = l` and either `ρ' ≃ νρ` or `ρ ≃ νρ'`. Then the
> representation `ρ × ρ'` has length 2. It has a unique proper submodule `ω`;
> the quotient `ω' = (ρ × ρ')/ω` is irreducible and one has
> `r_{(k,k),(2k)}(ω) = ρ ⊗ ρ'`, `r_{(k,k),(2k)}(ω') = ρ' ⊗ ρ`.

No errata note for Ze80 was found in the Library or the literature index.

## Objects

Fix a prime `p`, an actual finite extension `F` of `ℚ_p` (`PadicField.{uF} p`),
and a compatible topological realization `T : F.TopologicalData`. All
declarations take `F` and `T` as explicit parameters and are
universe-polymorphic in `uF` and `uV`.

- **Cuspidal factors.** `ρ` and `ρ'` are actual objects of
  `SupercuspidalRep.{uF, uV}` of ranks `k` and `l`, with complex carriers in
  universe `uV`. A `SupercuspidalRep` is a smooth complex representation that
  is irreducible and satisfies `IsSupercuspidal`. That predicate means
  admissible with zero Jacquet coinvariants for every proper standard block
  unipotent radical and each of its conjugates. This is Ze80 §1.10 (p.174):
  admissible and quasicuspidal, with irreducibility imposed separately. The
  conjugate radicals add no condition, since `ρ(g)` identifies the
  coinvariants for `U` with those for `gUg⁻¹`. So
  `ρ` is exactly an element of Ze80's `Irr G_k` that is cuspidal. The ranks are
  positive (`0 < k`, `0 < l`), as for Ze80's set `𝒞` of cuspidal classes of
  `G_n`, `n = 1, 2, …` (§1.10). Positivity is also needed because block sizes
  of a `BlockShape` are positive.
- **The twist `ν`.** Ze80 §1.11 defines `ν(g) = |det g|` with the standard
  norm of `F`. The published class map `T.supercuspidalClassRealPowerTwist d 1`
  sends the isomorphism class of `ρ` to that of `ρ ⊗ ν`. Its character is
  `T.determinantPowerCharacter d 1`, the power `g ↦ |det g|` with the
  residue-normalized absolute value, so `|ϖ| = q^(-1)`.
- **The block shape.** `Shahidi.twoBlocks k l hk hl` is the published
  ordered block shape of `k + l` with sizes `![k, l]`. Block `0` is the
  upper-left `GL_k` on the first `k` coordinates and block `1` is the
  lower-right `GL_l` (`twoBlocks_index_first`, `twoBlocks_index_second`). This
  is Ze80's partition `(k, l)` of §1.1 (p.170), whose blocks are
  `I_1 = {1, …, k}` and `I_2 = {k + 1, …, k + l}`. Its Levi
  `(twoBlocks k l hk hl).Levi F` is by definition the product group
  `∀ i : Fin 2, GL_{![k, l] i}(F)`, which is Ze80's `G_{(k,l)} = G_k × G_l`.
- **The product `ρ × ρ'`.** It is
  `(T.normalizedProductInductionFunctor (twoBlocks k l hk hl)).obj
  (twoBlockFactors hk hl ρ.obj ρ'.obj)`. Ze80 §1.8 (p.174) defines
  `ρ_1 × ⋯ × ρ_r = i_{(n),(n_1,…,n_r)}(ρ_1 ⊗ ⋯ ⊗ ρ_r)`, and §1.1 (p.170) takes
  `i_{(n),α}` to be the normalized induction functor `i_{G_n, G_α}` of BZ77 §2.3
  for the standard parabolic with Levi `G_α`. The published functor is upper
  block parabolic induction with right translation, normalized by `δ_P^(1/2)`
  (`T.leviHalfCharacter`); its representation is
  `T.normalizedProductInduced` of the block factors
  (`normalizedProductInductionFunctor_obj`, by `rfl`). The factor in block `0`
  is `ρ` and the factor in block `1` is `ρ'`, which is Ze80's order in
  `ρ ⊗ ρ'`. The carrier of the product lies in universe `max uF uV`.
- **Irreducibility.** `SmoothRep.IsIrreducible` means that the lattice of
  invariant subspaces is simple, which includes nonzeroness.
- **Length.** `HasCompositionSeriesLength P.obj 2` asserts the existence of an
  actual chain `0 = P_0 ⊆ P_1 ⊆ P_2 = P` of invariant subspaces whose two
  graded quotients are irreducible. This is Ze80's "has length 2". The
  Jordan–Hölder theorem, which makes the length independent of the series, is
  not part of the statement.
- **Submodules and quotient.** A submodule of `P` is an invariant subspace,
  `S : Subrepresentation P.representation`. The published
  `SmoothRep.subrepresentation P S` is the smooth representation on `S`, and
  `SmoothRep.quotient P S` is the smooth representation on the actual quotient
  module `P / S`. No abstract subobject or quotient object is chosen.
- **Jacquet modules.** `T.normalizedJacquetFunctor B` sends a smooth
  representation of `GL_n(F)` to its normalized Jacquet module along the
  standard upper block parabolic of `B`. This is the actual coinvariant quotient
  by the unipotent radical, with the Levi acting through its section into the
  parabolic and normalized by `δ_P^(-1/2)` (the inverse square root of
  `T.leviModulus B`). This is Ze80's `r_{α,(n)} = r_{G_α, G_n}` of §1.1, the
  normalized functor of BZ77 §2.3, here with `α = (k, k)` and `n = 2k`.
- **External tensor products.** `FiniteTensor.externalSmoothObject A` is the
  actual external tensor product `⨂_i A_i` of a finite family of smooth
  representations, as a representation of the product group `∀ i, H_i`. For
  the family `twoBlockFactors hk hk ρ.obj ρ'.obj`, the group is
  `∀ i : Fin 2, GL_{![k, k] i}(F)`, which is literally the Levi
  `(twoBlocks k k hk hk).Levi F`. The first factor `GL_k` acts on the first
  tensor factor. So this object is Ze80's `ρ ⊗ ρ' ∈ Irr G_{(k,k)}`, and
  `twoBlockFactors hk hk ρ'.obj ρ.obj` gives `ρ' ⊗ ρ`.

## Helper definition

`twoBlockFactors hk hl A₀ A₁` is the ordered pair family `(A₀, A₁)` of bundled
smooth representations indexed by the blocks of `twoBlocks k l hk hl`. It is
`Fin.cases A₀ (Fin.cases A₁ finZeroElim)`. It is an internal derived
definition with no counterpart in the source, which writes the pair as
`ρ ⊗ ρ'`. It is the bundled-`SmoothRep` analogue of the published
unbundled `Shahidi.pairFamily` and of the three-block family
`Parabolic.threeBlockSmoothFamily`. Neither published helper takes a pair of
`SmoothRep` objects indexed by `twoBlocks`, which the induction functor and
`externalSmoothObject` require. The field is any commutative topological ring,
so the helper also serves other two-block products.

## Declarations

### `TwoSupercuspidalNonadjacentProductIrreducible F T` (part (a))

For all positive ranks `k, l` and all `ρ : SupercuspidalRep (n := k)`,
`ρ' : SupercuspidalRep (n := l)`:

- if `⟨l, [ρ']⟩ ≠ ⟨k, [νρ]⟩` and
- `⟨k, [ρ]⟩ ≠ ⟨l, [νρ']⟩`

in the sigma type `Σ d : ℕ, SupercuspidalClass (n := d)` of rank-indexed
isomorphism classes, then the product `ρ × ρ'` is irreducible.

The two hypotheses are Ze80's `ρ' ≄ νρ` and `ρ ≄ νρ'`, in this order. Equality
in the sigma type is equality of ranks together with equality of classes. By
`SupercuspidalRep.isoClass_eq_iff`, the latter is the existence of an actual
isomorphism. Different ranks are never related, so no representation is cast
between ranks. When `k ≠ l` both hypotheses hold automatically, which is the
source's "in particular if `k ≠ l`". This is the same encoding as the published
`SupercuspidalProductIrreducibilityCriterion`. The hypotheses are only the two
cross relations of the source. The relations `ρ ≅ νρ` and `ρ' ≅ νρ'` are not
hypotheses here; by BZ77 Remark 4.2(1) they never hold, since the two sides
differ on the center.

### `TwoSupercuspidalAdjacentProductComposition F T` (part (b), structure)

For every positive rank `k` and all `ρ, ρ' : SupercuspidalRep (n := k)` with
`[ρ'] = [νρ]` or `[ρ] = [νρ']` as rank-`k` classes, let `P` be the product
`ρ × ρ'` along `twoBlocks k k hk hk`. Then:

1. `HasCompositionSeriesLength P.obj 2`: the product has length two.
2. `∃! S : Subrepresentation P.representation, S ≠ ⊥ ∧ S ≠ ⊤`: there is
   exactly one invariant subspace other than zero and the whole space.
3. For every invariant subspace `S` with `S ≠ ⊥` and `S ≠ ⊤`, both
   `SmoothRep.subrepresentation P S` and `SmoothRep.quotient P S` are
   irreducible.

Ze80's hypothesis `k = l` is built in by taking one rank `k` for both factors,
so the twist relations are ordinary equalities of classes in
`SupercuspidalClass (n := k)`. Ze80 writes "a unique proper submodule `ω`"
for the unique nonzero proper submodule. Item 2 states this uniqueness as an
invariant subspace (an element of the lattice `Subrepresentation`), not up to
isomorphism. It excludes both `⊥` (zero) and `⊤` (the whole space). By item 2,
the `S` of item 3 is `ω`, and item 3 then says that `ω` and
`ω' = (ρ × ρ') / ω` are irreducible. Ze80 states only the irreducibility of
`ω'`; that of `ω` follows from length two and is included because the task
requires both.

### `TwoSupercuspidalAdjacentProductJacquet F T` (part (b), Jacquet modules)

Under the same hypotheses, with `B = twoBlocks k k hk hk`, for every invariant
subspace `S` of `P` with `S ≠ ⊥` and `S ≠ ⊤`, there exist actual equivalences
of representations of the Levi `B.Levi F = GL_k(F) × GL_k(F)`:

- `r_{(k,k),(2k)}(S) ≅ ρ ⊗ ρ'`: from the representation of
  `(T.normalizedJacquetFunctor B).obj (SmoothRep.subrepresentation P S)` to
  that of `FiniteTensor.externalSmoothObject (twoBlockFactors hk hk ρ.obj
  ρ'.obj)`;
- `r_{(k,k),(2k)}(P / S) ≅ ρ' ⊗ ρ`: from the representation of
  `(T.normalizedJacquetFunctor B).obj (SmoothRep.quotient P S)` to that of
  `FiniteTensor.externalSmoothObject (twoBlockFactors hk hk ρ'.obj ρ.obj)`.

By the uniqueness in the composition clause, `S` is `ω` and `P / S` is `ω'`.
The order is the source's: the submodule has Jacquet module `ρ ⊗ ρ'`, with `ρ`
on the upper-left block, and the quotient has `ρ' ⊗ ρ`, with the factors
exchanged. Ze80's "`=`" is read as isomorphism of representations, as the task
requires; equality of classes or of Jordan–Hölder multisets would be weaker.

Both equivalences are `Representation.Equiv`, a linear isomorphism of
carriers that commutes with the two actions of the same group `B.Levi F`. No
Levi transport is needed: the normalized Jacquet functor lands in
representations of `B.Levi F`, which is by definition the product group on
which the external tensor product acts. An equivalence is used rather than an
isomorphism in one smooth category because the carriers lie in different
universes: the Jacquet modules in `max uF uV`, inherited from the product, and
the external tensor products in `uV`. A `Representation.Equiv` relates
representations of one group on carriers in arbitrary universes.

Taken alone, this clause would be vacuous if no such `S` existed. It is meant
to be used with the composition clause, which supplies existence and
uniqueness of `S`. The combined entry contains both.

### `TwoSupercuspidalProductStructure F T` (entry)

The conjunction of the three clauses for the given `F` and `T`: Ze80
Proposition 1.11 in full.

## Universes

- `uF` is the universe of the field `F : PadicField.{uF} p` and of the groups
  `GL_n(F)`.
- `uV` is the carrier universe of the input supercuspidal objects and of their
  external tensor products.
- The product `ρ × ρ'` consists of functions on `GL_{k+l}(F)` with values in
  the tensor carrier, so its carrier is in `max uF uV`. Its invariant
  subspaces, quotients and Jacquet modules have carriers in the same
  universe.

The source has no universes. Both universes are arbitrary and independent, as
the task requires.

## Source boundary and remaining proof obligations

Ze80 proves Proposition 1.11 as follows (p.175):

- Ze80 states that it follows immediately from BZ77 §2.16(1) (pp.449–450,
  PDF pp.10–11) that any `ρ × ρ'` is either irreducible or satisfies all
  conclusions of part (b). BZ77 §2.16(1) treats the case `l(M) = 2`. It uses
  non-zero morphisms `π → π'` and `π' → π` between the two induced
  representations (BZ77 §2.15) and lengths of Jacquet modules to show that a
  reducible `π` has length two and a unique proper submodule. Ze80 gives no
  further argument for the Jacquet descriptions of `ω` and `ω'`.
- Part (a) is a particular case of BZ77 Theorem 4.2 (p.454, PDF p.15), stated
  in the Library as `SupercuspidalProductIrreducibilityCriterion`.
- It remains to show that `ρ × νρ` is reducible. This was announced in BZ77
  Remark 4.2(2). **Ze80 gives only a sketch of this adjacent reducibility
  step.** The sketch assumes `ρ × νρ` irreducible, normalizes
  `ρ = ν^(-1/2) ρ_0` with `ρ_0` unitary, realizes
  `π_s = ν^(-s) ρ_0 × ν^s ρ_0` on one space, and takes an analytic family of
  invariant Hermitian forms `B_s` with `B_0` positive and non-degenerate.
  Irreducibility
  would make every `B_s` non-degenerate, hence positive, so every `π_s` would be
  unitary. This contradicts an unbounded matrix coefficient of `π_s` for large
  `|s|`.

A citation, or this proposition definition, is not a proof. The later proof of
`TwoSupercuspidalProductStructure` must discharge the adjacent reducibility
step completely, either by completing Ze80's sketch or from another complete
source. It must also prove the length-two, uniqueness and Jacquet conclusions
for the actual Library objects. It cannot use Ze80 Theorem 4.2's converse for
linked pairs or the segment results of Ze80 §§2–4, since those rest on §2,
which starts from Proposition 1.11. The published reducibility statement
`SupercuspidalProductReducibilityTheorem` covers only reducibility; it states
neither the unique submodule, nor the exact length, nor the Jacquet modules.

## Original sources

- Zelevinsky, *Induced representations of reductive p-adic groups II.
  Irreducible representations of GL(n)*, Ann. Sci. ENS (4) 13 (1980). The
  relevant passages are §1.1, p.170 (PDF p.7), for `G_α`, `i_{(n),α}` and
  `r_{α,(n)}`; §§1.8–1.10, p.174 (PDF p.11), for the product and cuspidal
  representations; and §1.11, Proposition and proof sketch, p.175
  (PDF p.12). Literature ID: `zelevinsky-1980-induced-ii`, PDF SHA-256
  `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
- Bernstein and Zelevinsky, *Induced representations of reductive p-adic
  groups I*, Ann. Sci. ENS (4) 10 (1977). The relevant passages are §2.3 for
  the normalized functors `i` and `r`, §2.16(1), pp.449–450 (PDF pp.10–11),
  and §4.2, Theorem 4.2 and Remark 4.2(2), p.454 (PDF p.15). Literature ID:
  `bernstein-zelevinsky-1977-induced-i`, PDF SHA-256
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
