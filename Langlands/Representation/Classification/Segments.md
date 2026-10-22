# Segments, multisegments and the representations `i(ρ, νρ, …, ν^(m-1) ρ)`

Author: Worker 23.

This module formalizes Zelevinsky's segments of irreducible supercuspidal classes
of the groups `GL_r(F)` for a p-adic field `F`, his linkage relations and
multisegments, and the induced representations `i(ρ, νρ, …, ν^(m-1) ρ)`. These
are the inputs of the Zelevinsky and Langlands classifications. The special
constituents of these induced representations are recorded only by relations:
Zelevinsky's `⟨Δ⟩` and Henniart's `St_m(ρ)`. The module asserts neither their
existence nor their uniqueness.

Everything is built from published Library constructions: supercuspidal classes
(`Classification/Supercuspidal`), the twist `A ↦ A ⊗ |det|^s` on objects and on
classes (`Category/Twist`, `Classification/SupercuspidalTwist`), the normalized
induction of block factors `i(σ_1, …, σ_r)` (`Induction/BlockFactors`), and the
constituent relations of `Classification/ConstituentRelations`.

## Transport of constituent relations

Namespace `Langlands.Classification`. `G` is any group and the representations are
complex. The ambient representations `ρ` and `ρ'` share one carrier universe with
the constituent `π`.

- `IsIrreducibleQuotient.of_equiv` and `IsIrreducibleHead.of_equiv` transport a
  quotient relation along an actual equivalence `ρ ≃ ρ'` of the source. The head
  form also transports its uniqueness clause, that all irreducible quotient maps
  have the same kernel.
- `IsIrreducibleSubrepresentation.of_equiv` and `IsIrreducibleSocle.of_equiv` do
  the same for subrepresentations of the ambient representation. The socle form
  also transports its uniqueness clause, that all irreducible embeddings have the
  same image.
- Each comes with an `_iff_of_equiv` form.

These are internal lemmas used below to show that the segment relations do not
depend on the representative.

## Uniform block shapes and twisting classes

- `GeneralLinear.BlockShape.uniform m r hr` is the ordered block shape
  `(r, …, r)` of `m * r`, with `m` blocks of size `r ≥ 1`. It has simp lemmas
  for its length and block sizes.
- `GeneralLinear.SupercuspidalClass.twist_congr` shows that the published class
  twist depends only on the character, not on the proofs of its side conditions.
- `PadicField.TopologicalData.supercuspidalClassRealPowerTwist_zero` and
  `supercuspidalClassRealPowerTwist_add` prove the action laws `ν^0 a = a` and
  `ν^s (ν^t a) = ν^(s+t) a` for the published twist by `|det|^s` on classes.

## Cuspidal data and segments

Fix a prime `p`, a p-adic field `F : PadicField.{uF} p`, and a realization
`T : F.TopologicalData`. All constructions below take `T` as an explicit
argument. Here `ν = |det|`, the published `T.determinantPowerCharacter`: the
absolute value is residue-normalized, so `|ϖ| = q⁻¹`.

- `T.CuspidalDatum` is an element of Zelevinsky's set `𝒞`. It consists of a rank
  `r ≥ 1` and a published `SupercuspidalClass`, the isomorphism class of an
  irreducible supercuspidal representation of `GL_r(F)` with carrier in
  `Type uV`. Zelevinsky's "cuspidal" representations are those whose Jacquet
  modules vanish for all proper parabolics. These are the supercuspidal
  representations of the Library.
- `CuspidalDatum.twist s ρ = ν^s ρ`, for a real `s`, applies the published class
  twist. `twist_zero` and `twist_twist` are the action laws.
- `T.Segment` records a segment by its beginning `base = ρ` and its number of
  elements `length = m ≥ 1`. `member i = ν^i ρ`, `last = ν^(m-1) ρ`, and
  `support = {ρ, νρ, …, ν^(m-1) ρ}` is the segment as a subset of `𝒞`. `rank` is
  the common rank `r` of its members, and `degree = m r`. `Segment.twist s`
  twists the beginning by `ν^s`. It has the action laws, and `member_twist` shows
  that it twists every member.
- `Segment.IsLinked Δ₁ Δ₂` holds when neither support contains the other and the
  union of the supports is the support of a segment. It is symmetric
  (`IsLinked.symm`, `isLinked_comm`) and irreflexive (`not_isLinked_self`).
- `Segment.IsJuxtaposed Δ₁ Δ₂` holds when the segments are linked and their
  supports are disjoint.
- `Segment.Precedes Δ₁ Δ₂` holds when the segments are linked and the beginning
  of `Δ₂` is `ν^k` times the beginning of `Δ₁` for a natural number `k > 0`.

**Encoding.** Zelevinsky defines a segment as a subset
`{ρ, νρ, …, ν^k ρ}` of `𝒞` with `k ≥ 0`. The structure records the beginning and
the number of elements, and `support` recovers the subset. All three relations
are stated through `support`, as in the source. A segment in Zelevinsky's sense
determines its beginning and its number of elements only because
`ν^a ρ ≇ ρ` for every integer `a ≠ 0`. The central characters of `ν^a ρ` and `ρ`
differ by `|z|^(a r)` on scalars `z`. That fact is a theorem, which is neither
proved nor assumed here. Without it, two values of `Segment` could have the same
support. Similarly, Zelevinsky's exponent `k` in "precedes" is an integer, and
`k > 0` makes it a positive natural number.

## Multisegments and orderings

- `T.Multisegment` is `Multiset (T.Segment)`. This is Zelevinsky's set `𝒪` of
  finite multisets of segments, and the empty multiset is included. `degree` is
  `∑ m_i r_i`, and `twist s` twists every segment.
- `Multisegment.IsOrdering a Δ` holds when the family `Δ : Fin r → Segment` lists
  `a` with multiplicities. `IsListOrdering a l` is the same condition for a list
  `l`. The two agree by `isOrdering_iff_isListOrdering`.
- `Multisegment.IsUnlinked a` holds when no two segments of `a` are linked. This
  is condition (2) of Zelevinsky's Theorem 4.2. A segment is never linked with
  itself, so the diagonal is harmless.
- `T.IsPrecedenceOrdered Δ` holds when `Δ i` does not precede `Δ j` for any
  `i < j`. This is the hypothesis of Zelevinsky's Theorem 6.1(a).
  `IsPrecedenceOrderedList` is the same condition for lists (`List.Pairwise`),
  and `isPrecedenceOrdered_iff_list` shows the two agree on `List.ofFn Δ`.

## The induced representations

`A` is a smooth complex representation of `GL_r(F)` with carrier in `Type uV`, as
an object `SmoothRep.{0, uF, uV} ℂ (GL_r(F))` for the topology of `T`. The
representations are not required to be irreducible or supercuspidal.

- `T.segmentFactor A s` is the actual twist `ν^s A`, acting by
  `g ↦ |det g|^s A(g)`. It is the published `SmoothRep.twist` by
  `T.determinantPowerCharacter r s`.
- `T.segmentFactors A m hr` is the family `(A, νA, …, ν^(m-1) A)` indexed by the
  blocks of `uniform m r`.
- `T.segmentInduced A m hr` is `i(A, νA, …, ν^(m-1) A)` on `GL_{mr}(F)`. It is
  the published `T.normalizedProductInductionFunctor (uniform m r)` applied to
  that family: normalized parabolic induction from the standard upper block
  parabolic with `m` diagonal blocks of size `r`.
  `segmentInduced_representation` identifies its representation with
  `T.normalizedProductInduced` by `rfl`.
- `T.segmentInducedIso e m hr` sends an isomorphism `e : A ≅ A'` to an isomorphism
  of the induced objects. It applies the induction functor to the family of
  twisted isomorphisms.
- `segmentFactorsDown`, `segmentInducedDown` and `segmentInducedDownIso` are the
  decreasing order `i(ν^(m-1) A, …, νA, A)`.

## Segment relations

`CuspidalDatum.IsRepresentedBy ρ A` says that the actual supercuspidal object `A`
has isomorphism class `ρ`. For a segment `Δ = [ρ, ν^(m-1) ρ]` and a smooth
representation `π` of `GL_{mr}(F)` with carrier in `Type (max uF uV)`:

- `T.IsSegmentQuotient Δ π`: for some representative `A` of `ρ`, `π` is an
  irreducible quotient of `i(A, νA, …, ν^(m-1) A)`.
- `T.IsSegmentHead Δ π`: the same, and every irreducible quotient map of the
  induced representation has the kernel of the given one. This is the form
  satisfied by Henniart's `St_m(ρ)`, and by Zelevinsky's `⟨Δ⟩^t` in its quotient
  description.
- `T.IsSegmentSubrepresentation Δ π`: for some representative `A`, `π` is an
  irreducible subrepresentation of `i(A, νA, …, ν^(m-1) A)`.
- `T.IsSegmentSocle Δ π`: the same, and every irreducible embedding into the
  induced representation has the image of the given one. This is the form
  satisfied by Zelevinsky's `⟨Δ⟩`.

The four relations do not depend on the representative.
`segmentInducedIsoOfRepresented` and `segmentInducedDownIsoOfRepresented` give the
isomorphism between the induced objects of two representatives. The theorems
`isSegmentQuotient_iff`, `isSegmentHead_iff`, `isSegmentSubrepresentation_iff`
and `isSegmentSocle_iff` restate each relation for any fixed representative.
`IsSegmentHead.isSegmentQuotient` and `IsSegmentSocle.isSegmentSubrepresentation`
drop the uniqueness clause.

The relations do not assert existence. The head and socle forms state uniqueness
only relative to a given `π`. Zelevinsky's statement that `⟨Δ⟩` exists and is the
unique irreducible submodule is a theorem, and so is Henniart's statement that
`i(ρ, …, ν^(n-1) ρ)` has a unique irreducible quotient. Neither is proved here.
Constructors of `⟨Δ⟩` or `St_m(ρ)` as representations or classes therefore await
those theorems. The decreasing-order representation `segmentInducedDown` gives
Zelevinsky's second description of `⟨Δ⟩^t`, as the unique irreducible submodule of
`ρ' × ν⁻¹ρ' × … × ρ`. That description is available by applying
`Classification.IsIrreducibleSocle` to it. No separate relation is named for it.

## Universes and scope

The supercuspidal representatives and the block factors have carriers in
`Type uV`. The field `F` lies in `Type uF`. The induced carrier lies in
`Type (max uF uV)`, as in `Induction/BlockFactors`. The published constituent
relations compare the induced representation only with constituents in its own
carrier universe, so `π` lies in `Type (max uF uV)`. Every p-adic field, every
rank `r ≥ 1` and every segment length `m ≥ 1` is covered, so every `GL_n(F)` with
`n = m r` is reached.

## Source correspondence

- Zelevinsky (1980), introduction, printed page 166 / PDF page 3: "Call a
  segment in 𝒞 any subset of 𝒞 of the form Δ = {ρ, νρ, ν²ρ, ..., ν^k ρ = ρ'}
  where ν is the character ν(g) = |det g| and k is an integer ≥ 0 (we use the
  notation Δ = [ρ, ρ']). To each segment Δ = [ρ, ρ'] in 𝒞 we associate the
  irreducible representation ⟨Δ⟩ = ⟨[ρ, ρ']⟩ (3.1); it may be defined as the
  (unique) irreducible submodule of ρ × νρ × ... × ρ'." This gives `Segment`,
  `support`, `segmentInduced` and `IsSegmentSocle`. The same page defines `𝒪` as
  the finite multisets of segments.
- Zelevinsky (1980), section 3.1, printed page 180 / PDF page 17: `𝒞` is the set
  of equivalence classes of irreducible cuspidal representations of the groups
  `G_n`, `n = 1, 2, …` (`CuspidalDatum`). A segment is a subset
  `{ρ, νρ, …, ν^k ρ = ρ'}`, where `ρ` is its beginning and `ρ'` its end
  (`base`, `last`).
- Zelevinsky (1980), section 4.1, printed page 184 / PDF page 21: "We say that
  Δ₁ and Δ₂ are linked if Δ₁ ⊄ Δ₂, Δ₂ ⊄ Δ₁ and Δ₁ ∪ Δ₂ is also a segment. If Δ₁
  and Δ₂ are linked and Δ₁ ∩ Δ₂ = ∅ then we say that Δ₁ and Δ₂ are juxtaposed
  ... If Δ₁ and Δ₂ are linked and ρ₂ = ν^k ρ₁ where k > 0 then we say that Δ₁
  precedes Δ₂." This gives `IsLinked`, `IsJuxtaposed` and `Precedes`. Theorem
  4.2(2) on the same page gives `Multisegment.IsUnlinked`.
- Zelevinsky (1980), section 6.1(a), printed page 188 / PDF page 25: "Suppose
  for each pair of indices i, j such that i < j, Δ_i does not precede Δ_j"
  (`IsPrecedenceOrdered`, `IsPrecedenceOrderedList`).
- Zelevinsky (1980), section 6.5, printed page 189 / PDF page 26: `𝒪`, the set of
  all finite multisets of segments, with `π(∅)` defined for `G_0`
  (`Multisegment`, including the empty multiset), and orderings `(Δ_1, …, Δ_r)`
  of `a` (`IsOrdering`, `IsListOrdering`).
- Zelevinsky (1980), section 9.1, printed page 197 / PDF page 34: "Another way to
  define ⟨Δ⟩^t is to say that ⟨Δ⟩^t is the unique irreducible submodule of
  ρ' × ν⁻¹ρ' × ... × ρ (or the unique irreducible quotient of
  ρ × νρ × ... × ρ'), see 2.10." This gives `IsSegmentHead` and
  `segmentInducedDown`.
- Zelevinsky (1980), sections 1.5 and 1.7, printed pages 171--173: the product
  `ρ_1 × ⋯ × ρ_r` is `i(ρ_1 ⊗ ⋯ ⊗ ρ_r)`, normalized induction from the standard
  block parabolic. The construction here induces the tensor product of all `m`
  factors at once, as in `Induction/BlockFactors`.
- Henniart (2002), sections 2.5--2.6, printed page 595 / PDF page 9: "Si χ est un
  quasicaractère de F× et π ∈ A, on note χπ ∈ A la classe de la représentation
  g ↦ χ∘det(g)π(g). On note encore ν le quasicaractère de F× donné par la valeur
  absolue normalisée." (`segmentFactor`, `CuspidalDatum.twist`.) And: "On forme
  la représentation i(ρ, νρ, ..., ν^(n−1)ρ); elle a un unique quotient
  irréductible, qui est essentiellement de carré intégrable, et sa classe est
  St_n(ρ)." (`segmentInduced`, `IsSegmentHead`.)

The originals were read at these pages. Registered sources:

- `zelevinsky-1980-induced-ii`, SHA256
  `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
- `henniart-2002-characterization`, SHA256
  `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.

Two derivations are explicit. The induced representations accept arbitrary smooth
`A`, not only supercuspidal ones. The relations quantify over actual
representatives of a class and are shown to be independent of the choice.

## Not claimed

This module does not prove the existence or uniqueness of `⟨Δ⟩`, `⟨Δ⟩^t` or
`St_m(ρ)`, or that `St_m(ρ)` is essentially square-integrable. It does not prove
that a segment is determined by its support, or that a precedence-ordered
ordering of a multisegment exists. It does not prove Zelevinsky's Theorems 4.2
and 6.1 or his classification bijection. It defines no contragredient segment
`Δ^∨`, Zelevinsky involution or Langlands data. The normalized induction uses the
published explicit block modulus, whose identification with the Haar module is a
separate obligation recorded in `Induction/Parabolic.md`.
