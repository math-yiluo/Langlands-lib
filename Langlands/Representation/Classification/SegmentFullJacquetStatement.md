# Full cuspidal Jacquet modules of segment subrepresentations and quotients

Author: Worker 890.

`Langlands.Classification.SegmentFullJacquetFormula.{uF,uV} F T` is a proposition
definition. It states Zelevinsky 1980, 3.1 (printed pp.180–181, PDF pages 17–18)
and 9.1, displayed formula (*) (printed p.197, PDF page 34), for the actual
Library objects. The source is registered as `zelevinsky-1980-induced-ii`.
**This contribution does not prove either formula.** It states them, and
compiling the definitions proves nothing about them. The file adds no helper
definitions and assumes no theorem as data.

## The statement

Fix a prime `p`, an arbitrary p-adic field `F : PadicField.{uF} p` and supplied
topological data `T : F.TopologicalData`. Everything is read under
`letI := T.topology`. The field universe `uF` and the base universe `uV` are
independent, and `uV` is not saturated.

Both clauses quantify over the following data:

- every segment `Δ : Segment.{uV,uF} T`, with beginning `ρ = Δ.base`, length
  `m = Δ.length`, cuspidal rank `r = Δ.rank` and degree `n = Δ.degree`. The
  degree is the abbreviation `Δ.length * Δ.rank`, so `n = m r`;
- every actual supercuspidal representative
  `A : SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := Δ.rank)` of `ρ`, that is,
  with `Δ.base.IsRepresentedBy A`;
- every actual smooth complex representation
  `π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)`.

Let `B = BlockShape.uniform Δ.length Δ.rank Δ.rank_pos`. This is the shape
`(r, …, r)` of `GL_{mr}` with `m` blocks. Let `J = T.normalizedJacquetFunctor B`.
`Segment.degree` is the abbreviation `length * rank` and `BlockShape.uniform m r hr`
is a shape of `m * r`, so `J` applies to `π` without a cast.

| Declaration | Hypothesis on `π` | Conclusion |
| --- | --- | --- |
| `SegmentSubrepresentationFullJacquet F T` (Ze80 3.1) | `T.IsSegmentSubrepresentation Δ π` | `Nonempty ((J.obj π).representation.Equiv (FiniteTensor.externalSmoothObject (T.segmentFactors A.obj Δ.length Δ.rank_pos)).representation)` |
| `SegmentQuotientFullJacquet F T` (Ze80 9.1(*)) | `T.IsSegmentQuotient Δ π` | `Nonempty ((J.obj π).representation.Equiv (FiniteTensor.externalSmoothObject (T.segmentFactorsDown A.obj Δ.length Δ.rank_pos)).representation)` |
| `SegmentFullJacquetFormula F T` | — | the conjunction of the two clauses |

In words:

1. If `π` is an irreducible subrepresentation of `i(ρ, νρ, …, ν^(m-1) ρ)`, then the
   normalized Jacquet module of `π` along `(r, …, r)` is equivalent to
   `A ⊗ νA ⊗ … ⊗ ν^(m-1) A`, in increasing order.
2. If `π` is an irreducible quotient of the same `i(ρ, νρ, …, ν^(m-1) ρ)`, then it
   is equivalent to `ν^(m-1) A ⊗ … ⊗ νA ⊗ A`, in decreasing order.

### The objects used

All objects are published Library declarations, used by their Lean names.

- **Segments and representatives.** `Segment` records the beginning `ρ`, a
  `CuspidalDatum` (a rank `r ≥ 1` and a supercuspidal isomorphism class of
  `GL_r(F)`), and the number `m ≥ 1` of elements. Its members are
  `ν^i ρ = Δ.base.twist i`. `CuspidalDatum.IsRepresentedBy ρ A` says that the
  actual object `A` has class `ρ.cls`.
- **The relations.** `T.IsSegmentSubrepresentation Δ π` holds when, for some
  representative `A'` of `ρ`, `π` is irreducible and has an injective intertwiner
  into `T.segmentInduced A'.obj Δ.length Δ.rank_pos`.
  `T.IsSegmentQuotient Δ π` holds when, for some representative `A'`, `π` is
  irreducible and receives a surjective intertwiner from the same induced
  representation. The induced representation is `i(A', νA', …, ν^(m-1) A')`, normalized
  parabolic induction from the standard upper block parabolic of
  `BlockShape.uniform`. **Both relations use the increasing order of induction.**
  `segmentInducedDown` is not used.
- **The block factors.** `T.segmentFactors A m hr i = T.segmentFactor A i`, the twist
  `ν^i A = A ⊗ |det|^i` placed in block `i`. `T.segmentFactorsDown A m hr i` is
  `ν^(m-1-i) A`. The twist uses `T.determinantPowerCharacter r s = |det|^s` with
  the residue-normalized absolute value. This is Ze80's `ν = |det|` with the
  standard norm of `F` (§1.11).
- **The tensor product.** `FiniteTensor.externalSmoothObject` is the actual external
  tensor product of a finite family of smooth representations. It is a
  representation of the product group `∀ i, GL_{B.size i}(F)`, with block `i`
  acting on tensor factor `i`. That group is by definition the block Levi
  `B.Levi F.Carrier`, the group on which `J.obj π` is a representation.
- **The equivalence.** `Representation.Equiv` is a linear isomorphism of carriers
  that intertwines the two actions of the same group `B.Levi F.Carrier`. The
  carriers lie in different universes. The Jacquet module of `π` has its carrier
  in `max uF uV`, and the tensor product has its carrier in `uV`. A
  `Representation.Equiv` allows this, as in the published
  `TwoSupercuspidalAdjacentProductJacquet`. The conclusion is an object-level
  equivalence of Levi representations. It is not an equality of isomorphism
  classes, a Jordan–Hölder count, an eigencharacter or an exponent norm. No
  equivalence is assumed as structure data. The topology of the Levi plays no
  role in `Representation.Equiv`.

### Choice of the representative

The conclusion uses the quantified representative `A`. The hypothesis
`IsSegmentSubrepresentation` (resp. `IsSegmentQuotient`) mentions its own
representative `A'`. The published `isSegmentSubrepresentation_iff` and
`isSegmentQuotient_iff` show that these hypotheses do not depend on the
representative. Two representatives of one class are isomorphic, so their twisted
tensor products are equivalent. Quantifying over every `A` is therefore
equivalent to the same statement for one fixed representative. The clauses are
not weakened by this choice.

## Source and notation

Ze80 §3.1 first writes a segment as `Δ = {ρ, νρ, …, ν^k ρ = ρ'}` with `k ≥ 0`, so
`[ρ, ρ']`. It defines `⟨Δ⟩` as the irreducible representation with support
`{ρ, νρ, …, ρ'}` attached by 2.2 to the orientation `ρ → νρ → … → ρ'`. It then
says:

> Let `ρ ∈ Irr G_m`, `ρ' = ν^(k-1) ρ` so `⟨Δ⟩ ∈ Irr G_n`, where `n = km`. Let
> `β = (m, m, …, m)` be a partition of `n`. Then by definition
> `r_{β,(n)}(⟨Δ⟩) = ρ ⊗ νρ ⊗ … ⊗ ρ'`
> and `⟨Δ⟩` may be defined by this property. Another way to define `⟨Δ⟩` is to
> say that `⟨Δ⟩` is the unique irreducible submodule of `ρ × νρ × … × ρ'` (or the
> unique irreducible quotient module of `ρ' × ν^(-1) ρ' × … × ρ`), see 2.10.

Ze80 §9.1 defines `⟨Δ⟩^t` by the reversed orientation `ρ ← νρ ← … ← ρ'` and says:

> Using notations of 3.1, one may define `⟨Δ⟩^t` by the property
> (*) `r_{β,(n)}(⟨Δ⟩^t) = ρ' ⊗ ν^(-1) ρ' ⊗ … ⊗ ρ`.
> Another way to define `⟨Δ⟩^t` is to say that `⟨Δ⟩^t` is the unique irreducible
> submodule of `ρ' × ν^(-1) ρ' × … × ρ` (or the unique irreducible quotient of
> `ρ × νρ × … × ρ'`), see 2.10.

Notation translation:

| Ze80 | Lean |
| --- | --- |
| `m`, with `ρ ∈ Irr G_m` | cuspidal rank `r = Δ.rank` |
| `k + 1`, the number of elements of `{ρ, …, ν^k ρ}` | length `m = Δ.length` |
| `ρ' = ν^k ρ`, the end | `ν^(m-1) ρ`, `Δ.last` |
| `n` | `Δ.degree = m * r` |
| `β = (m, …, m)` | `BlockShape.uniform Δ.length Δ.rank Δ.rank_pos` |
| `r_{β,(n)}` | `T.normalizedJacquetFunctor B` |
| `ρ × νρ × … × ρ'` | `T.segmentInduced A.obj Δ.length Δ.rank_pos` |
| `ρ ⊗ νρ ⊗ … ⊗ ρ'` | `FiniteTensor.externalSmoothObject (T.segmentFactors A.obj …)` |
| `ρ' ⊗ ν^(-1) ρ' ⊗ … ⊗ ρ` | `FiniteTensor.externalSmoothObject (T.segmentFactorsDown A.obj …)` |
| `⟨Δ⟩`, resp. `⟨Δ⟩^t` | any `π` with `IsSegmentSubrepresentation Δ π`, resp. `IsSegmentQuotient Δ π` |

The second paragraph of 3.1 changes parameters: there `ρ' = ν^(k-1) ρ` and
`n = km`, so in that sentence the source's `k` itself is the number of elements.
In both conventions the number of elements is our `m`, and `n = m r`. The
displayed formulas do not depend on this choice. 9.1(*) uses "notations of 3.1".
Its tensor `ρ' ⊗ ν^(-1) ρ' ⊗ … ⊗ ρ` has `ν^(m-1-i) ρ` in block `i`, which is
`segmentFactorsDown`.

The source writes `=` for isomorphism of representations of
`G_β = G_m × ⋯ × G_m`. The Lean conclusion reads it as an actual equivalence of
Levi representations.

No errata note for Zelevinsky 1980 exists in the Library (`notes/` has no
`errata` directory at the current Library commit). The literature index lists
none.

## Normalization of the Jacquet functor

Ze80 §1.1 takes `r_{β,(n)}` to be the normalized Jacquet functor of BZ77 §2.3, and
`i_{(n),β}` the normalized induction functor, both for the standard upper block
parabolic (§1.3). The Library uses the same normalization:

- `T.normalizedJacquetFunctor B` is the actual coinvariant quotient of the
  representation space by the unipotent radical of the standard upper block
  parabolic. The Levi acts through its section into the parabolic, times
  `δ_P(m)^(-1/2)`. Here `δ_P = T.leviModulus B`, whose factor for blocks `i < j`
  is `|det m_i|^(n_j) / |det m_j|^(n_i)`. The lemmas `normalizedJacquet_mk` and
  `normalizedJacquet_mk_eq_inv_halfModulus` in `Jacquet/Parabolic.lean` give this
  inverse half modulus.
- `T.normalizedProductInductionFunctor B`, which defines `segmentInduced`, is
  upper block parabolic induction normalized by `δ_P^(1/2)` (`T.leviHalfCharacter`).

**GL_2 check.** Let `χ` be a character of `F^× = GL_1(F)`, so `r = 1`, `m = 2`,
`Δ = [χ, νχ]`, and `B` is the torus of `GL_2`. On `diag(a, d)` one has
`δ_P = |a| / |d|`.

- *Subrepresentation.* A function `f` in `χ × νχ` satisfies
  `f(diag(a,d) u g) = |a|^(1/2) |d|^(-1/2) χ(a) χ(d) |d| f(g)
  = (χν^(1/2))(ad) f(g)`. So `g ↦ (χν^(1/2))(det g)` spans an invariant line, the
  subrepresentation `χν^(1/2) ∘ det`. This is the case `k = 1` of Ze80 3.2. The
  unipotent radical acts trivially on it. The torus acts on its normalized Jacquet
  module by `|a|^(-1/2) |d|^(1/2) · χ(a) χ(d) |a|^(1/2) |d|^(1/2) = χ(a) · (νχ)(d)`.
  That is `χ ⊗ νχ`, the tensor of `segmentFactors χ 2`, as clause 1 asserts.
- *Quotient.* The quotient `(χ × νχ) / (χν^(1/2) ∘ det)` is the twisted Steinberg
  representation `St ⊗ (χν^(1/2) ∘ det)`. The unnormalized Jacquet module of `St`
  is the character `δ_P`. The normalized Jacquet module of the quotient is
  therefore `|a|^(-1/2) |d|^(1/2) · (|a| / |d|) · χ(a) χ(d) |a|^(1/2) |d|^(1/2)
  = (νχ)(a) · χ(d)`. That is `νχ ⊗ χ`, the tensor of `segmentFactorsDown χ 2`, as
  clause 2 asserts. Exactness gives the same answer: the normalized Jacquet module
  of `χ × νχ` has the two factors `χ ⊗ νχ` and `νχ ⊗ χ`.

With `δ_P^(+1/2)` in the Jacquet functor, the subrepresentation would have
Jacquet module `νχ ⊗ χ`, contradicting 3.1. The inverse half modulus is thus the
normalization that agrees with Ze80's `r`.

## Order of induction

Both clauses take the increasing induction `i(ρ, νρ, …, ν^(m-1) ρ)`, Ze80's
`ρ × νρ × … × ρ'`. Clause 1 concerns its irreducible subrepresentation `⟨Δ⟩`, and
clause 2 its irreducible quotient `⟨Δ⟩^t`, as in the last sentence of 9.1 quoted
above. So the Jacquet module in clause 1 is the increasing tensor and that in
clause 2 the reversed, decreasing tensor. The same quotient is also the
irreducible submodule of the decreasing induction `ρ' × ν^(-1) ρ' × … × ρ`, but the
statement does not use that description.

In Ze80 §2 terms, take `R = {ρ, νρ, …, ρ'}`, whose elements are pairwise distinct.
The increasing ordering `λ` gives the orientation `ρ → νρ → … → ρ'` (2.2). By 2.10,
`π(λ) = ρ × νρ × … × ρ'` has the unique irreducible submodule `ω(λ) = ⟨Δ⟩`, with
`Ω(ω(λ)) = {ρ ⊗ νρ ⊗ … ⊗ ρ'}`. It also has the unique irreducible quotient
`ω(λ)^t`, which carries the reversed orientation, so `ω(λ)^t = ⟨Δ⟩^t`, with
`Ω(⟨Δ⟩^t) = {ρ' ⊗ ν^(-1) ρ' ⊗ … ⊗ ρ}`. All blocks have size `r`, so only the
partition `β` occurs. A one-element `Ω` means that the Jacquet module along `β`
is irreducible and isomorphic to that element.

## Weak and strong hypotheses

The hypotheses are the weak relations: `π` is *some* irreducible subrepresentation
or quotient. They are not the strong `IsSegmentSocle` / `IsSegmentHead`, which add
that all irreducible embeddings have one image, resp. all irreducible quotient
maps have one kernel. Nothing assumes that such a `π` exists.

- *Strong implies weak* in the Library: `IsSegmentSocle.isSegmentSubrepresentation`
  and `IsSegmentHead.isSegmentQuotient`. So the statement applies directly under
  the strong hypotheses.
- *Weak implies strong* mathematically, by Ze80 2.10. Its proof shows that `π(λ)`
  has a unique minimal nonzero submodule and a unique maximal proper submodule.
  The image of any irreducible embedding is a minimal nonzero submodule, and the
  kernel of any surjection onto an irreducible representation is a maximal proper
  submodule. So every irreducible subrepresentation has the same image and is
  isomorphic to `⟨Δ⟩`, and every irreducible quotient has the same kernel and is
  isomorphic to `⟨Δ⟩^t`. This equivalence is not proved here.

So the weak hypotheses describe the same representations as Ze80's `⟨Δ⟩` and
`⟨Δ⟩^t`, and the clauses are Ze80's formulas. Neither the hypotheses are
strengthened nor the conclusions weakened.

## Universes

- `uF`: the field `F`, the groups `GL_n(F)`, and the block Levi.
- `uV`: the carriers of the representatives `A` and of their twisted external
  tensor products. The index type `Fin m` lies in `Type`, so the tensor product
  stays in `uV`.
- `max uF uV`: the carrier of `π`, as required by `IsSegmentSubrepresentation`
  and `IsSegmentQuotient`, and of its Jacquet module.

The universe of `Segment.{uV,uF}` is the free `uV`. A consumer working with
`Segment.{max uF uV, uF}` uses the instance `uV := max uF uV`.

## Proof status

This file states the formulas and proves nothing about them. Ze80 derives them
from §2 (Theorem 2.8, Corollary 2.9, Proposition 2.10, with 2.2, 2.4 and 2.7). That
route uses the geometric lemma, multiplicity-freeness of the full cuspidal Jacquet
module of `ρ × νρ × … × ρ'`, Ze80 1.11 for two supercuspidal representations,
exactness and transitivity of Jacquet functors, and Frobenius reciprocity. Each of
these must be proved for the Library objects in the separate proof task.

## Original source

Zelevinsky, *Induced representations of reductive p-adic groups II. Irreducible
representations of GL(n)*, Ann. Sci. ENS (4) 13 (1980). Literature ID
`zelevinsky-1980-induced-ii`, PDF SHA-256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`. The relevant
passages are §1.1 (p.170) for `i` and `r`; §2.1–2.10 (pp.176–180) for the setting,
the orientations and Proposition 2.10; 3.1 and 3.2 (pp.180–181); and 9.1 with (*)
(p.197).
