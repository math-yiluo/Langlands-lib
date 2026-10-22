# Multisegment socle and Langlands head compatibility

Worker 67 authored the five-clause statement family. Worker 126 contributed
an independently developed four-clause draft and the source/derivation audit
adapted below. Worker 111 contributed the endpoint, reversed-block, and
central-character source audit. This is a proposition-definition installment: it states, and
does not prove, compatibility of the actual published constituent relations.

## Scope, universes, and conventions

Fix a prime `p`, `F : PadicField.{uF} p`, and its compatible topological
realization `T`. The coefficient field is `ℂ`. Field universe `uF` and
supercuspidal-carrier universe `uV` are independent. Segments have type
`T.Segment.{uV, uF}`; their supercuspidal representatives have carrier
universe `uV`. Output representations have carrier universe `max uF uV`.
Every output rank `n` in this family is positive. Finite segment families
may be empty, but a constituent relation at positive rank cannot be
witnessed by an empty product. No rank-zero classification is asserted.

Write `ν = |det|`, with the residue-normalized absolute value
`|varpi| = q⁻¹`. A segment `Δ = [ρ, ν^(m-1)ρ]` begins at a supercuspidal
class of positive rank `d`, has positive length `m`, and degree `md`.
Its socle `Z(Δ)` is the irreducible socle of the increasing cuspidal
product; its special head `L(Δ)` is the irreducible head of that product.
All induction uses the standard upper block parabolic, right translation,
and covariance by `δ_P^(1/2)`, as in BZ77 §§1.8 and 2.2–2.3.

The published relations `Multisegment.IsZelevinskySocle` and
`Multisegment.IsLanglandsHead` quantify over actual `SegmentProductDatum`
whose multiset is the given one. Such data list segments so that no earlier
segment precedes a later one, and the blocks are respectively segment
socles or segment heads. The output is the irreducible socle or irreducible
head of their actual normalized induction. The strong constituent relations
use equality of images of irreducible embeddings or kernels of irreducible
quotient maps. They do not choose classification outputs. Existence,
ordering independence, and classification bijections are separate assertions.

`List.ofFn` in the dual and scalar-character clauses enumerates multisets
with multiplicity. The displayed family need not itself be ordered: the
multisegment relations quantify over an appropriate ordering. No separate
degree equation is a hypothesis; the constituent relation supplies product
data of total degree `n`.

## Exact declaration correspondence

All declarations below are in namespace `Langlands.Classification`.

| Declaration | Lean assertion | Original source or explicit derivation |
| --- | --- | --- |
| `MultisegmentConstituentRealTwistCompatibility F T` | For every positive rank, multisegment `a`, real `s`, and actual smooth `π`, both constituent relations are equivalent to their versions for `a.twist s` and `π.twist (ν^s)`. | Ta86 §1.8, pp.342–343, for socles; Proposition 5.6(ii), p.363, for heads. |
| `MultisegmentConstituentCharacterTwistCompatibility F T` | For a character `χ : Fˣ →* ℂˣ` with open kernel, twist every segment base by `χ ∘ det`, keep its length, and map the entire multiset. Each constituent relation is equivalent to that for the actual `χ ∘ det` twist of `π`. | Derived from BZ77 Proposition 1.9(f), p.445, and the constituent relations; reasoning below. |
| `MultisegmentConstituentContragredientCompatibility F T` | For any finite family `Δ_i` and supercuspidal representatives `B_i` of their endpoints, there exist supercuspidal `Bv_i` genuinely equivalent to their actual smooth duals. The segments beginning at `[Bv_i]` with the original lengths form `av`. For every positive rank and `π`, a socle or head relation for `a` implies the corresponding relation for `av` and the actual smooth dual of `π`. | Ze80 §3.3, p.181, and Theorem 7.10, pp.194–195; Ta86 §1.15, p.344, and Proposition 5.6(iii), p.363. |
| `SquareIntegrableLanglandsHeadContragredientCompatibility F T` | If `d : SquareIntegrableLanglandsDatum n` and `π` is its Langlands head, the actual smooth dual of `π` is the irreducible head of normalized induction on `d.shape.reverse` of the actual smooth dual blocks `(d.blocks i.rev)^∨`. | H02 §2.8, p.596. |
| `MultisegmentConstituentCentralCharacter F T` | If `A_i` represents the beginning of `Δ_i` and has prescribed scalar character `ω_i`, either constituent of `{Δ_i}` has the product of the segment scalar characters specified below. | Derived from BZ77 §§1.6 and 1.8, pp.443–444, and the published segment scalar-character formula; it is not asserted to be part of Ta86 §5.6. |
| `MultisegmentConstituentCompatibilityTheorems F T` | Conjunction of the preceding five propositions. | Internal packaging, with no new mathematical assertion. |
| `PadicMultisegmentConstituentCompatibilityTheorems` | The conjunction for every prime, finite p-adic extension, and compatible realization, with both universes explicit. | Internal universal quantification. |

## Twist construction and derived character statement

The real twist uses the published `Multisegment.twist`,
`determinantPowerCharacter`, and its open-kernel theorem. The general
character clause constructs each segment using the published
`SupercuspidalClass.twist`; it does not posit a class transformation.
For every rank `k`, the required openness proof is explicitly
`hχ.preimage (T.generalLinearDeterminant k).continuous`.
The kernel-containment proof is `ker_determinant_le_ker_comp χ`.
Thus the inline construction proves its intrinsic topology obligations.

BZ77 1.9(f) moves a character through normalized induction. A determinant
character is trivial on the unipotent radical and restricts on a Levi to
the product of that character on the individual block determinants. It
commutes with powers of `ν`. Twisting by its inverse gives an inverse
functor, so it preserves and reflects irreducibility and equality of
images or kernels. Its bijection on supercuspidal classes commutes with
`ν`, and therefore preserves linkage and precedence. Applying this to
segment blocks and their product gives the two asserted equivalences.
This argument explains the derived statement; no new proof of those
compatibilities is implemented here.

## Smooth contragredients and endpoint reversal

For `Δ_i = [ρ_i, ν^(m_i-1)ρ_i]`, the dual segment begins at
`(ν^(m_i-1)ρ_i)^∨ = ν^(1-m_i)ρ_i^∨` and ends at `ρ_i^∨`.
In Lean, `B_i` represents `(Δ_i).last`, and the conclusion supplies
`Bv_i` together with
`Nonempty ((Bv_i).obj.representation.Equiv
  (smoothContragredient (B_i).obj.representation))`.
The inline segment `Δv_i` begins at `(Bv_i).isoClass`, retains the positive
rank and length, and is enumerated into the actual multiset `av`.

The supercuspidal dual representatives are existential conclusions,
not compatibility or existence assumptions. Their existence is part of
the source assertion that the dual segment remains a segment in the
supercuspidal set (Ze80 §3.3, Ta86 §1.15). Explicit preservation sources
are Ca95 Proposition 2.1.10 and Corollary 2.1.13, p.22, for admissibility
and irreducibility, and Theorem 5.3.1(a)–(b), pp.48–49, for
supercuspidality. Its eventual Lean proof needs these preservation
results; this module supplies none of those proofs. The smooth-dual carrier lies in the
same carrier universe, since it is a subspace of the complex linear dual.
No total or arbitrary map on supercuspidal classes is introduced.
The proposition supplies one family of endpoint dual representatives
that works for every output rank and every candidate `π`.

The target representation is exactly
`SmoothRep.of (smoothContragredient π.representation)
  (isSmooth_smoothContragredient π.representation)`.
Both constituent conclusions are forward implications. There is no
claim of bidual reflexivity for all smooth representations. No order is
imposed on the displayed dual family: its target multisegment relation
provides the ordering. All representation equivalences are actual linear
intertwining equivalences, rather than a user-supplied isomorphism predicate.

For square-integrable data, `d.shape.reverse.size i` is definitionally
`d.shape.size i.rev`. The inline `dualBlocks` therefore has exactly the
rank required by the reversed induction functor. Smoothness is supplied
by the published `isSmooth_smoothContragredient` proof. The conclusion is
`IsIrreducibleHead` for this concrete reversed product and the concrete
dual of `π`. It introduces no second `SquareIntegrableLanglandsDatum`
whose constructor fields would require additional analytic proofs.
H02 §2.8 orders exponents weakly decreasingly. Duality negates them, so
reversing their order gives the corresponding weakly decreasing dual
order, including equal-exponent blocks. The formula is
`J(π_1,…,π_r)^∨ ≅ J(π_r^∨,…,π_1^∨)`.

The dual throughout is the smooth contragredient. Ta86 §2.1 also defines
a Hermitian contragredient involving complex conjugation; that operation
is not asserted here. Ta86's proof of 5.6 cites Ze80 Proposition 9.5 for
the segment-dual formula, but the formula occurs in Ze80 Proposition 9.4,
p.198. The cited Langlands-head proof also uses Jacquet's *Principal
L-functions of the linear group*, equation (3.3.13); that upstream proof
source has not been read for this contribution. Neither that citation nor
Ze80's conjecture in §9.17 is treated as a supplied Lean proof.

## Central-character formula

Put `m_i = (Δ_i).length` and `d_i = (Δ_i).rank`. The Lean segment factor is

```text
ωΔ_i = ω_i ^ m_i *
  (T.determinantPowerCharacter (Δ_i).degree ((m_i - 1)/2)).comp scalar,
```

where the exponent's subtraction and division are real operations. The
conclusion is `HasScalarCharacter π.representation scalar (∏ i, ωΔ_i)`.
In scalar notation,

```text
ω_a(z) = ∏ i, ω_i(z)^m_i |z|^(d_i*m_i*(m_i-1)/2).
```

This is a derived assertion. On the `j`-th cuspidal member of segment `i`,
for `0 ≤ j < m_i`, the scalar acts by `ω_i(z)|z|^(d_i*j)`.
Multiplication over `j` gives exactly the segment factor above. A scalar
matrix lies in the Levi with the same scalar on every block. Its conjugation
on the unipotent radical is trivial, so its parabolic modulus is one;
this identity is already proved by `T.leviModulus_scalar` in the published
`Langlands.Group.GL.BlockModulus` module.
In the normalized induced model, right translation by the scalar can be
moved to the left, and covariance gives the product of the block scalar
actions. Injective or surjective intertwiners transfer the scalar action
to subrepresentations or quotients. Applying this to segment constituents
and then to their product yields the displayed finite product, with
multiplicity and independently of enumeration.

The character of each base representative is an explicit hypothesis.
This clause does not assert central-character existence for arbitrary
smooth representations. The product of an empty family is the trivial
character; at positive rank the premise for that empty family is
unrealizable by the constituent definitions.

## Published dependencies and remaining proof obligations

The five direct imports are already published modules:

- `Langlands.Representation.Classification.LanglandsData`: actual
  multisegment relations, square-integrable data, block induction, and
  their underlying segment and smooth-representation constructions.
- `Langlands.Representation.Classification.SegmentConstituentCompatibilityStatement`:
  single-segment statement targets, including
  `SegmentConstituentContragredientCompatibility` and
  `SegmentConstituentCentralCharacter`; they are reused as the statement
  boundary, not assumed as proofs or duplicated.
- `Langlands.Representation.Classification.ConstituentCompatibility`:
  the algebraic `TwistConstituentCompatibilityFor` and
  `GLConstituentCentralCharacterFor` statement interfaces for actual
  twists, intertwiners, and scalar action.
- `Langlands.Representation.Smooth.Contragredient.LawsProof`:
  the actual smooth dual and the proved
  `isSmooth_smoothContragredient` used to form smooth representations.
- `Langlands.Group.GL.ReverseBlocks`: the actual `BlockShape.reverse`
  with its positivity and total-rank proofs.

No draft or pending classification candidate is imported. No induction,
classification, or constituent-existence theorem is supplied as a
constructor field or proposition hypothesis. The substantive compatibility
assertions remain unproved. Their eventual proofs require induction/twist
and induction/dual equivalences, segment and multisegment classification,
supercuspidal-dual preservation, and the scalar-action calculation.
The source-level supercuspidal-dual input has a separate published target
`GeneralLinear.SupercuspidalContragredientStatement`.
Dualizing a socle embedding alone produces a quotient, so it does not by
itself prove the socle-dual clause; Ze80 Theorem 7.10 is essential.
The reversed square-integrable head statement uses H02 §2.8 beyond the
single-segment assertion. Compilation and `Prop` inspection check the
formal statements, not these outstanding mathematical proofs.

## Retained originals and reading extent

Source IDs and fingerprints below identify registered, retained originals.
All PDF page numbers are one-based. Relevant sections were read for this
statement family; there is no claim to have read every article in full.
No source-specific project errata files were found for these source IDs.

- **BZ77:** I. N. Bernstein and A. V. Zelevinsky, *Induced representations
  of reductive p-adic groups I*, Ann. Sci. ENS (4) 10 (1977), 441–472.
  ID `bernstein-zelevinsky-1977-induced-i`; SHA-256
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
  Read §§1.4–1.9 and 2.2–2.3, pp.443–446 (PDF pp.4–7): tensor product,
  covariance, right action, character twists, and upper normalized products.
- **Ze80:** A. V. Zelevinsky, *Induced representations of reductive p-adic
  groups II. On irreducible representations of GL(n)*, Ann. Sci. ENS (4)
  13 (1980), 165–210. ID `zelevinsky-1980-induced-ii`; SHA-256
  `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
  Read the relevant normalization and duality passages on pp.170–171,
  §3.3 p.181, Theorem 7.10 and proof pp.194–195, and §9.4 p.198
  (PDF pp.7–8, 18, 31–32, 35). Worker 126 additionally audited
  §§6.1–6.5, pp.188–189 (PDF pp.25–26).
- **Ta86:** M. Tadić, *Classification of unitary representations in
  irreducible representations of general linear group (non-archimedean
  case)*, Ann. Sci. ENS (4) 19 (1986), 335–382.
  ID `tadic-1986-unitary`; SHA-256
  `08e4e1e7c1ccc1e340999287867bc0448f3d8f4bab49906fbf1deda866ae4683`.
  Read the segment and twist conventions in §§1.3–1.9, ordinary dual in
  §1.15, Hermitian dual in §2.1, and §§5.1–5.6, especially Proposition
  5.6 on p.363 (relevant pp.341–345, 361–363; PDF pp.8–12, 28–30).
- **H02:** G. Henniart, *Une caractérisation de la correspondance de
  Langlands locale pour GL(n)*, Bull. Soc. Math. France 130 (2002),
  587–602. ID `henniart-2002-characterization`; SHA-256
  `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.
  Read §§2.6–2.9, pp.595–597 (PDF pp.9–11), using §2.8, p.596
  (PDF p.10), for the reversed square-integrable Langlands-head dual.
- **Ca95:** W. Casselman, *Introduction to the theory of admissible
  representations of p-adic reductive groups*, draft of 1 May 1995.
  ID `casselman-1995-admissible-representations`; SHA-256
  `78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`.
  Worker 111 read §§2.1 and 5.1, pp.21–22 and 46, Corollary 4.2.5,
  p.42, and Theorem 5.3.1, pp.48–49, for the endpoint-dual
  supercuspidal representatives. Worker 67 rechecked Proposition 2.1.10,
  Corollary 2.1.13, p.22, and Theorem 5.3.1(a)–(b), pp.48–49.
  Printed and one-based PDF page numbers coincide.
