# Twists, contragredients and central characters of segment constituents

Author: Worker 47. These proposition definitions state how the segment
relations of the published module
`Langlands.Representation.Classification.Segments` behave under three
operations, for segments of supercuspidal representations of general linear
groups over finite extensions of p-adic fields. The operations are a common
twist by a character of the determinant, the smooth contragredient, and
restriction to the scalar matrices. The constituents involved are
Zelevinsky's `⟨Δ⟩`, the irreducible subrepresentation of
`ρ × νρ × ⋯ × ν^(m-1) ρ` (Ze80 §3.1), and the special representation
`⟨Δ⟩^t = St_m(ρ)`, the irreducible quotient of the same product (Ze80 §9.1).
Nothing is proved and no theorem is assumed as data. No constituent, dual
segment or central character is chosen: every statement relates actual
representations through actual intertwiners or actual isomorphisms.

## Objects

Fix a prime `p`, an actual finite extension `F` of `ℚ_p` (`PadicField p`) and
a compatible topological realization `T : F.TopologicalData`. Every object
below is already published. The ones from `Segments` are:

- A segment `Δ : T.Segment` with beginning `Δ.base = ρ` and length
  `m = Δ.length ≥ 1`. Here `ρ` is the isomorphism class of an irreducible
  supercuspidal representation of `GL_r(F)`, with `r = Δ.rank ≥ 1`. Its
  support is `{ρ, νρ, …, ν^(m-1) ρ}`, and `Δ.degree = m r`. The end
  `Δ.last` is `ν^(m-1) ρ`.
- `ν^s` is `T.determinantPowerCharacter d s`, the real power `|det|^s` on
  `GL_d(F)` for the normalized absolute value of `F`.
- `Δ.twist s` is the segment `ν^s Δ = [ν^s ρ, ν^(s+m-1) ρ]`. Its beginning
  is `T.supercuspidalClassRealPowerTwist r s ρ` and its length is `m`.
- For an actual supercuspidal representative `A` of `ρ`
  (`Δ.base.IsRepresentedBy A`, that is, `A.isoClass = ρ`), there are two
  upper normalized parabolic inductions from the standard block upper
  triangular parabolic subgroup with `m` blocks of size `r`.
  `T.segmentInduced A.obj m _` is the increasing product
  `ρ × νρ × ⋯ × ν^(m-1) ρ`, and `T.segmentInducedDown A.obj m _` is the
  decreasing product `ν^(m-1) ρ × ⋯ × ρ`.
- The four relations `T.IsSegmentSubrepresentation Δ π`,
  `T.IsSegmentSocle Δ π`, `T.IsSegmentQuotient Δ π` and `T.IsSegmentHead Δ π`
  all concern the increasing product of some actual representative of `ρ`.
  They say that `π` is, respectively:
  - an irreducible subrepresentation of it;
  - its unique irreducible subobject, meaning that all irreducible
    embeddings have the same image;
  - an irreducible quotient of it;
  - its unique irreducible quotient object, meaning that all irreducible
    quotient maps have the same kernel.

From other modules:

- `π.twist χ h` (`SmoothRep.twist`) is the representation
  `g ↦ χ(g) π(g)` on the same space. The hypothesis `h` says that `χ` has
  open kernel, so the twist is again smooth.
- `GeneralLinear.SupercuspidalClass.twist χ hχ hdet` (`SupercuspidalTwist`)
  sends the class of `A` to the class of `A ⊗ χ`, for a character `χ` of
  `GL_r(F)`. Here `hχ` says that `χ` has open kernel and `hdet` says that
  `χ` factors through the determinant. For `χ = η ∘ det` the factorization
  is the published `GeneralLinear.ker_determinant_le_ker_comp η`.
- `smoothContragredient ρ` is the smooth part of the algebraic dual of `ρ`.
- `HasScalarCharacter ρ GeneralLinear.scalar ω` means that the scalar matrix
  `z · 1` acts by multiplication by `ω(z)` for every `z ∈ F^×`. For a
  positive rank this is the statement that `ρ` has central character `ω`.

Every candidate `π` is a smooth complex representation of `GL_{mr}(F)` with
carrier in universe `max uF uV`, the universe of the induced
representations. The supercuspidal representatives have carriers in `uV`.

## Declarations

- `SegmentConstituentRealTwistCompatibility F T`. For every segment `Δ`,
  every real `s` and every `π` on `GL_{mr}(F)`, each of the four relations
  holds for `(Δ, π)` exactly when it holds for `(ν^s Δ, ν^s π)`. Here
  `ν^s π = π.twist (T.determinantPowerCharacter (m r) s) _`. In particular
  `ν^s ⟨Δ⟩ ≅ ⟨ν^s Δ⟩` and `ν^s ⟨Δ⟩^t ≅ ⟨ν^s Δ⟩^t`, as relations and with
  the uniqueness of subobjects and quotient objects preserved.
- `SegmentConstituentCharacterTwistCompatibility F T`. The same equivalences
  hold for an arbitrary homomorphism `χ : F^× → ℂ^×`, under two
  hypotheses: `χ ∘ det` has open kernel on `GL_r(F)` (`hr`) and on
  `GL_{mr}(F)` (`hd`). The twisted segment `χΔ` is written out inline. It
  begins at the class `SupercuspidalClass.twist (χ ∘ det) hr _ ρ` of `χρ`
  and has the same rank `r` and length `m`, so its support is
  `{χρ, νχρ, …, ν^(m-1) χρ}`. The twisted candidate is
  `π.twist (χ ∘ det) hd`. The two openness hypotheses are hypotheses. The
  statement does not claim that they are equivalent to each other or to
  continuity of `χ`.
- `SegmentConstituentContragredientCompatibility F T` (Ze80 Propositions 3.3
  and 9.4). Let `B` be an actual supercuspidal representative of the end
  `ρ' = ν^(m-1) ρ` of `Δ`, and let `B'` be an actual supercuspidal
  representation of `GL_r(F)` isomorphic to `smoothContragredient B`. The
  segment `Δv` is written out inline: it begins at the class of `B'` and has
  length `m`. For all `π` and `π'` on `GL_{mr}(F)` with `π'` isomorphic to
  `smoothContragredient π`:
  - if `π` is an irreducible subrepresentation of the increasing product
    for `Δ`, then `π'` is the unique irreducible subobject of the
    increasing product for `Δv`;
  - if `π` is an irreducible quotient of the increasing product for `Δ`,
    then `π'` is its unique irreducible quotient object for `Δv`.

  This is `⟨Δ⟩^∨ ≅ ⟨Δ^∨⟩` and `(⟨Δ⟩^t)^∨ ≅ ⟨Δ^∨⟩^t`.
- `SegmentConstituentCentralCharacter F T` (derived). Suppose that the
  representative `A` of `ρ` has central character `ω`. Put
  `ω_Δ(z) = ω(z)^m · ν^((m-1)/2)(z · 1_{mr})`, where `ν^((m-1)/2)` is
  `T.determinantPowerCharacter (m r) ((m - 1) / 2)` with a real exponent.
  Then `z · 1_{mr}` acts by `ω_Δ(z)` on the increasing product, on the
  decreasing product, and on every `π` that is an irreducible
  subrepresentation or an irreducible quotient of the increasing product.
  Since `|det(z · 1_{mr})| = |z|^(mr)`, this is
  `ω_Δ(z) = ω(z)^m |z|^(mr(m-1)/2)`. No natural-number division occurs.
- `SegmentConstituentCompatibilityTheorems F T` is the conjunction of the
  four statements for one field and one topological realization.
- `PadicSegmentConstituentCompatibilityTheorems` quantifies that conjunction
  over every prime `p`, every actual finite p-adic extension `F` and every
  compatible topological realization `T`. The universes `uF` (field) and
  `uV` (supercuspidal carriers) are arbitrary. Every rank `r ≥ 1` and every
  length `m ≥ 1` is covered, because both are fields of `Segment`.

## Sources and derivations

**Twists.** BZ77 Proposition 1.9(f) (p.445) states that twisting by a
character `χ` of the group commutes with induction:
`χ ∘ i_{U,θ} = i_{U,χθ} ∘ χ`. In Ze80 §1.8 the product `ρ_1 × ⋯ × ρ_m` is
normalized induction `i_{G,M}` from the standard Levi subgroup
`M = GL_r × ⋯ × GL_r` (BZ77 §2.3, `θ = 1`). A character `η ∘ det` of
`GL_{mr}(F)` is trivial on the unipotent radical, and on `M` it restricts to
`η ∘ det` on each block. So it carries `ρ × νρ × ⋯ × ν^(m-1) ρ` to
`ηρ × ν(ηρ) × ⋯ × ν^(m-1)(ηρ)`, using `η ν^i = ν^i η`. That is the
increasing product for `ηΔ`. Twisting by `η ∘ det` is an autoequivalence of
smooth representations with inverse the twist by `η^(-1) ∘ det`. It
therefore preserves and reflects irreducibility, injective and surjective
intertwiners, and the equality of images and of kernels. This gives the
four equivalences for `ν^s` and for general `χ`. The algebraic part of the
last step is the published `TwistConstituentCompatibilityFor`. These two
statements are derived from BZ77 1.9(f) together with the segment
relations of Ze80 §3.1 and §9.1.

**Contragredient.** Ze80 §3.3 (p.181): "For each segment `Δ = [ρ, ρ']` in
`𝒞` set `Δ^∨ = {ρ^∨ | ρ ∈ Δ}`. It is clear that `Δ^∨` is a segment in `𝒞`
with the beginning `ρ'^∨` and the end `ρ^∨`. Proposition. —
`⟨Δ⟩^∨ = ⟨Δ^∨⟩`." The proof dualizes the embedding
`⟨Δ⟩ ⊂ ρ × νρ × ⋯ × ρ'`, using Ze80 Proposition 1.1(d) (p.170). That
proposition is BZ77 Proposition 2.3(d): induction commutes with the
contragredient. Ze80 Proposition 9.4 (p.198) states
`(⟨Δ⟩^t)^∨ = ⟨Δ^∨⟩^t`, "the proof is the same as that of 3.3".

The Library has no contragredient map on supercuspidal classes. The
statement therefore takes actual representations: `B` represents
`ρ' = ν^(m-1) ρ`, and `B'` is a supercuspidal representation isomorphic to
`B^∨`. Then `Δv` has members `ν^i ρ'^∨ = (ν^(m-1-i) ρ)^∨` for
`0 ≤ i < m`. These are exactly the duals of the members of `Δ`, so `Δv` is
`Δ^∨`, beginning at `ρ'^∨` and ending at `ρ^∨`. Since
`Δ^∨ = ν^(1-m) [ρ^∨, ν^(m-1) ρ^∨]`, the real-twist statement then gives
`δ_m(ρ)^∨ ≅ ν^(1-m) δ_m(ρ^∨)` for `δ_m(ρ) = ⟨Δ⟩^t`. H02 §2.6 (p.595) drops
the dual on `ρ` in this formula, and Ze80 §§3.3 and 9.4 give the correct
version.

The hypothesis on `π` is the weak relation (an irreducible subrepresentation
or quotient). By the uniqueness in Ze80 §3.1 and §9.1, such a `π` is
`⟨Δ⟩` or `⟨Δ⟩^t` respectively. The conclusion is the strong relation
(unique subobject or unique quotient object) for `Δ^∨`.

The statement needs some supercuspidal `B'` isomorphic to `B^∨` with
carrier in `uV`; for a `Δ` with no such `B'` it is vacuous. The published
proposition `GeneralLinear.SupercuspidalContragredientStatement`, which is
stated but not proved, provides `B'`: the smooth contragredient of the
admissible supercuspidal `B` is supercuspidal and irreducible, and its
carrier `SmoothDual` lies in `uV`. The statement does not depend on that
proposition; it is quantified over every such `B'`.

**Central character.** This statement is derived; it is not a numbered
source theorem. The scalar matrix `z · 1_{mr}` is central and lies in the
Levi subgroup as `(z · 1_r, …, z · 1_r)`. It acts trivially on the Lie
algebra of the unipotent radical, so the modulus character is `1` at it.
For `f` in the induced space,
`f(g · z1) = f(z1 · g) = σ(z1) f(g)`, where `σ` is the tensor product of
the block factors. On the `i`-th block of the increasing product
(`0 ≤ i < m`), `z · 1_r` acts by `ω(z) · |det(z · 1_r)|^i = ω(z) |z|^(ri)`.
The product over the blocks is
`ω(z)^m |z|^(r · m(m-1)/2) = ω(z)^m |det(z · 1_{mr})|^((m-1)/2)`.
The decreasing product has the same exponents in the other order. An
irreducible subrepresentation or quotient inherits the scalar action of the
ambient representation; the algebraic form of this step is the published
`GLConstituentCentralCharacterFor`.

## Scope

- No proof is given. The twist statements follow formally from BZ77
  1.9(f). The contragredient statement relies on Ze80 §3.1 and §9.1, whose
  proofs go through Ze80 Theorem 2.2 and Proposition 2.10 and hence through
  Ze80 Proposition 1.11; Zelevinsky only sketches the reducibility half of
  1.11 (p.175).
- The contragredient here is the smooth contragredient. It is not the
  Hermitian contragredient of Ta86 §2.1, which is its complex conjugate.
- The twist and contragredient statements are about segment relations
  only. Multisegments and Langlands quotients are treated elsewhere.
