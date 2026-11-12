# Inputs of Tadić's Lemma 4.8(ii) and the reduction to them

Author: Worker 5121. Module
`Langlands.Representation.Classification.TadicBlockReductionStatement`.

This pair states three results that Tadić's proof of Lemma 4.8(ii) uses and that no
published statement covers yet. It also states the conjunction of all inputs of that
proof and the implication from them to the published
`Langlands.Classification.TadicBlockReduction` (module `TadicExhaustionLemmasStatement`).
**Nothing is proved here.** The module consists of Prop-valued definitions only. It adds
no axiom, no `sorry` and no structure field assuming the existence of anything.

## Sources

- M. Tadić, *Classification of unitary representations in irreducible representations of
  general linear group (non-Archimedean case)*, Ann. Sci. ÉNS (4) 19 (1986), 335–382,
  literature ID `tadic-1986-unitary`, SHA-256
  `08e4e1e7c1ccc1e340999287867bc0448f3d8f4bab49906fbf1deda866ae4683`. PDF page = printed
  page − 333. Used: §2.1–2.4 (pp.345–346), §3.1–3.3 (pp.352–353), Proposition 3.8
  (p.354), Lemma 4.8 and its proof (pp.360–361).
- A. V. Zelevinsky, *Induced representations of reductive p-adic groups II*, Ann. Sci.
  ÉNS (4) 13 (1980), 165–210, literature ID `zelevinsky-1980-induced-ii`, SHA-256
  `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`. Used:
  Proposition 8.5 (printed p.196, PDF p.33).

## Parameters and conventions

Every definition takes an arbitrary prime `p` with `[Fact p.Prime]`,
`F : PadicField.{uF} p` and `T : F.TopologicalData`. The field universe `uF` and the
representation universe `uV` are independent. Representations are actual smooth complex
representations `SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)` with
`letI := T.topology`, the carriers of `TadicBlockReduction`. Cuspidal data, segments and
multisegments are `T.CuspidalDatum.{max uF uV, uF}`, `T.Segment.{max uF uV, uF}` and
`T.Multisegment.{max uF uV, uF}`.

- `a.IsZelevinskySocle π` is the published `Multisegment.IsZelevinskySocle`: for some
  precedence-ordered ordering of `a` and some segment socles `⟨Δ_i⟩`, `π` is the
  irreducible socle of their normalized product. This is Zelevinsky's `⟨a⟩`.
- `tadicMultisegment ρ n d hd` is the published `a(n,d)^ρ` of Tadić §3.1 and §4.6.
- Products are the published normalized upper-block products
  `(T.normalizedProductInductionFunctor B).obj π` for a block shape `B`.
- `Δ.IsLinked Δ'` is the published Zelevinsky linkage `Segment.IsLinked`: neither
  segment contains the other and their union is a segment.
- A segment is recorded by its beginning and its length: `⟨ρ.twist x, l, hl⟩` is
  `[ν^x ρ, ν^(x+l-1) ρ]`.
- `ρ.IsUnitary` is the published `CuspidalDatum.IsUnitary`: `ρ ∈ C^u`.

## `UnlinkedSocleProductIrreducibility F T` (Zelevinsky, Proposition 8.5)

Zelevinsky p.196: "Let `a_1, …, a_p ∈ O`. Suppose for `i ≠ j` each segments
`Δ ∈ a_i`, `Δ' ∈ a_j` are not linked. Then `⟨a_1⟩ × … × ⟨a_p⟩ = ⟨a_1 + … + a_p⟩`."

The Lean statement: for every block shape `B : BlockShape n`, multisegments
`a : Fin B.length → T.Multisegment` and representations `π i` of `GL_(B.size i)` with
`(a i).IsZelevinskySocle (π i)` for every `i`, if for all `i ≠ j`, all `Δ ∈ a i` and all
`Δ' ∈ a j` the segments are not linked, then `(∑ i, a i).IsZelevinskySocle` holds for the
normalized product of the `π i`. The conclusion includes irreducibility of the product,
since a Zelevinsky socle is irreducible. Segments inside one `a i` may be linked. With no
blocks the statement concerns the empty product on `GL_0`.

## `TadicRectangleSoclePrime F T` (Tadić, Proposition 3.8)

Tadić p.354: "Let `d, n ∈ ℕ`, and `ρ ∈ C`. Then `⟨a(n,d)^(ρ)⟩` is a prime element of
`R`." Here `ℕ` is the positive integers (p.339) and `C` all cuspidal classes, not only
the unitary ones. `R` is the graded Grothendieck ring with the product `×` (Tadić §1);
§3.3 recalls that it is factorial (Zelevinsky, Corollary 7.5).

In Lean, `R` is the published `Aubert.gradedInductionRing F T hx hl` on the published
graded group `Aubert.GradedGrothendieckGroup F T` of actual finite-length
representations, whose multiplication is the class of the actual normalized product.
Its two hypotheses are supplied by the published proofs
`Aubert.binaryProductExactness F T` and `Aubert.gradedInductionRingLaws F T _`, so the
ring is fixed. The class of a representation `π` of `GL_N` of finite length is
`Aubert.gradedInclusion F T N (finiteLengthClass N F.Carrier π hπ)`, the homogeneous
class in degree `N`.

The statement: for every cuspidal `ρ` and `n, d > 0`, every Zelevinsky socle `π` of
`a(n,d)^ρ` on any `GL_N` and every finite-length witness `hπ`, this class is `Prime` in
Mathlib's sense (nonzero, not a unit, and dividing a product only if dividing a factor).
A Zelevinsky socle is irreducible, so a witness exists; the class does not depend on it.

## `UnitarizableSocleHermitianSymmetry F T` (Tadić, §2.1–2.4)

Tadić §2.1 (p.345): `π^+` is the Hermitian contragredient (the complex conjugate of the
contragredient); "each unitarizable admissible representation is Hermitian", i.e.
`π ≅ π^+`. §2.2: for `a = (Δ_1, …, Δ_k)`, `a^+ = (Δ_1^+, …, Δ_k^+)` with
`Δ^+ = {ρ^+ ; ρ ∈ Δ}`, and `⟨a⟩^+ = ⟨a^+⟩`. §2.3: every cuspidal `ρ` is `ν^α ρ_0` with
`α ∈ ℝ` and `ρ_0` unitarizable, and `ρ^+ = ν^(-α) ρ_0`. §2.4 records the resulting formula
for multisegments over a unitary `ρ`.

Combining these with the injectivity of `a ↦ ⟨a⟩` (Zelevinsky, Theorem 6.1), the
multisegment `a` of an irreducible unitarizable `π` satisfies `a^+ = a`. For a unitary
`ρ`, the Hermitian dual of `[ν^x ρ, ν^(x+l-1) ρ]` is `[ν^(-(x+l-1)) ρ, ν^(-x) ρ]`. Since
every cuspidal datum is `ν^x ρ` with `ρ` unitary, `a^+ = a` is equivalent to: for every
unitary `ρ`, every real `x` and every `l > 0`, the segments `⟨ρ.twist x, l, hl⟩` and
`⟨ρ.twist (-(x + (l - 1))), l, hl⟩` occur in `a` with the same multiplicity.

The Lean statement asserts exactly this count equality for every irreducible unitarizable
`π` on any `GL_N` and every multisegment `a` with `a.IsZelevinskySocle π`. It does not
define `ρ^+` for general cuspidal data; it only uses the unitary-base form of §2.3–2.4.
*Unitarizable* is the published `IsUnitarizable` and *irreducible* is Mathlib's
`Representation.IsIrreducible`.

## `TadicBlockReductionInputs F T` and `TadicBlockReductionFromInputs F T`

Tadić's proof of Lemma 4.8(ii) (pp.360–361) uses Bernstein's Theorem 2.5 (p.346),
Proposition 2.9 (p.350, through the set `X_(m-1)`), Proposition 3.8, the Hermitian facts
of §2, and Zelevinsky's theory. `TadicBlockReductionInputs F T` is the conjunction of

1. `BernsteinUnitaryProductIrreducibility F T` (Theorem 2.5(i), published),
2. `BernsteinShiftedHighestDerivativeUnitarity F T` (Theorem 2.5(iii), published),
3. `ComplementarySeriesUnitarity F T` (Proposition 2.9, published),
4. `UnlinkedSocleProductIrreducibility F T`,
5. `TadicRectangleSoclePrime F T`,
6. `UnitarizableSocleHermitianSymmetry F T`.

`TadicBlockReductionFromInputs F T` is the implication
`TadicBlockReductionInputs F T → TadicBlockReduction F T`. It is the reduction to be
proved for task `c6665b3d-54f6-41ac-a19d-3172cc1de886`. The planned proof does not follow
Tadić's case split into lines and Lemma 4.7: it uses the highest shifted derivative, the
factorization of `R` and the Hermitian symmetry directly for all supports at once. It does
not use Theorem 2.5(ii). Zelevinsky's Proposition 8.5 is used for the irreducibility of
the complementary products `ν^α σ × ν^(-α) σ`, `0 < |α| < 1/2`, which Proposition 2.9
requires.
