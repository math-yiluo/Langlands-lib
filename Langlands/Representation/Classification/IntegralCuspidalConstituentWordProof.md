# Actual constituent words from supercuspidal support

Authors: Worker 320 (shared Lean proof and initial explanation), Worker 438
(target verification, dependency audit and expanded explanation).

`Langlands.Classification.integralCuspidalConstituentWord` proves exactly
`Langlands.Classification.IntegralCuspidalConstituentWord.{uF,uV} F T`.
The prime is arbitrary, the actual p-adic field and topological datum are
supplied, and the field and carrier universes remain independent. Factors
and the constituent have carriers in `Type (max uF uV)`. The positive total
rank, irreducibility, actual constituent relation and prescribed integral
twist labels are precisely the hypotheses of the published target. The
proof adds no hypotheses.

The proof first packages the original factors as cuspidal data `τ` using
the positive block sizes and actual supercuspidal classes. Their normalized
product and its given subquotient witness give
`T.IsCuspidalConstituent τ π`. The published
`Langlands.glSupercuspidalEmbedding` supplies another ordered family `ρ`
and an actual injective intertwiner from `π` into its normalized upper
product. Its subrepresentation witness also gives a constituent witness.
`Langlands.glSupercuspidalSupportUniqueness` identifies the two multisets of
cuspidal data, including all multiplicities.

Projecting away the rank-positivity proofs gives a permutation of lists in
the dependent sum of ranks and supercuspidal classes. The input label
identities identify the second list with the image of `List.ofFn e` under
`z ↦ ⟨m, T.supercuspidalClassRealPowerTwist m (z : ℝ) A.isoClass⟩`.
Mathlib's `List.eq_map_comp_perm` lifts this permutation to a list `w` of
integer labels with `w.Perm (List.ofFn e)`. This lifting does not require
the label map to be injective and retains repeated labels. The list length
equality identifies `w.length` with the number of new factors. Indexing
`w` supplies the new exponent function `e'`; `List.ofFn_inj` gives the
rank-indexed class identity for every new factor.

Unpacking the embedding supplies the positive block shape
`T.cuspidalShape ρ hρ`, actual representatives `D i`, and the injective
intertwiner `j`. Since an irreducible representation is nonzero, injectivity
makes `j` nonzero. The published
`Langlands.CuspidalSupport.glCuspidalTensor` makes the actual external smooth
tensor of the `D i` irreducible. Applying
`Langlands.CuspidalSupport.isQuotient_normalizedJacquet_of_inductionHom`
therefore gives an actual quotient of the whole normalized upper Jacquet
module of `π` onto this tensor. That helper descends evaluation at the
identity to a nonzero Jacquet intertwiner and uses irreducibility of its
target to prove surjectivity. `SmoothRep.IsQuotient.isSubquotient` supplies
the required actual subquotient witness. Together with the recovered labels
and representative class identities, it constructs
`IntegralCuspidalJacquetWord F T m n A π w`.

The induction, external tensor and Jacquet functors in these steps are the
actual published constructions for the same supplied topology, standard
upper block parabolic, positive half-modulus normalization and right
translation. The word occurrence is an actual smooth quotient, subsequently
viewed as a subquotient.

This is an internal assembly of published support, tensor and adjunction
results followed by elementary list operations. Its source rationale is
Zelevinsky, *Induced representations of reductive p-adic groups II* (1980),
Proposition 1.10, printed p.174 / PDF p.11, registered as
`zelevinsky-1980-induced-ii`, SHA-256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
The passage asserts support uniqueness and a choice of ordering giving an
embedding, referring to Bernstein–Zelevinsky (1977), §§2.5 and 2.9. The
original passage was read and visually checked. The implemented proof uses
the published closing theorems named above and their documented lower
proofs; the integral-label interface is derived rather than a verbatim
source assertion.

The conservative project import closure contains 528 modules, including
this proof, at Library base
`e3944f764d2c00d53ac87227e98601bb667f348f`. Every existing dependency
Lean/Markdown pair and the target pair are unchanged. The closure contains
foundational segment definitions and lower support, tensor, finite-length,
Jacquet, induction and geometric-lemma results. It contains no segment
classification, multisegment exhaustion, ordered strong-head existence,
quotient coverage, tempered block uniqueness, square-integrable Langlands
classification, square-integrable exhaustion, regular exhaustion or proof
successor of these results. This theorem constructs one realizing word
per constituent; initial integral-line existence, local word moves,
segment extraction and analytic classification remain separate obligations.
