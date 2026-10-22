# Unitary generic classification of GL_n

Authors: Worker 62 (Lean statements and source reading), Worker 69 (collaborative
source and dependency audit). This pair states construction, exhaustion and
unordered uniqueness. It proves none of these assertions and assumes no
classification theorem in a constructor or axiom.

## Objects and conventions

Fix a prime `p`, a finite extension `F : PadicField.{uF} p`, and compatible
topological data `T`. Representation carriers lie in `Type (max uF uV)`.
The actual induction carrier has the same universe, so exhaustion does not
require representatives in an arbitrarily smaller universe. There is no
finite-dimensionality assumption on the representation carrier.

The total rank is `n + 1`, for arbitrary `n : ℕ`, including rank one.
`B : GeneralLinear.BlockShape (n + 1)` supplies a finite index set, strictly
positive ranks `B.size i`, and the equality of their sum with `n + 1`.
Consequently the block family is nonempty. Blocks are actual smooth complex
representations of `GL_(B.size i)(F)`, not labels for representations.

`T.twistedProductInduced B δ s` is normalized induction of the actual external
tensor product of `ν^(s i) δ_i`, inflated to the standard upper block parabolic.
Here `ν = |det|_F`, with `|ϖ|_F = q^(-1)`. Its covariance is
`f(pg) = δ_P(p)^(1/2) σ(p) f(g)` and its group action is right translation.
This is the published `LanglandsData` construction; BZ77 §§1.8–1.9,
pp.444–445, supplies the normalization and transitivity conventions.

`IsUnitarizable ρ` means `Nonempty (InvariantPositiveForm ρ)`: an actual
positive definite invariant Hermitian form. It is not merely a unitary
central character. `T.IsSquareIntegrable ρ` is the published analytic predicate
using admissibility, a unitary scalar central character, and square-integrable
absolute smooth matrix coefficients on the actual central quotient, for all
Borel Haar measures. The Library proves existence of these measures.
`Whittaker.IsGeneric ψ n ρ` includes irreducibility, admissibility, and an actual
nonzero linear functional transforming by `u ↦ ψ(∑ᵢ uᵢ,ᵢ₊₁)` on the upper
unipotent subgroup. `UnitaryAdditiveCharacter` includes continuity and
nontriviality. Genericity is asserted for every such character.

## Parameter predicates

All new names below are in `Langlands.Classification`.

| Declaration | Meaning |
| --- | --- |
| `IsUnitarySquareIntegrableBlockFamily F T B δ` | Every actual block is irreducible, unitarizable and analytically square-integrable. |
| `HasStrictUnitaryExponents s` | For each index, `-(1/2 : ℝ) < s i` and `s i < (1/2 : ℝ)`. Both endpoints are excluded. |
| `SameUnorderedUnitaryParameters F T B C δ ε s t` | There are a bijection `e : Fin B.length ≃ Fin C.length` and equalities `h i : B.size i = C.size (e i)` such that `s i = t (e i)` and `Nonempty ((h i ▸ δ i) ≅ ε (e i))` for every index. |
| `HasHermitianSymmetricParameters F T B δ s` | The preceding matching relation holds between `(B, δ, s)` and `(B, δ, -s)`. |
| `IsUnitaryGenericDatum F T B δ s` | Conjunction of the block conditions, strict bounds, and Hermitian parameter symmetry. The rank constraints come from `B`. |

These are concrete predicates on actual data. Category isomorphisms are
invertible equivariant complex-linear maps. Rank transport changes the group
index along the specified equality; it does not require equality of carrier
types. A bijection preserves every multiplicity, including repetitions of a
block with exponent zero. For sign symmetry it says `s i = -s (e i)`,
equivalently `s (e i) = -s i`. No involutive matching is required.

Ta86 §2.1, p.345, defines the Hermitian contragredient as the conjugate of the
smooth contragredient: the conjugate scalar structure is
`λ ⋅ v = conjugate(λ) v`. For a unitarizable admissible `δ`, its Hermitian dual
is isomorphic to `δ`. Thus Ta86 §5.5, p.362, gives
`(ν^s δ)^+ ≅ ν^(-s) δ`. Ordinary smooth contragredience instead gives
`(ν^s δ)^∨ ≅ ν^(-s) δ^∨`. The symmetry predicate uses the first formula and
places **no ordinary self-duality condition** on `δ`. The actual semilinear
Hermitian-dual bridge and twist/dual/central-character statements are the
separate compatibility installment; this predicate does not purport to
construct or prove that bridge.

## Classification clauses and source correspondence

| Declaration | Exact assertion | Original source and derivation |
| --- | --- | --- |
| `UnitaryGenericConstruction F T` | For every valid family, the actual twisted normalized induction is unitarizable and generic for every `ψ`, hence irreducible and admissible. | Ta86 Theorem D(i), pp.338–339, with `u(δ,1)=δ` and opposite-exponent complementary-series pairs; genericity is the specialization explained below using Ze80 Theorem 8.1, Corollary 8.3, Theorem 9.7 and §9.10, and BZ77 §§4.5–4.7. |
| `UnitaryGenericExhaustion F T` | Each generic unitarizable actual representation of rank `n+1` is isomorphic to the induction of some valid family. | Ta86 Theorem D(ii) and the generic Speh elimination below; H00 Appendix A.2, p.453, records precisely the strict interval and multiplicity-preserving Hermitian symmetry in this application. |
| `UnitaryGenericParameterUniqueness F T` | For two valid families of the same positive total rank, their actual induced representations are isomorphic if and only if the unordered parameter matching predicate holds. | Ze80 Theorem 9.7(b), pp.198–199, and §9.10, p.201; Ta86 §§5.3–5.4, p.362; H02 §2.8, p.596, for unique real exponent/unitary normalization and genuine multiset uniqueness. Ta86 Theorem D also gives permutation uniqueness for its unitary building blocks. |

`UnitaryGenericTheorems F T` conjoins the three clauses.
`PadicUnitaryGenericTheorems.{uF,uV}` universally quantifies that conjunction
over every prime, every finite p-adic extension and every compatible topology.
There are no theorem-valued input hypotheses. The uniqueness reverse implication
includes independence of the ordering and of the chosen block representatives.
The assertion is specific to GL_n.

## Generic specialization and provenance

The generic specialization is a derivation from the cited originals, not a
separately numbered theorem in Ta86. Ta86 Theorem D uses Speh blocks `u(δ,k)`
and paired products `ν^α u(δ,k) × ν^(-α) u(δ,k)` with `0 < α < 1/2`.
Ta86 §7.4, p.370, identifies `u(δ_d(ρ),k)` with `L(a(k,d)^(ρ))`;
Appendix A.10(iii), p.377, identifies this with the Zelevinsky representation
`⟨a(d,k)^(ρ)⟩`. Its Zelevinsky segments have length `k`.
Ze80 Theorem 8.1 and §9.10 say that a Zelevinsky representation is
nondegenerate exactly when all those segments are singletons. Corollary 8.3
compares the derivative with the Whittaker realization. Consequently the
Speh factor is generic exactly for `k = 1`.

BZ77 Lemma 4.5 and Corollary 4.6, p.455, give the derivative filtration and
multiplicativity: a product containing a factor with zero top derivative
has zero top derivative. This supplies the necessary elimination of `k > 1`
from a generic product in Ta86; irreducibility by itself would not supply it.
The remaining factors are unitary square-integrable blocks with exponent zero,
and opposite-exponent pairs with `0 < α < 1/2`. Conversely, finite sign
symmetry lets one group any valid family into exactly such pairs and zero
factors. Ta86 gives irreducibility and unitarizability of the resulting
product, while the derivative and Whittaker results give genericity.
Permutation and induction-transitivity comparisons remain proof obligations.

Ze80 §9.1, p.197, defines the special representation as the quotient of
**increasing** cuspidal twists (equivalently the subrepresentation of the
reversed decreasing product). This differs from the Zelevinsky segment socle
convention. Ta86's Speh quotient uses decreasing centered square-integrable
blocks, so it must not be mistaken for that increasing special quotient.
The rectangular-parameter identity above provides the needed translation.
No special or Speh representation is introduced as an assumed constructor.

H02 §§2.8–2.9 describes the multiset Langlands classification and its use to
assemble the full correspondence. Section 2.9 is an application and not an
additional proof of the unitary generic classification. Unique real unitary
normalization turns uniqueness of the essentially square-integrable factors
into simultaneous uniqueness of `s_i` and the isomorphism class of `δ_i`.
The predicates here implement this uniqueness on actual representatives.

## Published interfaces and outstanding dependencies

The pair was developed against Library commit
`9bcf0d658a507ac3b07db1ef643b50bd98c4bcff`. The following exact published Lean
names identify its construction dependencies at that version:

| Module below `Langlands.Representation` | Used interface |
| --- | --- |
| `Classification.LanglandsData` | `PadicField.TopologicalData.twistedProductInduced`, defined through `twistedBlocks` |
| `Classification.Tempered` | `PadicField.TopologicalData.IsSquareIntegrable` |
| `Classification.Segments` | `PadicField.TopologicalData.segmentFactor` and its determinant-power twist |
| `Induction.BlockFactors` | `PadicField.TopologicalData.normalizedProductInductionFunctor` |
| `Category.Basic` | `SmoothRep`, its actual representation and category isomorphisms |
| `Unitary.Basic` | `InvariantPositiveForm`, `IsUnitarizable` |
| `Whittaker.GeneralLinear` | `Whittaker.IsGeneric`, `standardCharacter` |

`GeneralLinear.BlockShape` supplies the positive-rank geometry and
`HarmonicAnalysis.UnitaryAdditiveCharacter` supplies the character. The direct
imports are `Classification.LanglandsData` and `Whittaker.GeneralLinear`;
there are no imports from drafts.

The proof dependency map distinguishes available statement targets from proofs:

- `Langlands.Classification.PadicSegmentSquareIntegrabilityTheorems` in
  `Classification.SegmentSquareIntegrabilityStatement` is published, first at
  `e7e1cf75d8341a5fe60f25d4e6bb64d251921cbf`, unchanged at the development base.
  In particular, `SegmentEssentialSquareIntegrableClassification`,
  `SegmentSpecialParameterUniqueness`, and
  `EssentialSquareIntegrabilityExponentUniqueness` supply the square-integrable
  parameter statements.
- `Langlands.Classification.PadicTemperedBlockTheorems` in
  `Classification.TemperedBlockStatement` is published, first at
  `2839e6bae86085a8a220122cf5eb434176a57d4c`, unchanged at the development base.
  `SquareIntegrableBlockInduction`, `SquareIntegrableBlockGenericity`,
  `TemperedBlockExhaustion`, and `TemperedBlockUniqueness` describe the
  zero-exponent case. They are statement definitions, not established proofs.
- At this base, the separate full multisegment classification and
  segment-product genericity installments have no published statement names.
  Their required content is respectively actual unordered multisegment
  classification, and special-product nondegeneracy/nonlinkage,
  generic exhaustion/uniqueness, and the singleton-segment criterion.
  These remain explicit proof prerequisites. The published relations
  `Multisegment.IsLanglandsHead` and `Multisegment.IsZelevinskySocle` do not
  establish any of those assertions.
- The separate unitary generic compatibility installment supplies actual
  Hermitian-dual, ordinary-dual, determinant-twist and scalar-central-character
  clauses for these construction parameters. Its publication remains a
  requirement of the surrounding assignment; this focused pair covers the
  three classification clauses only.

Ta86 p.339 notes a then-unpublished involution input used in its main argument.
Its Appendix pp.371–380 supplies a characteristic-zero route, applicable to
these p-adic fields, without assuming that general conjecture. The Appendix
uses deep globalization and residual-spectrum results, which are not proved
here and whose upstream originals are not claimed to have been read in this
installment. Ze80 §9.3 explicitly omits Bernstein's square-integrability
converse proof; the separate square-integrability source audit retains that
boundary. Ze80 §9.10 also omits an elementary combinatorial lemma proof.

Further proof obligations include derivative exactness and product filtration,
the derivative/Whittaker comparison and character independence, analytic
unitary induction and complementary series, the classification and exponent
uniqueness results, and the finite matching/permutation isomorphisms. Comparing
the analytic square-integrability predicate with a source using one Haar
measure uses uniqueness of Haar measure up to positive scalar. None of these
obligations is discharged by defining the present propositions.

## Retained original sources

All five originals were already registered. Their exact bytes were rehashed
for this submission. No source-specific errata note was present in the
current Library. Readings below are selected passages, not full-paper claims.

- **Ta86**: M. Tadic, *Classification of unitary representations in irreducible
  representations of general linear group (non-archimedean case)*, Ann. Sci.
  ENS (4) 19 (1986), 335–382. Read Theorem D, §§2.1–2.4, §§5.1–5.6,
  §7.4 and the Appendix introduction and relevant A.8–A.12 passages.
  Visually checked pp.345, 362–363 and 377.
  ID `tadic-1986-unitary`;
  SHA-256 `08e4e1e7c1ccc1e340999287867bc0448f3d8f4bab49906fbf1deda866ae4683`.
- **Ze80**: A. V. Zelevinsky, *Induced representations of reductive p-adic
  groups II. On irreducible representations of GL(n)*, Ann. Sci. ENS (4)
  13 (1980), 165–210. Read Theorem 8.1, Corollary 8.3, §§9.1–9.7 and 9.10,
  pp.195–199, 201 (PDF pp.32–36, 38).
  ID `zelevinsky-1980-induced-ii`;
  SHA-256 `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
- **BZ77**: I. N. Bernstein and A. V. Zelevinsky, *Induced representations of
  reductive p-adic groups I*, Ann. Sci. ENS (4) 10 (1977), 441–472.
  Read §§1.4–1.9, pp.443–445, and §§4.5–4.7, p.455 (PDF pp.4–6, 16).
  ID `bernstein-zelevinsky-1977-induced-i`;
  SHA-256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
- **H00**: G. Henniart, *Une preuve simple des conjectures de Langlands pour
  GL(n) sur un corps p-adique*, Invent. Math. 139 (2000), 439–455.
  Read Appendix A.1–A.3, pp.453–454; visually checked A.2, p.453 (PDF p.15).
  ID `henniart-2000-simple-proof`;
  SHA-256 `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
- **H02**: G. Henniart, *Une caracterisation de la correspondance de Langlands
  locale pour GL(n)*, Bull. Soc. Math. France 130 (2002), 587–602.
  Read §§2.6–2.9, pp.595–596 (PDF pp.9–10); §2.8 supplies the real exponent
  and multiset normalization, §2.9 its assembly use.
  ID `henniart-2002-characterization`;
  SHA-256 `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.
