# Strict L2 decay for one exactly extracted normalized coefficient

Author: Worker 580.

`Langlands.GLExtractedCoefficientL2ObstructionStatement.{uF,uV}` is a closed
Prop-valued definition. It states an analytic obstruction for a single actual
smooth matrix coefficient. The module contains no proof.

## Quantifiers and assertion

The statement quantifies over every prime `p`, every `F : PadicField.{uF} p`,
every supplied `T : F.TopologicalData`, every positive rank `n`, and every
complex module `V : Type uV`. The universes `uF` and `uV` are independent.
The actual representation
`ρ : Representation ℂ (GeneralLinear n F.Carrier) V` is assumed smooth for
the topology of `T`. The carrier has no topology or dimension assumption.

For every `c : UnitaryCentralCharacter ρ`, the space of integration is the
actual quotient

```
Q = GeneralLinear n F.Carrier ⧸ Subgroup.center (GeneralLinear n F.Carrier).
```

Every measurable structure on `Q` satisfying `BorelSpace Q`, and every Haar
measure `μ` for that structure, is quantified. The quotient topology comes
from the same supplied `T`. The datum `c` has its existing meaning: an
open-kernel unitary character of the full group center, with a proof that
the center acts through that character. Its published `coefficientNorm`
descends the absolute value of the actual coefficient to `Q`.

Choose any standard ordered block shape `B`, a homomorphism
`χ : (Fin B.length → F.Carrierˣ) →* ℂˣ` with open kernel, `v : V`,
`ℓ : SmoothDual ρ`, and `ε : ℝ` with `0 < ε ≤ 1`. Assume the exact equality

```
ℓ.1 (ρ (B.leviEmbedding F.Carrier (B.blockScalarLevi F.Carrier b)) v)
  = (T.leviHalfModulus B (B.blockScalarLevi F.Carrier b) : ℂ) * (χ b : ℂ)
```

for every tuple `b` satisfying

```
T.normalizedAbs ((b i : F.Carrier) / (b j : F.Carrier)) < ε  for all i < j.
```

These are strict inequalities on every forward block ratio. The identity
holds throughout that deep chamber, with coefficient of `χ` equal to one,
and permits arbitrary common scalar multiplication of all coordinates.
It is specific data about this coefficient. There is no Jacquet-exponent
hypothesis.

If `MeasureTheory.MemLp (c.coefficientNorm ℓ.1 v) 2 μ`, then every tuple `a`
with monotone normalized absolute values and at least two unequal such
values satisfies `‖(χ a : ℂ)‖ < 1`. Thus the conclusion includes boundary
directions of the closed chamber, where some consecutive absolute values
may be equal. When `B.length = 1`, the unequal-values hypothesis is
impossible; the conclusion is vacuous. The deep-chamber identity in that
case still ranges over every scalar tuple.

Only smoothness of `ρ` is assumed. There is no admissibility, finite length,
irreducibility, nonzero-carrier, finite-dimensionality, supplied fixing
subgroup, cell-volume estimate, cell-disjointness certificate, or assumed
spectral or exponent criterion. The identity itself forces the chosen
coefficient to be nonzero on its nonempty deep chamber. The statement
requires L2 membership of this one coefficient, rather than of every
coefficient of `ρ`.

## Source and derived provenance

W. Casselman, *Introduction to the theory of admissible representations of
p-adic reductive groups*, draft of 1 May 1995:

- Literature ID: `casselman-1995-admissible-representations`.
- SHA256:
  `78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`.
- Retained original:
  `/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Introduction to the theory of admissible representations of p-adic reductive groups--1995.pdf`.
- Printed and one-based PDF pages coincide.

The relevant passages were read: the central-quotient Cartan geometry in
§1.4, p.15; the modulus and double-coset volume argument in Lemma 1.5.1
and Proposition 1.5.2, p.16; the chamber decomposition in §4.3,
pp.42–43; and the lattice summability discussion in §4.4,
pp.43–45. In particular, Lemma 4.4.3 and Proposition 4.4.4 isolate strict
character decay, Corollary 4.4.5 introduces the inverse-volume modulus,
and Theorem 4.4.6 specializes the resulting condition to square
integrability. The formulas on pp.16 and 44 were checked in page images.
No applicable project errata entry was found in the bounded filename search.

This precise statement is a derived specialization to one exact exponential
coefficient on `GL_n`, not a verbatim theorem of the source. The extraction
identity replaces all spectral extraction and admissibility arguments.
Casselman's unnormalized exponential is here `δ_B^(1/2) χ`, so the
`δ^(-1/2)` factor at p = 2 leaves exactly the normalized character `χ`.
For an upper block-scalar matrix,

```
δ_B(b) = ∏_(i<j) |b_i/b_j|^(B.size i * B.size j).
```

This also equals the minimal upper-Borel modulus on that matrix: the roots
within a block have ratio one. The Library half modulus is the positive
complex square root of this explicit positive character.

As a source comparison, Waldspurger 2003, §III.1, Proposition III.1.1
and Corollary III.1.2, pp.263–264, were read in the retained original
`/home/taskhub/central-library/Waldspurger--La formule de Plancherel pour les groupes p-adiques d'apres Harish-Chandra--2003.pdf`
(literature ID `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`;
one-based PDF page is printed page minus 234). No applicable project errata
entry was found. The strict exponent criterion there is not an input to
this adapter; the decay estimate in its corollary already uses square
integrability through that criterion and cannot replace the independent
lower-bound argument below.

## Independent route required of a future proof

The following is a mathematical derivation plan, not an implemented Lean
proof or a list of extra premises.

1. **A common fixing subgroup.** Smoothness gives an open stabilizing
   subgroup for `v`. Membership of `ℓ` in the actual smooth dual gives
   one for `ℓ` under the contragredient action. Intersect them with the
   standard integral compact open subgroup `K = GL_n(O_F)` and choose
   a compact open subgroup `H` in the intersection. Inverse stability of
   `H` converts dual fixedness into left invariance of the coefficient;
   fixedness of `v` gives right invariance. Thus the coefficient norm
   is constant on the quotient images of `H g H`. All compactness,
   openness and continuity facts here must be proved or imported from
   proved Library results. In particular, the arbitrary-function
   local-constancy footnote in Corollary 4.4.5 is not invoked as an
   automatic property of an arbitrary function.

2. **Compact units and central compatibility.** The open-kernel condition
   makes `χ` locally constant and continuous. On the compact group of
   coordinatewise valuation units its image is finite, since the quotient
   by its open kernel is discrete. Hence its complex norm is one there.
   Coordinatewise uniformizer decompositions can therefore remove the
   unit factors without changing character norms. Also evaluate the
   assumed identity at a fixed deep tuple and its product with an
   arbitrary common scalar tuple. The embedded common scalar is an
   actual central scalar matrix; `c.acts` and the triviality of the
   modulus on scalars show that `χ` has norm one on this direction.
   Cancellation is valid because the coefficient supplied by the identity
   is nonzero. These scalar and valuation identifications are proof
   obligations, not character hypotheses added to the target.

3. **A deep ray and distinct normalized tuples.** If a closed-chamber
   tuple `a` violates the conclusion, its norm is at least one. Replace
   its coordinates by uniformizer powers with the same valuations,
   then remove a common power. This gives a nonconstant, antitone,
   nonnegative block valuation vector with last coordinate zero and the
   same character norm as `a`. Choose a fixed tuple `b₀` of uniformizer
   powers with every forward ratio below `ε`. Multiplication by successive
   powers of the normalized direction preserves these strict inequalities,
   even along walls. Thus the identity applies to each tuple `b₀ d^m`.
   Repeat each block valuation `B.size i` times and normalize by a
   common shift to obtain actual `CartanQuotient.Normalized` diagonal
   tuples `λ_m`. Positivity of all block sizes and nonconstancy of the
   direction make these tuples pairwise distinct. Common shifts leave
   the central-quotient point and its coefficient norm unchanged.

4. **Actual measurable disjoint cells and volume.** Let `s_m` be
   `CartanQuotient.subgroupCell T H λ_m`, the image of the actual
   double cell `H representative(λ_m) H` in `GL_n(F)/Z`. Compactness
   and continuity, with the Hausdorff quotient topology, give measurable
   cells. Since `H ≤ K`, each lies in its corresponding `K`-Cartan
   cell. Uniqueness of normalized elementary divisors modulo common
   shifts gives disjointness for distinct `λ_m`. The quotient Haar
   version of the lower estimate in Proposition 1.5.2 supplies a fixed
   `C > 0` with
   `μ(s_m) ≥ C δ_B(b₀ d^m)^(-1)`.
   This requires a proof on the actual quotient and the chosen Haar
   measure, including positivity and finiteness on compact open sets.
   The explicit upper block modulus must be identified with the relevant
   Haar scaling and with `CartanQuotient.delta T λ_m`. A volume
   statement alone is not such a proof.

5. **The p = 2 cancellation and divergence.** On `s_m` the descended
   norm equals
   `δ_B(b₀ d^m)^(1/2) ‖χ(b₀)‖ ‖χ(d)‖^m`.
   The square of this value times the cell volume is at least
   `C ‖χ(b₀)‖² ‖χ(a)‖^(2m)`.
   Its constant factor is strictly positive, and the geometric ratio
   is at least one. The weighted sum over `m : ℕ` is therefore infinite.
   Apply the published `Langlands.countableCellLpLower` at exponent two
   to these measurable disjoint cells and their constant lower values:
   the assumed `MemLp` instead makes that sum finite. The future proof
   must supply all conversions between nonnegative real values and
   `ℝ≥0∞`, the `p.toReal = 2` exponent identity, positivity, and the
   divergence argument. No covering by the small cells is required.

The analytic input `countableCellLpLower` is present in
`Langlands.Analysis.CountableCellLpProof`; its implementation is the
disjoint-union lower integral estimate and uses no exponent criterion.
`Langlands.Representation.MatrixCoefficient.NormRegularityProof`
proves continuity and almost-everywhere strong measurability of the
descended norm from a smooth vector. Its direct proof uses quotient
continuity and local constancy of the actual coefficient. These are
available elementary results to audit and reuse in the separate proof.
Neither they nor the geometric proof obligations are premises of this
statement.

## Imports, independence and proof boundary

The direct imports supply existing block-scalar embeddings, the explicit
positive block modulus, the actual smooth dual, and the actual coefficient
norm modulo the center. No existing imported Lean/Markdown pair is changed.
The statement does not import a Jacquet-exponent predicate or a classification
criterion. The separate extraction theorem can eventually supply its
identity when assembling the parent strict criterion.

The future proof must remain independent of the strict square-integrable
exponent criterion and of segment analytic classification, multisegment
special-head exhaustion, ordered special-head existence, quotient
coverage for classification, tempered block uniqueness,
`SquareIntegrableLanglandsClassification`, square-integrable exhaustion,
and regular exhaustion, including their proof successors and transitive
dependencies. Pending geometry or extraction tasks and published statements
are navigation pointers, not proved inputs. Shared geometry and measure
owners must be checked before splitting any lower proof work.

This contribution publishes only the proposition. Its exact proof successor
is to be published separately after this target is in the Library.
