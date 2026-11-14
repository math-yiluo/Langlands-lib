# The highest left cuspidal derivative lemma for `GL_n`: proposition target

Module `Langlands.Representation.Classification.LeftCuspidalDerivativeStatement`, namespace
`Langlands.Classification.LeftCuspidalDerivative`. The formulation was drafted by Worker 5735
for Task 5735; Worker 261 checked and documented it for Task 5909, with a source audit by
Worker 352.

This module defines actual iterated normalized products and left reducedness, proves their
elementary rank formula, and states the unproved proposition `LeftCuspidalDerivativeLemma`.
The proposition combines consequences of the highest left derivative lemma and segment Jacquet
formulas; it is not a verbatim statement of any one source.

## Objects and definitions

Fix a prime `p`, `F : PadicField.{uF} p`, `T : F.TopologicalData`, and
`A : GeneralLinear.SupercuspidalRep.{uF, max uF uV}` of `GL_d(F)`. All representations are
actual smooth complex representations with carriers in `max uF uV`. The field universe `uF`
and carrier parameter `uV` are independent.

* `powerRank d K m` is defined recursively by `powerRank d 0 m = m` and
  `powerRank d (K+1) m = d + powerRank d K m`.
  `powerRank_eq` proves `powerRank d K m = d * K + m` by induction on `K`, rewriting
  multiplication by a successor and finishing the natural-number equality with `omega`.
* For `Y` on `GL_m(F)`, `powerProduct F T A K Y` is the right-nested product
  `A × (A × ⋯ × (A × Y))` with `K` copies of `A`, on `GL_(powerRank d K m)(F)`.
  Its zero case is `Y`; its successor case applies the published functor
  `T.binaryNormalizedProductFunctor d (powerRank d K m)` to `A.obj` and the preceding
  product. The recursive rank makes these steps definitionally typed. The usual notation
  `A^K × Y` below means this construction. Transitivity of normalized induction relates it
  to a product first formed from the `K` copies of `A`.
* `LeftReduced F T A Y` means that, for every irreducible subquotient `Z` of `Y`, every
  `k`, every equality `h : d + k = m`, and every smooth representation `σ` of `GL_k(F)`,
  `Z` does not embed into
  `T.castRank h ((T.binaryNormalizedProductFunctor d k).obj (A.obj, σ))`.
  The quantifier over `σ` does not impose irreducibility or finite length.

`SmoothRep.IsSubrepresentation` is the existence of an injective intertwiner.
`SmoothRep.IsSubquotient` uses an actual subrepresentation followed by an actual quotient,
up to isomorphism. `T.castRank` is transport along the supplied equality of natural-number
ranks. Thus all embedding assertions concern representations, rather than only their classes
in a Grothendieck group. `HasFiniteLength` means composition length of the representation
as a group-algebra module, not finite dimension of its underlying vector space.

For positive `d`, `m ≥ d` and finite-length `Y`, this definition agrees with left `A`-reducedness
defined by the absence of `A ⊠ τ` among the constituents of the normalized upper Jacquet
module with Levi `GL_d × GL_(m-d)`. Exactness reduces to irreducible constituents of `Y`.
For an irreducible constituent, cuspidal-support block decomposition and first adjointness
convert such a Jacquet constituent into an embedding into `A × τ'`; the first factor
remains `A`, since its cuspidal support is the singleton `{A}`. Conversely an embedding
into `A × σ` gives a nonzero map from that Jacquet module, hence a constituent with first
factor `A`. See Mínguez [M09], §3, the block decomposition preceding Proposition `JA`
and that proposition's proof, and the reducedness definition in Lapid–Mínguez [LM16], §1.2.
This is a mathematical explanation of the definition, not an additional proved Lean theorem.

If `m < d`, there is no equality `d + k = m`, so reducedness holds automatically.
For positive `d` and `m = d`, it says precisely that `A` is not an irreducible subquotient
of `Y`. Zero-rank factors in the binary product are retained tensor factors.

## The target `LeftCuspidalDerivativeLemma`

The definition returns `Prop` and universally quantifies over every prime, field, topological
datum, natural-number rank `d`, and actual supercuspidal `A` above. Its five conjuncts are:

1. **Subquotients.** If `Y` has finite length, `Y'` is a subquotient of `Y`, and `Y` is
   left `A`-reduced, then `Y'` is left `A`-reduced.
2. **Products.** If `Y₁` and `Y₂` have finite length and are left `A`-reduced, then their
   binary normalized product is left `A`-reduced.
3. **Comparison.** Let `π` be irreducible on `GL_(powerRank d K m)(F)`, let `Y` have finite
   length and be left `A`-reduced on `GL_m(F)`, and let `S` be irreducible on `GL_m(F)`.
   Assume every irreducible subrepresentation of `Y` is isomorphic to `S`.
   If `π` embeds into `powerProduct F T A K Y`, then it embeds into
   `powerProduct F T A K S`.
4. **Uniqueness.** If `S` is irreducible and left `A`-reduced, any two irreducible
   subrepresentations of `powerProduct F T A K S` are isomorphic.
5. **Segments.** Let `κ : T.CuspidalDatum` have `hκ : κ.rank = d` and be represented by
   `hκ ▸ A`. For a segment `Δ` and a representation `π` of `GL_(Δ.degree)(F)`,
   `T.IsSegmentHead Δ π` and `Δ.last ≠ κ` imply that `π` is left `A`-reduced;
   `T.IsSegmentSocle Δ π` and `Δ.base ≠ κ` imply the same.

There is no multiplicity-one assumption on `S` in `Y` in clause 3. Clause 4 asserts
uniqueness of the isomorphism class, without separately asserting existence or multiplicity
one. No highest-derivative existence assertion is included. These are the five clauses of
Task 5909 revision 3. None is proved or assumed by this module.

## Source correspondence and derived content

Jantzen [J07], Definition 2.1.1 and Lemma 2.1.2 (printed pp.54–55), isolates the maximal
initial cuspidal-support factor of an irreducible representation. For a singleton set, it
gives an embedding into `A^K × D` with irreducible reduced `D`, determines the maximal
Jacquet term, and gives a unique irreducible subrepresentation of that induced product.
Jantzen states the result for representations on one cuspidal line. Lapid–Mínguez [LM16],
§1.2, Lemma 1.1 (retained manuscript p.6), explicitly states the arbitrary-support version
and explains that Jantzen's proof works in that setting. The present target imposes no
one-line restriction; this extension is part of its provenance.

Clause 1 follows from transitivity of subquotients in the chosen definition of reducedness.
Clause 2 is [LM16], §1.2, Lemma 1.2(1) (retained manuscript p.6), the reduced-product
consequence of the geometric lemma. The right-nested product and its rank bookkeeping are
internal constructions using the Library's actual normalized induction functor.

Clause 4 is a consequence of the highest derivative lemma and the reduced-factor
multiplicity computation: for irreducible reduced `S`, the relevant term of the Jacquet
module of `A^K × S` is `A^K ⊠ S` with multiplicity one. First adjointness and exactness
then give uniqueness. Compare [J07], Lemma 2.1.2 and its proof, [M09], §2, Lemma `mult1`,
and [LM16], Lemma 1.2(2) and §1.3, Lemma 1.5 (retained manuscript p.7).

Clause 3 is a derived version for a finite-length representation with homogeneous socle.
Its hypothesis permits repeated copies of `S` and self-extensions, beyond the usual
comparison with a supplied socle-irreducible representation in [LM16], Lemma 1.5.
Its justification uses the highest derivative lemma rather than applying that
multiplicity-one comparison directly. The geometric lemma and reducedness of `Y` force
the highest left `A`-order of an irreducible subrepresentation of `A^K × Y` to be `K`.
Its highest Jacquet block has just the factor `A^K ⊠ D`, with multiplicity one, for
irreducible reduced `D`, so this block is itself irreducible. The nonzero adjunction map
to `A^K ⊠ Y` restricts nontrivially to it by the finite-length cuspidal-support block
decomposition, and is injective on that irreducible source. Tensor-factor comparison
using Schur's lemma gives an embedding `D ↪ Y`. The hypothesis on irreducible
subrepresentations gives `D ≅ S`, and the highest derivative embedding gives the required
`π ↪ A^K × S`. This explains the derived formulation and adds no premise
or Lean proof.

Clause 5 uses Zelevinsky [Z80], Proposition 3.4 (printed pp.181–182) for segment socles
and Proposition 9.5 (printed p.198) for segment heads. The Library uses the increasing
upper-normalized product of a segment's cuspidals: its irreducible subrepresentation is
`IsSegmentSocle` (Zelevinsky's `⟨Δ⟩`), and its irreducible quotient is `IsSegmentHead`
(his `⟨Δ⟩ᵗ`). The formulas show that a supercuspidal first Jacquet factor can only be
the base for the socle and the last term for the head. First factors of a different rank
give zero Jacquet modules or longer, noncuspidal segment factors. Combined with the
reducedness interpretation above, these are exactly the asserted endpoint exclusions.

The Lean quantifier includes `d = 0`, since `SupercuspidalRep` itself does not require
positive rank. This boundary case is internal to the Library formulation, beyond the
positive-rank source convention. An irreducible complex representation of `GL_0` is the
one-dimensional trivial representation, and its binary product with `Y` is isomorphic to
`Y`. Consequently a finite-length left `A`-reduced `Y` must be zero. Clauses 1–3 then
reduce to zero cases, clause 4 has no irreducible reduced `S`, and clause 5 has no such
`κ`, whose rank is positive. Also, `K = 0` gives the literal representation `Y` and the
comparison reduces to its displayed hypothesis on irreducible subrepresentations.

## References

* [J07] C. Jantzen, *Jacquet modules of p-adic general linear groups*, Representation
  Theory 11 (2007), 45–83. Registered source `jantzen-2007-jacquet-gln`;
  `Jantzen--Jacquet modules of p-adic general linear groups--2007.pdf`,
  Definition 2.1.1 and Lemma 2.1.2, printed pp.54–55.
* [M09] A. Mínguez, *Sur l'irréductibilité d'une induite parabolique*, Journal für die reine
  und angewandte Mathematik 629 (2009), 107–131. Registered source
  `minguez-2009-irreductibilite-induite`; retained publication folder, file `0709.3194.tex`,
  §2 Lemma `mult1` and §3 Proposition `JA` with the preceding block decomposition.
* [LM16] E. Lapid and A. Mínguez, *On parabolic induction on inner forms of the general
  linear group over a non-archimedean local field*, Selecta Mathematica (N.S.) 22 (2016),
  2347–2400. Registered source `lapid-minguez-2016-parabolic-inner-forms`; retained
  57-page manuscript PDF, §1.2 reducedness and Lemmas 1.1–1.2, pp.5–6, and §1.3
  Lemma 1.5, p.7. These are the manuscript's actual section numbers.
* [Z80] A. V. Zelevinsky, *Induced representations of reductive p-adic groups II.
  On irreducible representations of GL(n)*, Annales scientifiques de l'École Normale
  Supérieure (4) 13 (1980), 165–210. Registered source `zelevinsky-1980-induced-ii`;
  retained PDF, Propositions 3.4 and 9.5, printed pp.181–182 and 198.
