# Existence of the local-field segment socle: proof

The module
`Langlands.AllFieldBZ.Representation.Classification.SegmentSocleExistenceProof`
proves `Langlands.AllFieldBZ.Classification.SegmentSocleExistenceStatement`
as the theorem `Langlands.AllFieldBZ.Classification.segmentSocleExistence`,
for every nonarchimedean local field `F : LocalFieldPackage.{uF}` with its
topological data `T`. The universes `uF` of the field and `uV` of the
carriers of the supercuspidal representations stay independent, as in the
statement `.{uF, uV}`.

## What is proved

Let \(\Delta = [\rho, \nu^{m-1}\rho]\) be a segment (`Segment`): a cuspidal
datum \(\rho\) of rank \(r\) (an isomorphism class of irreducible
supercuspidal representations of \(\mathrm{GL}_r(F)\)) and a length
\(m \ge 1\), with members \(\nu^i\rho\) (`Segment.member`), where
\(\nu = |\det|\). Then there is a smooth representation \(\pi\) of
\(\mathrm{GL}_{mr}(F)\), with carrier in `Type (max uF uV)`, such that
`IsSegmentSocle Δ π` holds. That is, for some actual representative \(A\) of
\(\rho\):

- \(\pi\) is irreducible and has an injective intertwiner into the normalized
  upper block induction
  \(A \times \nu A \times \cdots \times \nu^{m-1} A\) (`segmentInduced Δ A`);
- every injective intertwiner from an irreducible representation into this
  induction has the same image.

This is `Langlands.Classification.IsIrreducibleSocle` for the actual
induced representation; no subrepresentation is chosen in the statement.

## The proof

1. **Members are distinct.** The private lemma `realTwist_eq_zero` shows that
   a cuspidal datum fixed by \(\nu^s\) for a real exponent \(s \in \mathbb{R}\)
   has \(s = 0\). The exponent must be real: since \(|\det|\) takes values in
   \(q^{\mathbb{Z}}\), where \(q\) is the residue cardinality, the complex
   exponent \(s = 2\pi i/\log q\) gives the trivial twist. After choosing a
   representative \(A\) of the supercuspidal class, equality of the classes
   of \(\nu^s A\) and \(A\) gives an isomorphism of supercuspidal
   representations (`SupercuspidalRep.isoClass_eq_iff`), hence an
   equivalence \(A \simeq \nu^s A\) of the underlying smooth representations.
   `Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductTwistOne.exponent_eq_zero`
   applies to this equivalence, since \(A\) is admissible and irreducible
   and \(r > 0\), and gives \(s = 0\). The theorem
   `segment_member_injective` deduces that `Δ.member` is injective: if
   \(\nu^i\rho = \nu^j\rho\), twisting both sides by \(\nu^{-j}\)
   (`CuspidalDatum.twist_twist`, `CuspidalDatum.twist_zero`) gives
   \(\nu^{i-j}\rho = \rho\), so \(i = j\).

2. **The segment product is a regular cuspidal product.** Choose a
   representative \(A\) of the beginning \(\rho\) of \(\Delta\). Let `B` be the
   block shape \((r, \dots, r)\) of \(mr\) determined by the members
   (`cuspidalShape`), and take the factors `segmentFactor Δ A i`
   \(= \nu^i A\). By `segmentFactor_isRepresentedBy`, the cuspidal datum
   of the \(i\)-th factor is the member \(\nu^i\rho\). Step 1 therefore shows
   that the cuspidal data of the factors are pairwise distinct.

3. **The unique socle.** `regularCuspidalProductSocle` (the proof of
   `RegularCuspidalProductSocleStatement`) applies to `B` and these factors,
   whose normalized product is by definition `segmentInduced Δ A`. It gives
   `HasIrreducibleSocle`: an irreducible representation \(\pi_0\), with
   carrier in the universe of the induced representation, and an injective
   intertwiner \(j\) into `segmentInduced Δ A` whose image is shared by every
   irreducible embedding.

4. **Smoothness.** The induced representation is smooth, and \(j\) is
   injective, so \(\pi_0\) is smooth (`Langlands.isSmooth_of_injective`).
   Packaging \(\pi_0\) as a smooth representation gives the required \(\pi\),
   and the representative \(A\) together with the socle relation from step 3
   witnesses `IsSegmentSocle Δ π`.

## Dependencies

- `Langlands.AllFieldBZ.Classification.regularCuspidalProductSocle`: an
  ordered normalized product of supercuspidal factors with pairwise distinct
  cuspidal data has an irreducible socle with a unique image
  (Zelevinsky 1980, Proposition 2.10).
- `Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductTwistOne.exponent_eq_zero`:
  for a real exponent \(s \in \mathbb{R}\), an irreducible admissible
  representation of \(\mathrm{GL}_r(F)\), \(r>0\), is not equivalent to its
  twist by \(|\det|^s\) unless \(s=0\). The proof compares the central
  actions of the scalar matrix \(\varpi I_r\) of a uniformizer \(\varpi\) on
  the two sides. This gives \(|\det(\varpi I_r)|^s = q^{-rs} = 1\), and hence
  \(s = 0\), because \(q > 1\), \(r > 0\) and \(s\) is real.
- `LocalFieldPackage.TopologicalData.segmentFactor`,
  `segmentFactor_isRepresentedBy`, `segmentInduced` and `IsSegmentSocle`
  from `OrderedSegmentProducts`: the actual factors \(\nu^i A\), their
  cuspidal data and the increasing-order induction.
- `Langlands.isSmooth_of_injective`: a representation with an injective
  intertwiner into a smooth representation is smooth.

The theorem depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Relation to the literature

The statement is the description of \(\langle\Delta\rangle\) as the unique
irreducible submodule of \(\rho \times \nu\rho \times \cdots \times \rho'\) in
Zelevinsky, *Induced representations of reductive p-adic groups II. On
irreducible representations of GL(n)*, Ann. Sci. ENS (4) 13 (1980), §3.1,
printed pp. 180–181 (`zelevinsky-1980-induced-ii`), which refers to
Proposition 2.10, printed p. 180. In §1.1 (printed p. 170), Zelevinsky fixes
an arbitrary nonarchimedean local field \(F\), with no restriction on its
characteristic; this is the same scope as the field package `F` with its
topological data `T`. He defines a segment as a subset \(\{\rho, \nu\rho, \dots, \rho'\}\) of the set
of cuspidal classes and applies §2, on representations of multiplicity-free
support (printed p. 176), which needs the members to be distinct. The Lean
proof derives this distinctness from the central-character argument of
step 1 and takes the socle from `regularCuspidalProductSocle`; every result
it uses is stated for an arbitrary nonarchimedean local field.
