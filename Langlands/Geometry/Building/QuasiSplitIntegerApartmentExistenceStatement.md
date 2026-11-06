# Actual quasi-split apartment existence

`Langlands.Geometry.Building.QuasiSplitIntegerApartmentExistenceStatement`
is an unproved proposition requesting the initial actual apartment data. It
quantifies over every universe `u`, a field `k : Type u`, a surjective valuation
`v : Valuation k (WithZero (Multiplicative ℤ))`, and henselianity of
`v.valuationSubring`. For each actual quasi-split group `G/k` with its affine
structure and each prescribed actual maximal split torus `i : S → G`, it
requests the following objects.

- `D : KPApartmentData i (IntegerValuation.order v)`. Its carrier is a
  nonempty equipollence class of functions on the actual rational root groups
  `rootGroupPoints i a`, satisfying V0–V5 of KP Definition 6.1.2 and the
  split-torus part of V6. The class is stable under the actual normalizer
  points and their existing action.
- `C : CentralizerDatum i`, representing the actual torus centralizer
  `Z_G(S)`, with its closed inclusion, the factorization of `i`, and the
  bijective real restriction-evaluation map needed for the centralizer
  valuation.
- `IntegerValuation.IsOmegaCompatible v D C`, the full V6 identity on
  every valuation of this class and all rational points of this centralizer.
  Its translation is the negative of the positive character valuation
  defined using `IntegerValuation.order v`.

The torus is supplied as an algebraic object; none of the apartment,
root-coordinate system, valuation family, centralizer representation or
compatibility witnesses is a premise. `IsQuasiSplit G` includes connected
reductivity and an actual field-defined geometric Borel. The monomorphism
instance for `i` is deduced from its maximal split torus hypothesis. No
topology on `k`, perfectness of its residue field, completeness, residue
cardinality bound or characteristic restriction is assumed. In particular,
this target is formulated for the henselian maximal unramified field as
well as for local fields.

This interface requests initial apartment data. It does not request V7,
an affine root system axiom package, AS5, parahoric zero subgroups, an
unramified descent construction, or any building or metric axiom. Those
are additional obligations when constructing the building. This file
proves no existence assertion.

## Source correspondence and provenance

This is a derived interface packaging the apartment-existence consequences of
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Chapter 6,
opening paragraphs (printed pp.195–196, PDF226–227), Construction 6.1.17
and Proposition 6.1.19 (printed pp.205–207, PDF236–238), Definition 6.1.24,
§6.1(c), Definition 6.1.27 and Lemma 6.1.28 (printed pp.209–210,
PDF240–241). The source uses a henselian field with discrete valuation
normalized to have value group `ℤ`; surjectivity of `v` expresses this
normalization in the Library's multiplicative encoding. The R1 branch
uses additive root coordinates over a finite extension. The R2 branch
uses the quadratic unitary root coordinates and the value
`ω(v)/2`; root coordinates and the valuation axioms must be constructed
in any proof of this target.

The full centralizer law is V6 of Definition 6.1.2 (printed p.199,
PDF230), with the character-valuation description in §2.6(d),
(2.6.3)–(2.6.4) (printed pp.102–103, PDF133–134). The
`CentralizerDatum` fields express its actual centralizer and rational
character identifications. For quasi-split groups this centralizer is a
maximal torus; the usual character restriction identification gives the
real restriction-evaluation isomorphism. These algebraic identifications
remain part of the requested existence proof, not supplied hypotheses.

The authors' *Corrections and additions* (2024), PDF25, corrects (2.6.3)
to the positive character valuation; the apartment translation here is
its negative. PDF32 corrects the fusion signs in Lemma 6.1.12 and
replaces the derived-group construction in §6.1(c) and Definition 6.1.27
by the adjoint-group construction using `Gad` and `Sad`. That corrected
route underlies the reductive scope of this interface. PDF33 retains
AS5 as an additional standing premise for Chapter 7; it is not claimed
by this target.

The registered sources are `kaletha-prasad-2023-bruhat-tits-new-approach`,
SHA256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`,
and `kaletha-prasad-2024-corrections`, SHA256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
