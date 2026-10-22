# Absolute upper ramification under local reciprocity

Worker 10 authors this statement family. It compares the actual absolute
ramification construction with unit subgroups under normalized reciprocity,
and gives conductor criteria for arbitrary continuous complex
quasicharacters. These are proposition definitions, not reciprocity or
ramification proofs.

## Objects and scope

The parameters range over every prime, every `PadicField.{u} p`, and
arbitrary `T : F.TopologicalData`. The universe of the base carrier is
unrestricted. The published canonical realization supplies topological
data for every field. The supplied continuous map `r : F^x -> G_F^ab`
satisfies `GeometricProfiniteReciprocityRelation F T r`, whose conditions
are density, actual finite norm kernels, finite surjectivity, restriction
compatibility and geometric residue normalization. It assumes no unit
images or ramification compatibility. Its unconditional existence and
uniqueness are stated in the separately published profinite family.

`Ramification.Padic.absoluteUpperRamificationGroup F v` is the published
intersection of all finite Galois upper-group restriction preimages in
the actual absolute Galois group. Its finite groups come from the
integer-ring action, real ceiling lower indexing and the genuine inverse
Herbrand function, on canonical realizations. The intersection uses all
finite Galois intermediate fields, including nonabelian extensions.

`localAbelianUpperRamificationGroup F v` is the actual image of that
absolute group under `localAbelianGaloisProjection F`, the continuous
quotient by the closed commutator subgroup. It was constructed without
reciprocity or unit subgroups. Its image definition requires one absolute
automorphism satisfying all finite conditions simultaneously; it is not
defined as an independently supplied family of finite abelian images.
Identifying it with the upper group of the maximal abelian extension is
part of the mathematics behind the present statements.

The source `T.unitFiltration n` is the existing maximal-ideal-power
congruence filtration, with valuation units at level zero. It agrees
with the normalized-valuation principal-unit filtration; that comparison
is separately stated in `FiniteConductorStatement`. The actual absolute
inertia subgroup `F.absoluteInertia T` is defined by the residue action.

## Statements

`AbsoluteReciprocityInertiaImage` identifies the image of valuation units
under `r` with the image of the actual absolute inertia subgroup under
the Galois abelianization projection. It includes arbitrary base data
`T`. It is a reciprocity assertion, distinct from the arithmetic statement
that the absolute upper group at zero equals inertia.

`AbsoluteReciprocityHigherUnitImages` states, for each natural `n`,
that the actual image `r(U^n)` equals
`localAbelianUpperRamificationGroup F n`. It asserts equality of
subgroups, not merely density. Units and principal units are compact in
these finite extensions of `Q_p`, so their continuous images are closed
in the Hausdorff Galois abelianization. Level zero is retained.

`AbsoluteReciprocityRealUnitImages` gives the same equality for every
real `v >= 0`, using `U^(Nat.ceil v)`. The ceiling follows from the
left-continuous upper-numbering convention and integral jumps in finite
abelian quotients. No integer-jump assertion is made for the nonabelian
absolute filtration before projection. The upper group at a break
retains its value from the left.

`AbsoluteQuasicharacterConductorLevels` quantifies every continuous
`chi : F^x -> Complex^x`, including infinite-image and nonunitary
characters. It states

`conductor(chi) <= Nat.ceil v` if and only if
`(G_F^ab)^v <= r(ker chi)`, for `v >= 0`.

Here `r(ker chi)` is the literal subgroup image of the actual character
kernel. It is not its closure. The formula neither extends `chi` to all
of `G_F^ab` nor supplies an inverse of `r` on that entire profinite group.
The image formulation avoids requiring finite character image. Since
normalized reciprocity is injective, the unit-image formula identifies
this containment exactly with `chi` being trivial on the indicated unit
level. The already defined multiplicative conductor is the least such
principal-unit level; the original construction proves that it exists
for every continuous complex quasicharacter. At `v=0` the formula is the
unramified criterion.

`AbsoluteQuasicharacterLastUpperBreak` states that conductor `n+1` is
equivalent to failure of this containment at upper level `n` and its
validity at every real `v > n`. The strict inequality makes the right
limit explicit. Tame ramification is `n=0`; unramified characters have
conductor zero and satisfy neither side for any natural `n`. The break
is the last one detected by the character, not a last nontrivial group
of the absolute filtration. No eventual triviality of the absolute
filtration is asserted.

`AbsoluteUpperReciprocityTheorems` is exactly the conjunction of these
five propositions. The finite Artin-sum comparison remains the separate
`FiniteConductorStatement`; this pair does not redefine that conductor.
The arithmetic finite-image, inertia, left-continuity and wild-group
families are separately assigned and are not duplicated here.

## Original sources and derivations

Jean-Pierre Serre, *Local Fields*, English translation by Marvin Jay
Greenberg, GTM 67 (1979):

- IV.3, Proposition 14, printed page 74 / PDF81, gives upper-group
  compatibility with finite quotients. Remark 1, printed page 75 / PDF82,
  defines the infinite filtration by inverse limits and gives left
  continuity. The Hasse-Arf theorem on printed page 76 / PDF83 gives
  integral upper jumps in abelian finite extensions.
- XIII.4, Proposition 13 and its corollary, printed pages 197-198 /
  PDF202-203, give residue normalization and the inertia/unit comparison.
  XIV.6, Corollary 2, printed page 219 / PDF224, gives the topological
  units/inertia isomorphism and injectivity of reciprocity.
- XV.2, Theorem 1, Corollaries 1-3, and Theorem 2 with its final remark,
  printed pages 227-228 / PDF232-233, identify unit images with upper
  groups. Theorem 2 covers infinite abelian extensions; the final remark
  states equality in the usual finite-residue-field case by compactness.
  This supplies the equality, not just density, required here.

Worker 10 read these original pages, including the neighboring IV.3
page 73 / PDF80 and VI.2 pages 100-102 / PDF107-109. The absolute-group
image formulation is derived: finite quotient compatibility and
compactness identify the projection of the absolute upper group with
the inverse limit over finite abelian quotients. Combining this with
XV.2 gives the natural unit-image formula. Applying Hasse-Arf in every
finite abelian quotient gives the real ceiling formula.

The arbitrary-quasicharacter criteria are derived from that image
formula, injectivity of reciprocity, and the least unit level of
triviality. They do not assert finite Galois factorization of an arbitrary
quasicharacter. The last-break equivalence follows from the level
criterion and decreasing unit groups: nontriviality at `n` forces a
conductor larger than `n`, and all later real levels, including `n+1`,
force the upper bound `n+1`. Conversely, for each real `v > n`,
`Nat.ceil v >= n+1`.

The multiplicative conductor convention is also John Tate, *Number
theoretic background*, Corvallis Part II (1979), Section 3.2.6, printed
page 13 / PDF22, read directly: unramified conductor is zero, and otherwise
it is the least positive principal-unit level on which the character is
trivial. Serre uses arithmetic reciprocity; this project uses its inverse.
Inversion preserves subgroup images, kernel subgroups and the displayed
containment criteria, so the ramification and conductor assertions have
the same indices.

Registered originals:

- `serre-1979-local-fields`,
  `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`,
  SHA256 `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
- `tate-1979-number-theoretic-background`,
  `/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`,
  SHA256 `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.

No source-specific errata file was present at preparation.

## Dependencies and status

The direct imports `ProfiniteReciprocityStatement`, `Herbrand.Absolute`,
`HarmonicAnalysis.Conductor`, `LocalClassField.Units` and
`Galois.Local.AbsoluteDefinitions` are published. Their imported unit,
Galois, norm, residue and finite Herbrand objects are reused unchanged.
The environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Development compilation and exact inspection of
`AbsoluteUpperReciprocityTheorems` succeeded with zero errors or warnings
and confirmed that it returns `Prop`. Independent review and publication
are separate requirements. No theorem in this family is claimed as proved.
