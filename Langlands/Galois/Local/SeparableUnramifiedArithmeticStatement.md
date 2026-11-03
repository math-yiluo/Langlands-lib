# Residue and valuation arithmetic of the separable inertia fixed field

Lean and statement translation: Worker 60. Target design and original-source
map: Worker 118.

This unit defines unproved arithmetic propositions over the published
`Langlands.Galois.Local.SeparableInertiaDefinitions`. Its only new proof is
the short integer-ring comparison described below. That comparison does not
prove any of the arithmetic targets.

## Objects and scope

All declarations are in `Langlands.LocalGalois.Separable`, with one arbitrary
universe `u`. The base is `F : Type u` with exactly
`[Field F] [ValuativeRel F] [TopologicalSpace F]
[IsNonarchimedeanLocalField F]`.
Write `Ω = SeparableClosure F`, `U = inertiaFixedField F`,
`v_U = fixedFieldValuation F`, and `B = fixedFieldIntegers F`.
These are the actual published separable closure, inertia fixed intermediate
field, restricted spectral valuation, and its valuation subring. They are
reused unchanged.

The four file-local instances `localNormedField F`,
`localNormedField_ultrametric F`, `localNormedField_complete F` and
`localResidue_finite F` are the published choices. The base valuation relation
and topology remain the supplied ones. The norm is the chosen rank-one norm
of `localNormedField F`; no numerical normalization is required.
There is no `CharZero F` or `PerfectField F` premise. Both mixed and equal
characteristic are covered, including imperfect positive-characteristic
base fields. The finite residue field of a nonarchimedean local field is
perfect; this does not require perfectness of `F`.

The arithmetic interpretation is that `U` is the maximal unramified extension
inside this actual `Ω`. Finite arithmetic maximality and finite Galois
exhaustion are the separate targets of
`Langlands.Galois.Local.SeparableUnramifiedStatement`. This unit imports the
published construction directly, so it has no dependency on that statement
unit or a proof of its targets.

## Exact propositions

`FixedFieldResidueIsAlgClosure F` installs exactly
`(residueToFixedField F).toAlgebra`, and asserts
`IsAlgClosure 𝓀[F] (ResidueField B)` for that algebra.
Here `𝓀[F]` is the residue field of the supplied base integer ring `𝒪[F]`.
The structure map is literally the published
`residueToFixedField F : 𝓀[F] →+* ResidueField B`, obtained by reducing
`integerToFixedField F`. This asserts both algebraicity over `𝓀[F]` and
algebraic closedness of `ResidueField B`. The injectivity needed by
`IsAlgClosure` follows from the field structure; no additional algebra
structure or algebraic-closure witness is supplied as input.
The published `residueToFixedField_localResidueEquiv` compares this map with
the canonical spectral residue algebra through `localResidueEquiv F` and
`fixedFieldIntegersEquiv F`.

`FixedFieldValuesFromBase F` states
`∀ x : U, ∃ a : F, v_U x = ‖a‖₊`.
Both sides lie in the same `NNReal` codomain. The quantifier includes `x = 0`;
there is no nonzero restriction on `x` or `a`.
Together with the published fact that the spectral valuation restricts to
this base norm, this expresses equality of the sets of values on `U` and
`F`. It is independent of a numerical normalization.

`FixedFieldIntrinsicDiscrete F` explicitly installs the valuation relation
`ValuativeRel.ofValuation (fixedFieldValued F).v` on `U` and asserts
`ValuativeRel.IsDiscrete U` for that relation. By definition
`fixedFieldValued F = Valued.mk' v_U`, so this relation is
`x ≤ᵥ y ↔ v_U x ≤ v_U y`.
The proposition concerns its intrinsic `ValueGroupWithZero U`: it has a
maximal element below one in the sense of Mathlib's `IsDiscrete`.
It makes no discreteness assertion about the entire `NNReal` codomain.

The theorem `fixedFieldIntrinsicIntegers_eq` uses this same explicit relation
and proves
`(ValuativeRel.valuation U).valuationSubring = B`.
Thus the canonical valuation of that relation has exactly the actual
published integer ring, as valuation subrings of the same field `U`.
The proof installs compatibility of `(fixedFieldValued F).v` with its induced
relation using `Valuation.Compatible.ofValuation`, compares it with the
canonical valuation using `ValuativeRel.isEquiv`, and applies
`Valuation.isEquiv_iff_valuationSubring`. It uses no unramifiedness,
discreteness, Henselianity, or residue algebraic-closure assertion.
This is a derived implementation comparison, not an additional arithmetic
theorem taken from the literature.

`FixedFieldIntegersIsDVR F` asserts `IsDiscreteValuationRing B`.
`FixedFieldIntegersIsHenselian F` asserts `HenselianLocalRing B`.
Both use the actual ring structure inherited by the published valuation
subring `B`; neither is stated for an arbitrary isomorphic ring.
Mathlib's Henselian class asks that every monic polynomial over `B` with an
approximate root modulo its maximal ideal and unit derivative have a root
in `B` with the same residue.

`SeparableUnramifiedArithmeticStatement.{u} : Prop` is a closed proposition
universally quantifying `F` and the four supplied base structures, and
conjoining the five propositions above. All five arithmetic assertions are
conclusions. None is an assumption, a field of input data, or proved here.
The target asserts no completeness or local compactness of `U` and no torus
norm or Iwahori construction.

## Original sources and derived correspondence

Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg,
GTM 67, Springer, 1979. Registered source `serre-1979-local-fields`,
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

- Chapter III §5, Theorems 2–3 and Corollary 1, printed pp. 54–55/PDF
  pp. 61–62: finite unramified extensions correspond to finite separable
  residue extensions, and their direct limit is the maximal unramified
  extension with residue the separable closure of the base residue field.
  Here the base residue field is finite and perfect, so its separable
  closure is an algebraic closure. This supplies algebraicity as well as
  algebraic closedness in the residue target. The published map comparisons
  specify exactly how this conclusion is expressed over `𝓀[F]`.
- Chapter II §2, Proposition 3 and Corollaries 1–3, printed pp. 28–29/PDF
  pp. 36–37: finite extensions have complete discrete valuation rings, with
  the degree formula and uniqueness of the prolongation. For a finite
  unramified extension the ramification index is one, so every extended
  value is a base value. Finite exhaustion then gives the value-attainment
  target for every element of `U`, with zero handled by the zero element.
- Chapter II §2, Exercise 4(a), printed p. 30/PDF p. 38: maximal algebraic
  subextensions all of whose finite subextensions have ramification index
  one have discrete valuation and algebraic-closure residue. The exercise
  uses a full algebraic closure. The present formulation is an adaptation
  to the actual separable closure, using the finite unramified correspondence
  and perfectness of the finite residue field. It does not identify the
  separable closure with the full algebraic closure when `F` is imperfect.
  The unchanged value group gives intrinsic discreteness and the DVR
  property for the actual valuation ring.
- Chapter I §7, Propositions 20–22, printed pp. 21–22/PDF pp. 29–30, and
  Chapter IV §1, Proposition 1 and the corollary after Proposition 2,
  printed pp. 62–63/PDF pp. 69–70: finite inertia fixed fields identify the
  arithmetic maximal unramified extension. Together with the direct-limit
  result, they relate these targets to the actual inertia-kernel fixed
  field used here.
- Chapter II §4, Proposition 7, printed p. 34/PDF p. 42: simple-root
  lifting in a complete local ring. The Henselian target for `B` is derived
  from this finite-stage result as explained next.

For the infinite-union Henselian argument, choose a monic polynomial over `B`
and an integral representative of its proposed residue root. Its finitely
many coefficients and that representative lie in one finite unramified
Galois stage `E` of `U/F`. The restriction of the actual valuation to `E`
identifies its integer ring with the intersection with `B`; it also gives
the corresponding maximal-ideal and unit tests. Thus the polynomial's
approximate-root condition and the derivative-unit condition hold in this
finite stage. Its integer ring is complete by Serre II §2, so II §4,
Proposition 7 lifts the simple root there. Including the root back into `B`
gives the required Henselian lift. This is a derived route for a future proof,
not a proof implemented by this statement unit. It does not assume that the
infinite field `U` is complete.

Read with Serre, *Corrections to J-P. Serre's books* (2019), registered
source `serre-book-corrections-2019`, retained file
`/home/taskhub/pilot/literature/Jean-Pierre Serre — Corrections to J-P. Serre's books (2019).pdf`,
SHA-256 `b76739179d067850770081597a8e9ced68135ebf80678876605f471297a4fee5`,
PDF pp. 2–3. No correction affects these conclusions. The printed p. 63
entries concern Proposition 3, outside the inertia corollary cited above.

Tasho Kaletha and Gopal Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
registered source `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`,
§2.5(c), printed p. 88/PDF p. 119, uses the maximal unramified extension
inside a fixed separable closure. Their setup allows more general discretely
valued Henselian base fields; this unit states its arithmetic prerequisite
only for nonarchimedean local fields. Lemma 2.5.12 and Definition 2.5.13,
printed pp. 89–90/PDF pp. 120–121, motivate the later torus consumer and are
not asserted here.

Read with the authors' corrections of 1 November 2024, registered source
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF pp. 24–25. They do not change the maximal-unramified setup; the later
Remark 2.5.15 is replaced. Book and corrections are retained in
`/home/taskhub/central-library/Kaletha-Prasad--Bruhat-Tits theory, a new approach (book)--2023/`.
The cited originals and corrections were read for this translation.

## Dependencies and status

The only direct project import is
`Langlands.Galois.Local.SeparableInertiaDefinitions`, reused unchanged.
The additional Mathlib imports supply `IsAlgClosure`,
`IsDiscreteValuationRing` and `HenselianLocalRing`.
The environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0
with Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
All five arithmetic targets remain proof obligations for subsequent tasks.
