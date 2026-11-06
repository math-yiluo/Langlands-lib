# Apartment construction for an empty actual relative-root set

This is an internal construction in
`Langlands.Geometry.Building.RootFreeApartmentConstruction`. It works at every
universe `u` with the existing actual group schemes and relative roots. It adds
no root coordinates and changes no definition of the KP quotient.

For an inclusion `i : S.toGrp ⟶ G`, assume that the actual set
`relativeRoots i` is empty. `RootFunctionFamily.constantTop` assigns infinity
to every character and rational point. It is fixed by both the existing
translation action of `V S` and the normalizer action. It satisfies
`IsRootDatumValuation i` because off-root normalization holds by definition
and every root-indexed condition has an empty domain. Conversely, the
off-root normalization forces every root-datum valuation to equal this family.
Split-torus V 6 is also automatic.

`KPApartmentData.ofRelativeRootsEqEmpty i ω hΦ` constructs the singleton
containing this family. Its translation orbit is exactly that singleton,
and its normalizer stability follows from the fixedness just proved.
This construction works for any function `ω : kˣ → ℝ`; no valuation laws or
local-field hypotheses are needed for it. The carrier of every other valid
apartment class for this same empty root set is the same singleton.

For a nonarchimedean local field, full centralizer V 6 is automatic for every
supplied `CentralizerDatum i` and every valid apartment class: its defining
conditions are indexed by actual relative roots. Combining this with the
published
`KPApartmentData.satisfiesApartmentAxioms_iff_of_relativeRoots_eq_empty`
proves the existing single-apartment predicate. That predicate includes V 7,
AS 2–AS 4 and AS 5, using the derivative-spanning rank-zero convention
documented in [RankZeroAffineRootSystem](RankZeroAffineRootSystem.md).
This is the existing predicate, with its existing scope; it is not the
whole-building validity predicate.

`ValuationBuildingData.ofRelativeRootsEqEmpty` constructs local-field building
data from connected reductivity, a prescribed actual maximal split torus with
empty relative-root set, and a supplied actual centralizer datum. Its torus,
inclusion and centralizer fields are exactly the supplied ones, and its
apartment is the singleton constructed above. Its reduced building and action
are the existing KP quotient and action associated to those data.
`ofRelativeRootsEqEmpty_satisfiesApartmentAxioms` proves the single-apartment
predicate for that exact output.
`ofIsAnisotropic` supplies emptiness from the published
`IsAnisotropic.relativeRoots_eq_empty` for the prescribed split subtorus.

The analogous `IntegerValuationBuildingData.ofRelativeRootsEqEmpty` works
over any field with a supplied integer-valued valuation, including the trivial
valuation. It proves full integer centralizer V 6 by the same root elimination
and retains the prescribed torus and centralizer. It assumes neither
surjectivity nor henselianity and makes no topology assertion.

The construction does not prove existence of `CentralizerDatum`, general
root-valuation existence, derived covers, parahoric zero data, stabilizer
boundedness, descent, or the five building-axiom witnesses. In particular, an
empty relative-root set alone is not used to assert that the actual reduced
quotient is a singleton.

The provenance is internal and derived: the proof directly specializes the
published definitions and rank-zero equivalence. Its source context is
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Definition 6.1.2,
Lemma 6.1.6, Definition 6.1.7 and §6.1.8 (printed pp.199–201/PDF pp.230–232),
which define the valuations, translations, equipollence and normalizer action.
Definition 1.3.1 and Remark 1.3.2(4) (printed pp.14–15/PDF pp.45–46) explain
the rank-zero convention, with the affine-spanning distinction handled by the
imported derivative-spanning variant. KP does not state these Lean constructors
verbatim. The registered book source is
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
