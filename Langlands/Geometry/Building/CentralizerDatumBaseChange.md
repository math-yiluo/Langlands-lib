# Base change of the actual centralizer datum

This is an internal coherence unit toward Kaletha–Prasad Axiom 4.1.17
(compatibility with isomorphisms) for the valuation-quotient buildings of
supplied `ValuationBuildingData`. It does not prove that axiom. It produces,
from a `CentralizerDatum` over a field `k`, a `CentralizerDatum` for the base
changed torus over an extension `K`, which the published V6 field-restriction
result `IntegerValuation.fieldRestrictApartment_isOmegaCompatible` needs in the
form "actual base change of the downstairs centralizer inclusion and torus
factorization".

## Provenance

The source motivation is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), Axiom 4.1.17, printed p.162 (PDF p.193), and Definition 6.1.2 (V 6),
read with the authors' corrections of 1 November 2024 (PDF p.27). Registered
source IDs: `kaletha-prasad-2023-bruhat-tits-new-approach`,
`kaletha-prasad-2024-corrections`. The declarations are derived from the
published `CentralizerDatum` (`KPCentralizerCompatibility`),
`torusCentralizer_baseChange`, `SubgroupFunctor.IsRepresentedBy.baseChange`,
`IsClosedSubgroup.baseChange`,
`SubgroupFunctor.IsRepresentedBy.torusCentralizer_of_iso_square`,
`isoOfIsRepresentedBy`, `characterRestrict_comp`, `characterRestrict_id` and
`eval_cocharacterRealCongr`; the character computation follows the published
`CentralizerDatum.basedComparisonIso_characterRestriction`. They are not
statements from the source.

## Transfer of restriction-evaluation bijectivity

`CentralizerDatum.bijective_restrictionEvaluation_of_basedIso`: over one field
`K`, let `E` be a centralizer datum of `j : S' → H`, let `e : S ≅ S'` and
`f : G ≅ H` satisfy `i ≫ f.hom = groupHom e.hom ≫ j`, and let `l : Z → G`
represent the full centralizer `torusCentralizer i` with `s ≫ l = i`. Then
`Cartan.restrictionEvaluation s : V(S) → Hom(X^*(Z), ℝ)` is bijective.

Proof. The representative `l ≫ f.hom` of `torusCentralizer j`
(`torusCentralizer_of_iso_square`) and `E.j` give an isomorphism
`ψ : Z ≅ E.Z` with `ψ ≫ E.j = l ≫ f` (`isoOfIsRepresentedBy`). Cancelling
the monomorphism `E.j` gives `s ≫ ψ = e ≫ E.s`, hence for every character
`χ` of `E.Z`, the transport along `e` of the restriction of `ψ^*χ` along `s`
is the restriction of `χ` along `E.s`. With `eval_cocharacterRealCongr` this
gives, for every `v ∈ V(S)`,
`(restrictionEvaluation s v) ∘ ψ^* = restrictionEvaluation E.s (e_* v)`.
Precomposition with `ψ^*` is injective because `ψ^*` is surjective (with
inverse `(ψ⁻¹)^*`, by `characterRestrict_comp` and `characterRestrict_id`), and
`e_* = cocharacterRealCongr e` is a linear equivalence, so bijectivity of
`E.bijective` transfers.

## The base-changed datum

For a field extension `k → K` (base map `algebraBaseMap k K`) and a centralizer
datum `C` of `i : S → G` over `k`:

- `isRepresentedBy_baseChange`: the base change of `C.j` represents the full
  centralizer of the base-changed torus `i_K`; this is
  `torusCentralizer_baseChange` with `IsRepresentedBy.baseChange`.
- `comp_eq_baseChange`: `s_K ≫ j_K = i_K`, by functoriality of base change.
- `baseChangeOfBasedIso C E e f h`: given a based isomorphism
  `e : S_K ≅ S'`, `f : G_K ≅ H`, `h : i_K ≫ f.hom = groupHom e.hom ≫ j` to a
  torus with centralizer datum `E`, the centralizer datum of `i_K` whose group,
  inclusion and torus factorization are the actual base changes of `C.Z`,
  `C.j`, `C.s` (closedness by `IsClosedSubgroup.baseChange`; bijectivity by the
  transfer theorem above). `baseChangeOfBasedIso_j` and
  `baseChangeOfBasedIso_s` record that the inclusion and factorization are
  literally the base changes (`rfl`).

No building axiom, V 7, AS 5 or availability hypothesis is used.
